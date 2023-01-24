
use std::{marker::PhantomData};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell,Chip, Layouter, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
};


use halo2_proofs::{dev::MockProver, pairing::bn256::Fr as Fp};
use halo2_proofs::circuit::Region;
use halo2_proofs::plonk::Fixed;

#[derive(Clone)]
struct Number<F: FieldExt>(AssignedCell<F, F>);

#[derive(Clone, Debug)]
struct FieldConfig {
    advice: [Column<Advice>;2],
    instance: Column<Instance>,
    s_mul: Selector,
}

struct FieldChip<F: FieldExt>{
    config: FieldConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Chip<F> for FieldChip<F> {
    type Config = FieldConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl <F: FieldExt> FieldChip<F> {
    fn construct (config: <Self as Chip<F>>::Config)->Self {
        Self{
            config,
            _marker: PhantomData,
        }
    }
    fn configured(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>;2],
        instance: Column<Instance>,
        constant: Column<Fixed>) -> <Self as Chip<F>>::Config {
        meta.enable_equality(instance);
        meta.enable_constant(constant);
        for col in &advice {
            meta.enable_equality(*col);
        }
        let s_mul = meta.selector();

        meta.create_gate("mul", |meta| {
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[0], Rotation::next());
            let s_mul = meta.query_selector(s_mul);
            vec![s_mul * (lhs * rhs - out)]
        });

        FieldConfig{
            advice,instance,s_mul
        }
    }
}
trait NumericInstruction<F: FieldExt>: Chip<F> {
    type Num;

    fn load_private(&self, layouter: impl Layouter<F>, a: F) -> Result<Self::Num, Error>;

    fn load_constant(&self, layouter: impl Layouter<F>, constant: F) -> Result<Self::Num, Error>;

    fn mul(
        &self,
        layouter: impl Layouter<F>,
        a: Self::Num,
        b: Self::Num,
    ) -> Result<Self::Num, Error>;


    // why need this???
    fn expose_public(
        &self,
        layouter: impl Layouter<F>,
        num: Self::Num,
        row: usize,
    ) -> Result<(), Error>;
}

impl <F: FieldExt> NumericInstruction<F> for FieldChip<F> {
    type Num = Number<F>;

    fn load_private(&self, mut layouter: impl Layouter<F>, a: F) -> Result<Self::Num, Error> {
        let config = self.config();
        layouter.assign_region(||"load private", |mut region|{
            region.assign_advice(||"",config.advice[0], 0, ||Ok(a)).map(Number)
        })
    }

    fn load_constant(&self, mut layouter: impl Layouter<F>, constant: F) -> Result<Self::Num, Error> {
        let config = self.config();
        layouter.assign_region(||"load constant", |mut region|{
            region.assign_advice_from_constant(||"constant input",config.advice[0], 0, constant).map(Number)
        })

    }

    fn expose_public(&self, mut layouter: impl Layouter<F>, num: Self::Num, row: usize) -> Result<(), Error> {
       let config = self.config();
        layouter.constrain_instance(num.0.cell(), config.instance, row)
    }


    fn mul(&self, mut layouter: impl Layouter<F>, a: Self::Num, b: Self::Num) -> Result<Self::Num, Error> {
        let config = self.config();
        layouter.assign_region(||"mul", |mut region: Region<'_, F>|{
            config.s_mul.enable(&mut region, 0)?;

            a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
            b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

            let value = a.0.value().copied().unwrap() * b.0.value().copied().unwrap();
          //  println!("{:?}", value);

            region.assign_advice(|| "lhs * rhs", config.advice[0], 1, || Ok(value)).map(Number)

        })
    }
}
#[derive(Default)]
struct MyCircuit<F: FieldExt> {
    constant: F,
    a: F,
    b: F
}


impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = FieldConfig;

    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column()];

        let instance = meta.instance_column();

        let constant = meta.fixed_column();

        FieldChip::configured(meta, advice, instance, constant)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let field_chip = FieldChip::construct(config);

        let a = field_chip.load_private(layouter.namespace(|| "load a"), self.a)?;

        let b = field_chip.load_private(layouter.namespace(|| "load b"), self.b)?;

        let constant = field_chip.load_constant(layouter.namespace(|| "load constant"), self.constant)?;

        let ab = field_chip.mul(layouter.namespace(||"a * b"), a, b)?;
        let absq = field_chip.mul(layouter.namespace(|| "ab * ab"), ab.clone(), ab)?;

        let c = field_chip.mul(layouter.namespace(||"constant * absq"), constant, absq)?;

        field_chip.expose_public(layouter.namespace(|| "field expose"), c, 0)

    }
}

fn main() {
     let k = 5;

    let constant = Fp::from(7);
    let a = Fp::from(2);
    let b = Fp::from(3);
    let c = constant * a.square() * b.square();

    let circuit = MyCircuit {
        constant,
        a,
        b,
    };

    let public_input = vec![c];

    let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

}