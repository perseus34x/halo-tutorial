use halo2_proofs::{dev::MockProver, pairing::bn256::Fr as Fp};
use std::marker::PhantomData;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};


#[derive(Debug, Clone)]
struct FibonacciConfig {
    pub col_one: Column<Fixed>,
    pub col_a: Column<Advice>, // cond
    pub col_b: Column<Advice>, // thenval
    pub col_c: Column<Advice>, // elseval
    pub col_out: Column<Advice>, // output
    pub selector: Selector,
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct FibonacciChip<F: FieldExt> {
    config: FibonacciConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FibonacciChip<F> {
    pub fn construct(config: FibonacciConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> FibonacciConfig {
        let col_one = meta.fixed_column();
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let col_out = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        meta.enable_constant(col_one);
        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(col_out);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s
            //
            let s = meta.query_selector(selector);
            let one = meta.query_fixed(col_one, Rotation::cur());
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            let out = meta.query_advice(col_out, Rotation::cur());
            vec![
                s * ( a.clone() * b + (one-a.clone()) * c - out )

                // a = 2
                // 2b - c = 0
                // b = 3, c = 6
                // out = 0
            ]
        });

        FibonacciConfig {
            col_one,
            col_a,
            col_b,
            col_c,
            col_out,
            selector,
            instance,
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let one_cell = region.assign_fixed(
                    || "one",
                    self.config.col_one,
                    0,
                    || Ok(F::one()))?;

                let a_cell = region.assign_advice_from_instance(
                    || "cond",
                    self.config.instance,
                    0,
                    self.config.col_a,
                    0)?;

                let b_cell = region.assign_advice_from_instance(
                    || "thenval",
                    self.config.instance,
                    1,
                    self.config.col_b,
                    0)?;

                let c_cell = region.assign_advice_from_instance(
                    || "elseval",
                    self.config.instance,
                    2,
                    self.config.col_c,
                    0)?;

                let out_cell = region.assign_advice(
                    || "out",
                    self.config.col_out,
                    0,
                    // || a_cell.value().copied() + b_cell.value(),
                    || Ok(a_cell.value().copied().unwrap() * b_cell.value().copied().unwrap() + (one_cell.value().copied().unwrap() - a_cell.value().copied().unwrap()) * c_cell.value().copied().unwrap()),
                )?;

                Ok(out_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit<F>(PhantomData<F>);

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = FibonacciConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FibonacciChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = FibonacciChip::construct(config);

        let out = chip.assign_first_row(layouter.namespace(|| "first row"))?;

        println!("# in synthesize: out={:?}", out);

        chip.expose_public(layouter.namespace(|| "out"), &out, 3)?;

        Ok(())
    }
}

fn main() {
 
    // ANCHOR: test-circuit
    // The number of rows in our circuit cannot exceed 2^k. Since our example
    // circuit is very small, we can pick a very small value here.
    let k = 4;

    // good one
     let cond = Fp::from(1); // instance[0], a
     let thenval = Fp::from(2); // instance[1], b
     let elseval = Fp::from(3); // instance[2], c
     let outval = if cond == Fp::from(1) {thenval} else {elseval};
    // let outval = Fp::from(2); // instance[3]
    // println!("# in main: outval={:?}", outval);

    // bad one
   // let cond = Fp::from(2); // instance[0], a
   // let thenval = Fp::from(3); // instance[1], b
   // let elseval = Fp::from(6); // instance[2], c
    // let outval = if cond == Fp::from(1) {thenval} else {elseval};
   // let outval = Fp::from(0); // instance[3]
    println!("# in main: outval={:?}", outval);

    let circuit = MyCircuit(PhantomData);

    // let public_input = vec![cond, thenval, elseval];
    let public_input = vec![cond, thenval, elseval, outval];

    println!("# start.");
    let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
    assert_eq!(prover.verify(),Ok(()));
    println!("# done.");

    // ANCHOR_END: test-circuit
}