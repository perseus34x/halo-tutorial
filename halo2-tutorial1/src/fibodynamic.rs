

use std::{marker::PhantomData};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, TableColumn,ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
};

#[derive(Clone)]
struct Number<F: FieldExt>(AssignedCell<F, F>);

use halo2_proofs::{dev::MockProver, pairing::bn256::Fr as Fp};

#[derive(Debug, Clone)]
struct FibonacciConfig {
    pub advice: [Column<Advice>; 3],
    pub s_add: Selector,
    pub s_xor: Selector,
    pub xor_table: [TableColumn; 3],
    pub instance: Column<Instance>,
}
#[derive(Debug, Clone)]
struct FibonacciChip<F: FieldExt> {
    config: FibonacciConfig,
    _marker: PhantomData<F>,
}
/*
    |   a   |   b   |   c   |   s_add   |   s_xor   |     table_column_a   |   table_column_b |   table_column_xor   |


*/
impl<F: FieldExt> FibonacciChip<F> {
    pub fn construct(config: FibonacciConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
    pub fn configure(meta: &mut ConstraintSystem<F>) -> FibonacciConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let s_add = meta.selector();
        let s_xor = meta.complex_selector();
        let instance = meta.instance_column();

        let xor_table = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s
            //
            let s = meta.query_selector(s_add);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            vec![s * (a + b - c)]
        });

        meta.lookup("lookup",|meta| {
            let s = meta.query_selector(s_xor);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table[0]),
                (s.clone() * rhs, xor_table[1]),
                (s * out, xor_table[2]),
            ]
        });


        FibonacciConfig {
            advice: [col_a, col_b, col_c],
            s_add,
            s_xor,
            xor_table,
            instance,
        }
    }
    fn load_table(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..32 {
                    for rhs in 0..32 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table[0],
                            idx,
                            || Ok(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table[1],
                            idx,
                            || Ok(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table[2],
                            idx,
                            || Ok(F::from(lhs ^ rhs)),
                        )?;
                        idx += 1;
                    }
                }
                Ok(())
            }
        )
    }
    #[allow(clippy::type_complexity)]
    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        nrows: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "entire circuit",
            |mut region| {
                self.config.s_add.enable(&mut region, 0)?;

                // assign first row
                let a_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    0,
                    self.config.advice[0],
                    0,
                )?;
                let mut b_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    1,
                    self.config.advice[1],
                    0,
                )?;
                let mut c_cell = region.assign_advice(
                    || "add",
                    self.config.advice[2],
                    0,//Ok(a_cell.value().copied().unwrap() + b_cell.value().copied().unwrap())
                    || a_cell.value().and_then(|b| b_cell.value().map(|c| *b + *c)).ok_or(Error::Synthesis),
                )?;

                // assign the rest of rows
                for row in 1..nrows {
                    b_cell.copy_advice(
                        || "a",
                        &mut region,
                        self.config.advice[0],
                        row,
                    )?;
                    c_cell.copy_advice(
                        || "b",
                        &mut region,
                        self.config.advice[1],
                        row,
                    )?;

                    let new_c_cell = if row % 2 == 0 {
                        self.config.s_add.enable(&mut region, row)?;
                        region.assign_advice(
                            || "advice",
                            self.config.advice[2],
                            row,//Ok(b_cell.value().copied().unwrap() + c_cell.value().copied().unwrap()),
                            || b_cell.value().and_then(|b| c_cell.value().map(|c| *b + *c)).ok_or(Error::Synthesis),
                        )?
                    } else {
                        self.config.s_xor.enable(&mut region, row)?;

                        let c = b_cell.value().and_then(|a| c_cell.value().map(|b| {
                            let a_val = a.get_lower_128() as u64 ;
                            let b_val = b.get_lower_128() as u64 ;
                            F::from( a_val ^ b_val)
                        }));
                        region.assign_advice(
                            || "advice",
                            self.config.advice[2],
                            row,
                            ||c.ok_or(Error::Synthesis),
                        )?
                    };

                    b_cell = c_cell;
                    c_cell = new_c_cell;
                }

                Ok(c_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: AssignedCell<F, F>,
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
        chip.load_table(layouter.namespace(|| "load lookup table"))?;
        let out_cell = chip.assign(layouter.namespace(|| "entire table"), 8)?;
        chip.expose_public(layouter.namespace(|| "out"), out_cell, 2)?;

        Ok(())
    }
}
fn main() {

    let k = 11;

    let a = Fp::from(1); // F[0]
    let b = Fp::from(1); // F[1]
    let out = Fp::from(21); // F[9]

    let circuit = MyCircuit(PhantomData);

    let public_input = vec![a, b, out];

    let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));



}