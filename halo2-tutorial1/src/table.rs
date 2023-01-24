
use std::{marker::PhantomData};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell,Chip, Layouter, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, TableColumn,ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
};

#[derive(Clone)]
struct Number<F: FieldExt>(AssignedCell<F, F>);

use halo2_proofs::{dev::MockProver, pairing::bn256::Fr as Fp};
use halo2_proofs::circuit::floor_planner::V1;
use halo2_proofs::plonk::Assigned;

#[derive(Clone, Copy)]
pub(super) struct RangTableConfig<F: FieldExt> {
    pub(super) col_value: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> RangTableConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let table_column = meta.lookup_table_column();

        Self {
            col_value: table_column,
            _marker: PhantomData,
        }
    }

    pub fn load(
        &self,
        layouter: &mut impl Layouter<F>,
        values: Vec<usize>,
    ) -> Result<(), Error> {
        layouter.assign_table(
            || "range check",
            |mut table| {
                let mut offset = 0;

                println!("load values: {:?}", values);
                for el in values.clone() {
                    println!("assign cell, offset {:?}, element: {:?}", offset, el);
                    table.assign_cell(
                        || "assign table cell",
                        self.col_value,
                        offset,
                        || Ok(F::from(el as u64)),
                    )?;
                    offset += 1;
                }

                Ok(())
            },
        )
    }
}
#[derive(Clone, Copy)]
struct TestConfig<F: FieldExt> {
    a: Column<Advice>,
    q_selector: Selector,
    lookup_table: RangTableConfig<F>,
}

#[derive(Default)]
struct MyCircuit<F: FieldExt> {
    value: F
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = TestConfig<F>;

    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let a = meta.advice_column();

        let q_selector = meta.complex_selector();

        let lookup_table = RangTableConfig::configure(meta);

        meta.lookup("lookup",|meta| {
            let q_selector = meta.query_selector(q_selector);

            let value = meta.query_advice(a, Rotation::cur());

            vec![(q_selector*value, lookup_table.col_value)]
        });

        TestConfig {
            a,
            q_selector,
            lookup_table,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        config.lookup_table.load(&mut layouter, vec![0,3,4,5,7,8,15,16,18])?;

        layouter.assign_region(
            || "assign columns",
            |mut region| {
                config.q_selector.enable(&mut region, 0)?;

                region.assign_advice(
                    || "assign a",
                    config.a,
                    0,
                    || Ok(self.value),
                )
            },
        )?;
        Ok(())
    }
}

pub fn Test() {
    let test_value: u64 = 8;

    let circuit = MyCircuit::<Fp> { value: Fp::from(test_value as u64).into() };

    let prover = MockProver::run(4, &circuit, vec![]).unwrap();
    assert_eq!(prover.verify(), Ok(()));
}