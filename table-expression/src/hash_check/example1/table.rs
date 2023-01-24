use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error, TableColumn},
};

/// A lookup table of values from 0..RANGE.
#[derive(Debug, Clone)]
pub(super) struct HashTableConfig<F: FieldExt, const RANGE: usize> {
    pub(super) input_a: TableColumn,
    pub(super) input_b: TableColumn,
    pub(super) hash_value: TableColumn,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const RANGE: usize> HashTableConfig<F, RANGE> {
    pub(super) fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let input_a = meta.lookup_table_column();
        let input_b = meta.lookup_table_column();
        let hash_value = meta.lookup_table_column();
        Self {
            input_a,
            input_b,
            hash_value,
            _marker: PhantomData,
        }
    }

    pub(super) fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "load hash-check table",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..RANGE {
                    for rhs in 0..RANGE {
                        //take hash(a,b)
                        table.assign_cell(
                            || "input_a",
                            self.input_a,
                            idx,
                            || Value::known(F::from(lhs as u64)),
                        )?;
                        table.assign_cell(
                            || "input_b",
                            self.input_b,
                            idx,
                            || Value::known(F::from(rhs as u64)),
                        )?;
                        table.assign_cell(
                            || "hash",
                            self.value,
                            idx,
                            || Value::known(F::from((lhs ^ rhs) as u64)),
                        )?;
                        idx += 1;
                    }

                }

                Ok(())
            },
        )
    }
}
