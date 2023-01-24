use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Constraints, Error, Expression, Selector},
    poly::Rotation,
};

mod table;
use table::*;

/// This helper checks that the values witnessed in  given cells is computed correctly.

#[derive(Debug, Clone)]

struct HashConstrained<F: FieldExt, const RANGE: usize>(AssignedCell<Assigned<F>, F>);

#[derive(Debug, Clone)]
struct HashCheckConfig<F: FieldExt, const RANGE: usize, const LOOKUP_RANGE: usize> {
    q_hash_check: Selector,
    q_lookup: Selector,
    value: Column<Advice>,
    table: HashTableConfig<F, LOOKUP_RANGE>,
}


impl<F: FieldExt, const RANGE: usize, const LOOKUP_RANGE: usize> HashCheckConfig<F, RANGE, LOOKUP_RANGE>
{
    pub fn configure(meta: &mut ConstraintSystem<F>, lhs: Column<Advice>,rhs: Column<Advice>,value: Column<Advice>) -> Self {
        let q_hash_check = meta.selector();
        let q_lookup = meta.complex_selector();
        let table = HashTableConfig::configure(meta);


        meta.lookup(|meta| {
            let s = meta.query_selector(q_lookup);
            let lhs = meta.query_advice(lhs, Rotation::cur());
            let rhs = meta.query_advice(rhs, Rotation::cur());
            let value = meta.query_advice(value, Rotation::cur());

            vec![(s.clone() * lhs, table.input_a),
                 (s.clone() * rhs, table.input_b),
                 (s * value, table.hash_value)]
        });

        Self {
            q_hash_check,
            q_lookup,
            value,
            table,
        }
    }

    pub fn assign_simple(
        &self,
        mut layouter: impl Layouter<F>,
        a: Value<Assigned<F>>,
        b: Value<Assigned<F>>,
        value: Value<Assigned<F>>,
    ) -> Result<HashConstrained<F, RANGE>, Error> {
        layouter.assign_region(
            || "Assign value for simple hash check",
            |mut region| {
                let offset = 0;

                // Enable q_hash_check
                self.q_hash_check.enable(&mut region, offset)?;

                // Assign value
                region
                    .assign_advice(|| "value", self.value, offset, || value)
                    .map(HashConstrained).expect("TODO: panic message");
                region
                    .assign_advice(|| "value", self.value, offset, || value)
                    .map(HashConstrained);
                region
                    .assign_advice(|| "value", self.value, offset, || value)
                    .map(HashConstrained)
            },
        )
    }

    pub fn assign_lookup(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<Assigned<F>>,
    ) -> Result<HashConstrained<F, LOOKUP_RANGE>, Error> {
        layouter.assign_region(
            || "Assign value for lookup hash check",
            |mut region| {
                let offset = 0;

                // Enable q_lookup
                self.q_lookup.enable(&mut region, offset)?;

                // Assign value
                region
                    .assign_advice(|| "value", self.value, offset, || value)
                    .map(HashConstrained)
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use halo2_proofs::{
        circuit::floor_planner::V1,
        dev::{FailureLocation, MockProver, VerifyFailure},
        pasta::Fp,
        plonk::{Any, Circuit},
    };

    use super::*;

    #[derive(Default)]
    struct MyCircuit<F: FieldExt, const RANGE: usize, const LOOKUP_RANGE: usize> {
        a: Value<Assigned<F>>,
        b: Value<Assigned<F>>,
        value: Value<Assigned<F>>,
        lookup_value: Value<Assigned<F>>,
    }

    impl<F: FieldExt, const RANGE: usize, const LOOKUP_RANGE: usize> Circuit<F>
    for MyCircuit<F, RANGE, LOOKUP_RANGE>
    {
        type Config = HashCheckConfig<F, RANGE, LOOKUP_RANGE>;
        type FloorPlanner = V1;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let value = meta.advice_column();
            HashCheckConfig::configure(meta, value)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            config.table.load(&mut layouter)?;

            config.assign_simple(layouter.namespace(|| "Assign simple value"), self.a,self.b,self.value)?;
            config.assign_lookup(
                layouter.namespace(|| "Assign lookup value"),
                self.lookup_value,
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_range_check_2() {
        let k = 9;
        const RANGE: usize = 8; // 3-bit value
        const LOOKUP_RANGE: usize = 256; // 8-bit value

        // Successful cases
        for i in 0..RANGE {
            for j in 0..LOOKUP_RANGE {
                let circuit = MyCircuit::<Fp, RANGE, LOOKUP_RANGE> {
                    a: Value::known(Fp::from(i as u64).into()),
                    b: Value::known(Fp::from(i as u64).into()),
                    value: Value::known(Fp::from(i as u64).into()),
                    lookup_value: Value::known(Fp::from(j as u64).into()),
                };

                let prover = MockProver::run(k, &circuit, vec![]).unwrap();
                prover.assert_satisfied();
            }
        }

    }

}
