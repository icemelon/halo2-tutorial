use std::{marker::PhantomData};

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
};

#[derive(Clone)]
struct Number<F: FieldExt>(AssignedCell<F, F>);

// Config that contains the columns used in the circuit
#[derive(Debug, Clone)]
struct FiboConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    c: Column<Advice>,
    i: Column<Instance>,
    s: Selector,
}

// The chip that configures the gate and fills in the witness
struct FiboChip<F: FieldExt> {
    config: FiboConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FiboChip<F> {
    fn construct(config: FiboConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
    ) -> FiboConfig {
        // create columns
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let i = meta.instance_column();
        let s = meta.selector();

        // enable permutation checks for the following columns
        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);
        meta.enable_equality(i);

        // define the custom gate
        meta.create_gate("add", |meta| {
            let s = meta.query_selector(s);
            let lhs = meta.query_advice(a, Rotation::cur());
            let rhs = meta.query_advice(b, Rotation::cur());
            let out = meta.query_advice(c, Rotation::cur());
            vec![s * (lhs + rhs - out)]
        });

        FiboConfig {
            a, b, c, i, s,
        }
    }

    fn load_first_row(
        &self,
        mut layouter: impl Layouter<F>,
        a: F,
        b: F,
    ) -> Result<(Number<F>, Number<F>, Number<F>), Error> {
        // load first row
        layouter.assign_region(
            || "first row",
            |mut region| {
                // enable the selector
                self.config.s.enable(&mut region, 0)?;

                let a_num = region.assign_advice(
                    || "a",
                    self.config.a, // column a
                    0, // rotation
                    || Ok(a),
                ).map(Number)?;

                let b_num = region.assign_advice(
                    || "b",
                    self.config.b, // column b
                    0, // rotation
                    || Ok(b),
                ).map(Number)?;

                let c_num = region.assign_advice(
                    || "c",
                    self.config.c, // column c
                    0, // rotation
                    || Ok(a + b),
                ).map(Number)?;

                Ok((a_num, b_num, c_num))
            },
        )
    }

    fn load_row(
        &self,
        mut layouter: impl Layouter<F>,
        a: &Number<F>,
        b: &Number<F>,
    ) -> Result<Number<F>, Error> {
        layouter.assign_region(
            || "row",
            |mut region| {
                // enable the selector
                self.config.s.enable(&mut region, 0)?;

                // copy the cell from previous row
                a.0.copy_advice(|| "a", &mut region, self.config.a, 0)?;
                b.0.copy_advice(|| "b", &mut region, self.config.b, 0)?;
                let c = a.0.value().and_then(|a| b.0.value().map(|b| *a + *b));

                region.assign_advice(
                    || "c",
                    self.config.c,
                    0,
                    || c.ok_or(Error::Synthesis),
                ).map(Number)
            },
        )
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        num: Number<F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(num.0.cell(), self.config.i, row)
    }
}

#[derive(Default)]
struct FiboCircuit<F> {
    a: F,
    b: F,
    num: usize,
}

impl<F: FieldExt> Circuit<F> for FiboCircuit<F> {
    type Config = FiboConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FiboChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>
    ) -> Result<(), Error> {
        let chip = FiboChip::construct(config);
        let (_, mut b, mut c) = chip.load_first_row(
            layouter.namespace(|| "first row"),
            self.a,
            self.b,
        )?;
        for _ in 3..self.num {
            let new_c = chip.load_row(
                layouter.namespace(|| "row"),
                &b,
                &c,
            )?;
            b = c;
            c = new_c;
        }
        chip.expose_public(layouter.namespace(|| "expose c"), c, 0)?;
        Ok(())
    }
}

fn get_fibo_seq(a: u64, b: u64, num: usize) -> Vec<u64> {
    let mut seq = vec![0; num];
    seq[0] = a;
    seq[1] = b;
    for i in 2..num {
        seq[i] = seq[i - 1] + seq[i - 2];
    }
    seq
}

fn main() {
    use halo2_proofs::{dev::MockProver, pairing::bn256::Fr as Fp};

    // Prepare the private and public inputs to the circuit!
    let num = 12;
    let seq = get_fibo_seq(1, 1, num);
    let res = Fp::from(seq[num - 1]);
    println!("{:?}", seq);

    // Instantiate the circuit with the private inputs.
    let circuit = FiboCircuit {
        a: Fp::from(seq[0]),
        b: Fp::from(seq[1]),
        num,
    };

    // Arrange the public input. We expose the multiplication result in row 0
    // of the instance column, so we position it there in our public inputs.
    let mut public_inputs = vec![res];

    // Set circuit size
    let k = 4;

    // Given the correct public input, our circuit will verify.
    let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    // If we try some other public input, the proof will fail!
    public_inputs[0] += Fp::one();
    let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
    assert!(prover.verify().is_err());
}
