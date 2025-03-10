use super::poseidon2_params::Poseidon2Params;
use std::{marker::PhantomData, sync::Arc};
use halo2_proofs::halo2curves::ff::PrimeField;
use itertools::Itertools;

#[derive(Clone, Debug)]
pub struct Poseidon2<F: PrimeField> {
    pub(crate) params: Arc<Poseidon2Params<F>>,
}

impl<F: PrimeField> Poseidon2<F> {
    pub fn new(params: &Arc<Poseidon2Params<F>>) -> Self {
        Poseidon2 {
            params: Arc::clone(params),
        }
    }

    pub fn get_t(&self) -> usize {
        self.params.t
    }

    pub fn permutation(&self, input: &[F]) -> Vec<F> {
        let t = self.params.t;
        assert_eq!(input.len(), t);

        let mut current_state = input.to_owned();

        // Linear layer at beginning
        self.matmul_external(&mut current_state);

        for r in 0..self.params.rounds_f_beginning {
            current_state = self.add_rc(&current_state, &self.params.round_constants[r]);
            current_state = self.sbox(&current_state);
            self.matmul_external(&mut current_state);
        }

        let p_end = self.params.rounds_f_beginning + self.params.rounds_p;
        for r in self.params.rounds_f_beginning..p_end {
            current_state[0].add_assign(&self.params.round_constants[r][0]);
            current_state[0] = self.sbox_p(&current_state[0]);
            self.matmul_internal(&mut current_state, &self.params.mat_internal_diag_m_1);
        }
        
        for r in p_end..self.params.rounds {
            current_state = self.add_rc(&current_state, &self.params.round_constants[r]);
            current_state = self.sbox(&current_state);
            self.matmul_external(&mut current_state);
        }
        current_state
    }

    fn sbox(&self, input: &[F]) -> Vec<F> {
        input.iter().map(|el| self.sbox_p(el)).collect()
    }

    fn sbox_p(&self, input: &F) -> F {
        let mut input2 = *input;
        input2.square();

        match self.params.d {
            3 => {
                let mut out = input2;
                out.mul_assign(input);
                out
            }
            5 => {
                let mut out = input2;
                out.square();
                out.mul_assign(input);
                out
            }
            7 => {
                let mut out = input2;
                out.square();
                out.mul_assign(&input2);
                out.mul_assign(input);
                out
            }
            _ => {
                panic!()
            }
        }
    }

    pub fn matmul_m4(&self, input: &mut[F]) {
        let t = self.params.t;
        let t4 = t / 4;
        for i in 0..t4 {
            let start_index = i * 4;
            let mut t_0 = input[start_index];
            t_0.add_assign(&input[start_index + 1]);
            let mut t_1 = input[start_index + 2];
            t_1.add_assign(&input[start_index + 3]);
            let mut t_2 = input[start_index + 1];
            t_2.double();
            t_2.add_assign(&t_1);
            let mut t_3 = input[start_index + 3];
            t_3.double();
            t_3.add_assign(&t_0);
            let mut t_4 = t_1;
            t_4.double();
            t_4.double();
            t_4.add_assign(&t_3);
            let mut t_5 = t_0;
            t_5.double();
            t_5.double();
            t_5.add_assign(&t_2);
            let mut t_6 = t_3;
            t_6.add_assign(&t_5);
            let mut t_7 = t_2;
            t_7.add_assign(&t_4);
            input[start_index] = t_6;
            input[start_index + 1] = t_5;
            input[start_index + 2] = t_7;
            input[start_index + 3] = t_4;
        }
    }

    pub fn matmul_external(&self, input: &mut[F]) {
        let t = self.params.t;
        match t {
            2 => {
                // Matrix circ(2, 1)
                let mut sum = input[0];
                sum.add_assign(&input[1]);
                input[0].add_assign(&sum);
                input[1].add_assign(&sum);
            }
            3 => {
                // Matrix circ(2, 1, 1)
                let mut sum = input[0];
                sum.add_assign(&input[1]);
                sum.add_assign(&input[2]);
                input[0].add_assign(&sum);
                input[1].add_assign(&sum);
                input[2].add_assign(&sum);
            }
            4 => {
                // Applying cheap 4x4 MDS matrix to each 4-element part of the state
                self.matmul_m4(input);
            }
            8 | 12 | 16 | 20 | 24 => {
                // Applying cheap 4x4 MDS matrix to each 4-element part of the state
                self.matmul_m4(input);

                // Applying second cheap matrix for t > 4
                let t4 = t / 4;
                let mut stored = [F::ZERO; 4];
                for l in 0..4 {
                    stored[l] = input[l];
                    for j in 1..t4 {
                        stored[l].add_assign(&input[4 * j + l]);
                    }
                }
                for i in 0..input.len() {
                    input[i].add_assign(&stored[i % 4]);
                }
            }
            _ => {
                panic!()
            }
        }
    }

    pub fn matmul_internal(&self, input: &mut[F], mat_internal_diag_m_1: &[F]) {
        let t = self.params.t;

        match t {
            2 => {
                // [2, 1]
                // [1, 3]
                let mut sum = input[0];
                sum.add_assign(&input[1]);
                input[0].add_assign(&sum);
                input[1].double();
                input[1].add_assign(&sum);
            }
            3 => {
                // [2, 1, 1]
                // [1, 2, 1]
                // [1, 1, 3]
                let mut sum = input[0];
                sum.add_assign(&input[1]);
                sum.add_assign(&input[2]);
                input[0].add_assign(&sum);
                input[1].add_assign(&sum);
                input[2].double();
                input[2].add_assign(&sum);
            }
            4 | 8 | 12 | 16 | 20 | 24 => {
                // Compute input sum
                let mut sum = input[0];
                input
                    .iter()
                    .skip(1)
                    .take(t-1)
                    .for_each(|el| sum.add_assign(el));
                // Add sum + diag entry * element to each element
                for i in 0..input.len() {
                    input[i].mul_assign(&mat_internal_diag_m_1[i]);
                    input[i].add_assign(&sum);
                }
            }
            _ => {
                panic!()
            }
        }
    }

    fn add_rc(&self, input: &[F], rc: &[F]) -> Vec<F> {
        input
            .iter()
            .zip(rc.iter())
            .map(|(a, b)| {
                let mut r = *a;
                r.add_assign(b);
                r
            })
            .collect()
    }
}

pub struct Sbox5T4Gate<F: PrimeField> {
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Sbox5T4Gate<F> {
    pub fn new() -> Self {
        Sbox5T4Gate {
            _marker: PhantomData,
        }
    }

    pub fn evaluate(&self, input: &[F], index: Option<usize>) -> F {
        if let Some(index) = index {
            input[index].square().square() * input[index]
        } else {
            panic!("index is not set");
        }
    }

    pub fn evaluate_full(&self, input: &[F]) -> Vec<F> {
        input.iter().map(|el| el.square().square() * el).collect()
    }
    
    fn degree(&self) -> usize {
        5
    }

    fn nb_inputs(&self) -> usize {
        4   
    }

    fn nb_outputs(&self) -> usize {
        1
    }

    fn name(&self) -> String {
        "sbox5".to_string()
    }
}

pub struct MatmulM4Gate<F: PrimeField> {
    _marker: PhantomData<F>,
}

impl<F: PrimeField> MatmulM4Gate<F> {
    pub fn new() -> Self {
        MatmulM4Gate {
            _marker: PhantomData,
        }
    }

    pub fn evaluate(&self, input: &[F], index: Option<usize>) -> F {
        let t = 4;
        let t4 = t / 4;
        let mut input_copy = input.to_vec();
        for i in 0..t4 {
            let start_index = i * 4;
            let mut t_0 = input[start_index];
            t_0.add_assign(&input[start_index + 1]);
            let mut t_1 = input[start_index + 2];
            t_1.add_assign(&input[start_index + 3]);
            let mut t_2 = input[start_index + 1];
            t_2.double();
            t_2.add_assign(&t_1);
            let mut t_3 = input[start_index + 3];
            t_3.double();
            t_3.add_assign(&t_0);
            let mut t_4 = t_1;
            t_4.double();
            t_4.double();
            t_4.add_assign(&t_3);
            let mut t_5 = t_0;
            t_5.double();
            t_5.double();
            t_5.add_assign(&t_2);
            let mut t_6 = t_3;
            t_6.add_assign(&t_5);
            let mut t_7 = t_2;
            t_7.add_assign(&t_4);
            input_copy[start_index] = t_6;
            input_copy[start_index + 1] = t_5;
            input_copy[start_index + 2] = t_7;
            input_copy[start_index + 3] = t_4;
        }

        if let Some(index) = index {
            input_copy[index]
        } else {
            panic!("index is not set");
        }
    }

    pub fn evaluate_full(&self, input: &[F]) -> Vec<F> {
        let t = 4;
        let t4 = t / 4;
        let mut input_copy = input.to_vec();
        for i in 0..t4 {
            let start_index = i * 4;
            let mut t_0 = input[start_index];
            t_0.add_assign(&input[start_index + 1]);
            let mut t_1 = input[start_index + 2];
            t_1.add_assign(&input[start_index + 3]);
            let mut t_2 = input[start_index + 1];
            t_2.double();
            t_2.add_assign(&t_1);
            let mut t_3 = input[start_index + 3];
            t_3.double();
            t_3.add_assign(&t_0);
            let mut t_4 = t_1;
            t_4.double();
            t_4.double();
            t_4.add_assign(&t_3);
            let mut t_5 = t_0;
            t_5.double();
            t_5.double();
            t_5.add_assign(&t_2);
            let mut t_6 = t_3;
            t_6.add_assign(&t_5);
            let mut t_7 = t_2;
            t_7.add_assign(&t_4);
            input_copy[start_index] = t_6;
            input_copy[start_index + 1] = t_5;
            input_copy[start_index + 2] = t_7;
            input_copy[start_index + 3] = t_4;
        }
        input_copy
    }

    fn degree(&self) -> usize {
        1
    }

    fn nb_inputs(&self) -> usize {
        4
    }

    fn nb_outputs(&self) -> usize {
        4
    }

    fn name(&self) -> String {
        "matmul_m4".to_string()
    }
}

pub struct MatmulInternalGate<F: PrimeField> {
    _marker: PhantomData<F>,
}

impl<F: PrimeField> MatmulInternalGate<F> {
    pub fn new() -> Self {
        MatmulInternalGate {
            _marker: PhantomData,
        }
    }

    pub fn evaluate(&self, input: &[F], mat_internal_diag_m_1: &[F], index: Option<usize>) -> F {
        let mut input_copy = input.to_vec();
        let t = 4;
            // Compute input sum
            let mut sum = input[0];
            input
                .iter()
                .skip(1)
                .take(t-1)
                .for_each(|el| sum.add_assign(el));
            // Add sum + diag entry * element to each element
        for i in 0..input.len() {
            input_copy[i].mul_assign(&mat_internal_diag_m_1[i]);
            input_copy[i].add_assign(&sum);
        }

        if let Some(index) = index {
            input_copy[index]
        } else {
            panic!("index is not set");
        }
    }

    fn degree(&self) -> usize {
        1
    }

    fn nb_inputs(&self) -> usize {
        4
    }

    fn nb_outputs(&self) -> usize {
        1
    }

    fn name(&self) -> String {
        "matmul_internal".to_string()
    }
}

pub struct AddRcGate<F: PrimeField> {
    rc: Vec<F>,
}

impl<F: PrimeField> AddRcGate<F> {
    pub fn new(rc: Vec<F>) -> Self {
        AddRcGate {
            rc,
        }
    }

    pub fn evaluate(&self, input: &[F], index: Option<usize>) -> F {
        let output = input
            .iter()
            .zip(self.rc.iter())
            .map(|(a, b)| {
                let mut r = *a;
                r.add_assign(b);
                r
            })
            .collect_vec();

        if let Some(index) = index {
            output[index]
        } else {
            panic!("index is not set");
        }
    }

    pub fn evaluate_full(&self, input: &[F]) -> Vec<F> {
        input
            .iter()
            .zip(self.rc.iter())
            .map(|(a, b)| {
                let mut r = *a;
                r.add_assign(b);
                r
            })
            .collect_vec()
    }

    fn degree(&self) -> usize {
        1
    }

    fn nb_inputs(&self) -> usize {
        4
    }

    fn nb_outputs(&self) -> usize {
        1
    }

    fn name(&self) -> String {
        "add_rc".to_string()
    }
}

#[allow(unused_imports)]
#[cfg(test)]
mod poseidon2_tests_bn256 {
    use super::*;
    use halo2_proofs::halo2curves::ff::Field;
    use rand::thread_rng;
    use super::super::super::utils::from_hex;
    use super::super::poseidon2_instance_bn256::POSEIDON2_BN256_PARAMST3;
    use std::convert::TryFrom;

    use halo2_proofs::halo2curves::bn256::Fr;
    type Scalar = Fr;
    static TESTRUNS: usize = 5;

    #[test]
    fn consistent_perm() {
        let poseidon2 = Poseidon2::new(&POSEIDON2_BN256_PARAMST3);
        let t = poseidon2.params.t;
        for _ in 0..TESTRUNS {
            let input1: Vec<Scalar> = (0..t).map(|_| Scalar::random(&mut thread_rng())).collect();

            let mut input2: Vec<Scalar>;
            loop {
                input2 = (0..t).map(|_| Scalar::random(&mut thread_rng())).collect();
                if input1 != input2 {
                    break;
                }
            }

            let perm1 = poseidon2.permutation(&input1);
            let perm2 = poseidon2.permutation(&input1);
            let perm3 = poseidon2.permutation(&input2);
            assert_eq!(perm1, perm2);
            assert_ne!(perm1, perm3);
        }
    }

    #[test]
    fn kats() {
        let poseidon2 = Poseidon2::new(&POSEIDON2_BN256_PARAMST3);
        let mut input: Vec<Scalar> = vec![];
        for i in 0..poseidon2.params.t {
            input.push(Scalar::from(i as u64));
        }
        let perm = poseidon2.permutation(&input);
        assert_eq!(perm[0], from_hex("0x0bb61d24daca55eebcb1929a82650f328134334da98ea4f847f760054f4a3033"));
        assert_eq!(perm[1], from_hex("0x303b6f7c86d043bfcbcc80214f26a30277a15d3f74ca654992defe7ff8d03570"));
        assert_eq!(perm[2], from_hex("0x1ed25194542b12eef8617361c3ba7c52e660b145994427cc86296242cf766ec8"));

    }
}
