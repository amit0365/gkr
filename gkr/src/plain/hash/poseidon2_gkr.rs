use std::marker::PhantomData;
use halo2_proofs::halo2curves::ff::{Field, PrimeField};
use crate::{plain::{hash::poseidon2::{AddRcGate, MatmulM4Gate, Sbox5T4Gate}, scalar_mul::DblAddSelectGate}, util::arithmetic::{fe_to_bits_le, fe_to_fe}};
use super::{poseidon2_instance_bn256::POSEIDON2_BN256_PARAMST4, poseidon2_params::Poseidon2Params};
use super::poseidon2::Poseidon2;
use halo2_proofs::halo2curves::bn256;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Poseidon2T4Gate<F: PrimeField> {
    params: Poseidon2Params<F>,
}

impl<F: PrimeField> Poseidon2T4Gate<F> {
    pub fn new(params: &Poseidon2Params<F>) -> Self {
        Self {
            params: params.clone(),
        }
    }

    pub fn evaluate(&self, inputs: &[F], index: Option<usize>) -> F {
        let mut inputs = inputs.to_vec();
        let t = 4;
        assert_eq!(inputs.len(), t);

        let mut current_state = inputs.to_owned();

        // Linear layer at beginning
        let matmul_m4 = MatmulM4Gate::<F>::new();
        current_state = matmul_m4.evaluate_full(&current_state);

        for r in 0..self.params.rounds_f_beginning {
            current_state = AddRcGate::<F>::new(self.params.round_constants[r].clone()).evaluate_full(&current_state);
            current_state = Sbox5T4Gate::<F>::new().evaluate_full(&current_state);
            current_state = MatmulM4Gate::<F>::new().evaluate_full(&current_state);
        }

        let p_end = self.params.rounds_f_beginning + self.params.rounds_p;
        for r in self.params.rounds_f_beginning..p_end {
            current_state[0].add_assign(&self.params.round_constants[r][0]);
            current_state[0] = Sbox5T4Gate::<F>::new().evaluate(&[current_state[0]], Some(0));
            current_state = MatmulM4Gate::<F>::new().evaluate_full(&current_state);
        }
        
        for r in p_end..self.params.rounds {
            current_state = AddRcGate::<F>::new(self.params.round_constants[r].clone()).evaluate_full(&current_state);
            current_state = Sbox5T4Gate::<F>::new().evaluate_full(&current_state);
            current_state = MatmulM4Gate::<F>::new().evaluate_full(&current_state);
        }

        if let Some(index) = index {
            current_state[index]
        } else {
            panic!("index is not set");
        }
    }

    pub fn degree(&self) -> usize {
        1
    }

    pub fn nb_inputs(&self) -> usize {
        2
    }

    pub fn nb_outputs(&self) -> usize {
        1
    }

    pub fn name(&self) -> String {
        "poseidon2_t4".to_string()
    }
}

#[allow(unused_imports)]
#[cfg(test)]
mod tests {
    use std::io;
    use poseidon::Spec;
    use itertools::Itertools;
    use std::collections::HashMap;
    use crate::plain::gkr::gkr_verify;
    use crate::plain::hash::poseidon2_instance_bn256::POSEIDON2_BN256_PARAMST4;

    use halo2_proofs::{arithmetic::Field, halo2curves::bn256::Fr};
    use crate::plain::gkr::{gkr_prove, AddGate, AnyGate, GKRCircuit, Wire, WireAssignment};
    use crate::poly::multivariate::{make_subgroup_elements, MultivariatePolynomial};

    use crate::util::transcript::InMemoryTranscript;
	use crate::util::transcript::PoseidonNativeTranscript;

	const T: usize = 4;
	const RATE: usize = 3;
	const R_F: usize = 8;
	const R_P: usize = 56;

    #[test]
    fn test_gkr_poseidon2_gate() {

        let m: usize = 16;
		let num_vars = 2;
		let points = make_subgroup_elements::<Fr>(m as u64);
		let domain = points.chunks(m/num_vars).take(num_vars).map(|chunk| chunk.to_vec()).collect_vec(); 
		
		// add gate polynomial with input preprocessors f(P_0(x, y),..,P_n(x, y)) = P_0(x, y) + P_1(x, y) + .. + P_n(x, y)
		// consider fan in 2 so f(P_0(x, y), P_1(x, y)) = P_0(x, y) + P_1(x, y)
		// we can model input preprocessors as P_0(x, y) = x*y and P_1(x, y) = x*y^3
		let p0_terms: Vec<(usize, usize)> = vec![(0, 1), (1, 1)];
		let p1_terms: Vec<(usize, usize)> = vec![(0, 1), (1, 2)];
        let p2_terms: Vec<(usize, usize)> = vec![(0, 1), (1, 3)];
        let p3_terms: Vec<(usize, usize)> = vec![(0, 1), (1, 4)];

		let input_polys = [
			MultivariatePolynomial::new(vec![p0_terms.clone()], vec![Fr::ONE], 2, 2, m).unwrap(), 
			MultivariatePolynomial::new(vec![p1_terms.clone()], vec![Fr::ONE], 2, 3, m).unwrap(),
            MultivariatePolynomial::new(vec![p2_terms.clone()], vec![Fr::ONE], 2, 4, m).unwrap(),
            MultivariatePolynomial::new(vec![p3_terms.clone()], vec![Fr::ONE], 2, 5, m).unwrap(),
		];
        let output_poly = MultivariatePolynomial::new(vec![p0_terms, p1_terms, p2_terms, p3_terms], 
            vec![Fr::ONE; 4], 2, 5, m).unwrap();

        let c = {
            let wires = (0..6).map(|_| Wire::new(AnyGate::new_identity(), vec![], 1)).collect_vec();
            vec![wires[0].clone(), wires[1].clone(), wires[2].clone(), wires[3].clone(), 
            Wire::new(AnyGate::new_poseidon2_t4(&POSEIDON2_BN256_PARAMST4), 
            vec![wires[0].clone(), wires[1].clone(), wires[2].clone(), wires[3].clone()], 1)]
        };

        let mut assignment = HashMap::new();
        for i in 0..3 {
            assignment.insert(c[i].clone(), input_polys[i].clone());
        }

        let spec = Spec::<Fr, T, RATE>::new(R_F, R_P); 
		let mut prover_transcript = PoseidonNativeTranscript::<Fr, io::Cursor<Vec<u8>>>::new(spec.clone());
		// each layer has 8*8 = 64 gates => each variable can have domain size, |H| = 8 = 16/2 = m/num_vars
		// degree of each variable is at most, |H| - 1 = 7

        let proof = gkr_prove(c.clone(), &assignment, &mut prover_transcript);
        assert!(proof.is_ok());
        let proof_bytes = prover_transcript.into_proof();

        let mut verifier_transcript = PoseidonNativeTranscript::<Fr, io::Cursor<Vec<u8>>>::from_proof(spec, &proof_bytes);
        gkr_verify(c, assignment, &mut verifier_transcript, &proof.unwrap()).unwrap();
    }
}
