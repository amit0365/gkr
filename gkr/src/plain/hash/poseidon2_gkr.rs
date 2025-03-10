use std::marker::PhantomData;
use halo2_proofs::halo2curves::ff::{Field, PrimeField};
use crate::{plain::scalar_mul::DblAddSelectGate, util::arithmetic::{fe_to_bits_le, fe_to_fe}};
use super::poseidon2_instance_bn256::POSEIDON2_BN256_PARAMS;
use super::poseidon2::Poseidon2;
use halo2_proofs::halo2curves::bn256;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Poseidon2Gate<F: Field> {
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Poseidon2Gate<F> {
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }

    pub fn evaluate(&self, inputs: &[F], index: Option<usize>) -> F {
        let mut inputs = inputs.to_vec();
        let scalar = inputs.last().unwrap();
        let scalar_bits = fe_to_bits_le(scalar.clone());
        for i in 0..scalar_bits.len() {
            let outputs = Poseidon2::new(&POSEIDON2_BN256_PARAMS).permutation(&inputs.iter().map(|x| fe_to_fe::<F, bn256::Fr>(*x)).collect::<Vec<_>>());
            inputs = outputs[..6].iter().map(|x| fe_to_fe::<bn256::Fr, F>(*x)).collect();
        };
        if let Some(index) = index {
            inputs[index]
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
        "scalar_mul".to_string()
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

		let input_polys = [
			MultivariatePolynomial::new(vec![p0_terms.clone()], vec![Fr::ONE], 2, 2, m).unwrap(), 
			MultivariatePolynomial::new(vec![p1_terms.clone()], vec![Fr::ONE], 2, 3, m).unwrap(),
            MultivariatePolynomial::new(vec![p2_terms.clone()], vec![Fr::ONE], 2, 4, m).unwrap(),
		];
        let output_poly = MultivariatePolynomial::new(vec![p0_terms, p1_terms, p2_terms], 
            vec![Fr::ONE; 3], 2, 7, m).unwrap();

        let c = {
            let wires = (0..6).map(|_| Wire::new(AnyGate::new_identity(), vec![], 1)).collect_vec();
            vec![wires[0].clone(), wires[1].clone(), wires[2].clone(), Wire::new(AnyGate::new_dbl_add(), 
            vec![wires[0].clone(), wires[1].clone(), wires[2].clone()], 3)]
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
