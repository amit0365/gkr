use halo2_proofs::arithmetic::Field;
use halo2_proofs::halo2curves::ff::PrimeField;
use std::marker::PhantomData;

use crate::util::arithmetic::fe_to_bits_le;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProjAddGate<F: Field> {
    _marker: PhantomData<F>,
}

impl<F: PrimeField> ProjAddGate<F> {
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }

    pub fn evaluate(&self, inputs: &[F]) -> (F, F, F) {
        assert_eq!(inputs.len(), self.nb_inputs());
        
        let (x1, y1, z1) = (inputs[0], inputs[1], inputs[2]);
        let (x2, y2, z2) = (inputs[3], inputs[4], inputs[5]);
        
        let b3 = F::from(21);
        let t0 = x1 * x2;
        let t1 = y1 * y2;
        let t2 = z1 * z2;
        let mut t3 = (x1 + y1) * (x2 + y2);
        let mut t4 = t0 + t1;
        t3 -= t4;
        t4 = (y1 + z1) * (y2 + z2);
        let mut x3 = t1 + t2;
        t4 -= x3;
        x3 = (x1 + z1) * (x2 + z2);
        let mut y3 = t0 + t2;
        y3 = x3 - y3;
        x3 = t0 + t0 + t0;
        let t2 = b3 * t2;
        let mut z3 = t1 + t2;
        let t1 = t1 - t2;
        let y3 = b3 * y3;
        x3 = t4 * y3;
        let t2 = t3 * t1;
        x3 = t2 - x3;
        let y3 = y3 * (t0 + t0 + t0);
        let t1 = t1 * z3;
        let y3 = t1 + y3;
        let t0 = (t0 + t0 + t0) * t3;
        z3 *= t4;
        z3 += t0;

        (x3, y3, z3)
    }

    fn degree(&self) -> usize {
        4
    }

    fn nb_inputs(&self) -> usize {
        6
    }

    fn nb_outputs(&self) -> usize {
        1
    }

    fn name(&self) -> String {
        "projadd".to_string()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProjSelectGate<F: Field> {
    _marker: PhantomData<F>,
}

impl<F: Field> ProjSelectGate<F> {
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }

    pub fn evaluate(&self, inputs: &[F]) -> (F, F, F) {
        let (selector, x1, y1, z1, x2, y2, z2) = (
            inputs[0], inputs[1], inputs[2], inputs[3], 
            inputs[4], inputs[5], inputs[6]
        );

        let mut x3 = x1 - x2;
        x3 = selector * x3;
        x3 += x2;

        let mut y3 = y1 - y2;
        y3 = selector * y3;
        y3 += y2;

        let mut z3 = z1 - z2;
        z3 = selector * z3;
        z3 += z2;

        (x3, y3, z3)
    }

    fn degree(&self) -> usize {
        2
    }

    fn nb_inputs(&self) -> usize {
        7
    }

    fn nb_outputs(&self) -> usize {
        1
    }

    fn name(&self) -> String {
        "projselect".to_string()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ProjDblGate<F: PrimeField> {
    _marker: PhantomData<F>,
}

impl<F: PrimeField> ProjDblGate<F> {
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }

    pub fn evaluate(&self, inputs: &[F]) -> (F, F, F) {
        let (x, y, z) = (inputs[0], inputs[1], inputs[2]);
        let b3 = F::from(21);
        let t0 = y * y;
        let mut z3 = t0 + t0;
        z3 = z3 + z3;
        z3 = z3 + z3;
        let t1 = y * z;
        let mut t2 = z * z;
        t2 = b3 * t2;
        let mut x3 = t2 * z3;
        let mut y3 = t0 + t2;
        z3 = t1 * z3;
        let t1 = t2 + t2;
        t2 = t1 + t2;
        let t0 = t0 - t2;
        y3 = t0 * y3;
        y3 = x3 + y3;
        let t1 = x * y;
        x3 = t0 * t1;
        x3 = x3 + x3;

        (x3, y3, z3)
    }

    fn degree(&self) -> usize {
        4
    }

    fn nb_inputs(&self) -> usize {
        3
    }

    fn nb_outputs(&self) -> usize {
        1
    }

    fn name(&self) -> String {
        "projdbl".to_string()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DblAddSelectGate<F: PrimeField> {
    _marker: PhantomData<F>,
}

impl<F: PrimeField> DblAddSelectGate<F> {
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }

    pub fn evaluate(&self, inputs: &[F], index: Option<usize>) -> F {
        if inputs.len() != self.nb_inputs() {
            panic!("incorrect nb of inputs");
        }

        // X1, Y1, Z1 == accumulator
        let (x1, y1, z1) = (inputs[0], inputs[1], inputs[2]);
        // X2, Y2, Z2 == result  
        let (x2, y2, z2) = (inputs[3], inputs[4], inputs[5]);
        let selector = inputs[6];

        let (tmp_x, tmp_y, tmp_z) = ProjAddGate::<F>::new().evaluate(&[x1, y1, z1, x2, y2, z2]);
        let (res_x, res_y, res_z) = ProjSelectGate::<F>::new().evaluate(&[selector, tmp_x, tmp_y, tmp_z, x2, y2, z2]);
        let (acc_x, acc_y, acc_z) = ProjDblGate::<F>::new().evaluate(&[x1, y1, z1]);

        let res = [acc_x, acc_y, acc_z, res_x, res_y, res_z];
        if let Some(index) = index {
            res[index]
        } else {
            panic!("index is not set");
        }

    }

    pub fn evaluate_full(&self, inputs: &[F]) -> Vec<F> {
        if inputs.len() != self.nb_inputs() {
            panic!("incorrect nb of inputs");
        }

        // X1, Y1, Z1 == accumulator
        let (x1, y1, z1) = (inputs[0], inputs[1], inputs[2]);
        // X2, Y2, Z2 == result  
        let (x2, y2, z2) = (inputs[3], inputs[4], inputs[5]);
        let selector = inputs[6];

        let (tmp_x, tmp_y, tmp_z) = ProjAddGate::<F>::new().evaluate(&[x1, y1, z1, x2, y2, z2]);
        let (res_x, res_y, res_z) = ProjSelectGate::<F>::new().evaluate(&[selector, tmp_x, tmp_y, tmp_z, x2, y2, z2]);
        let (acc_x, acc_y, acc_z) = ProjDblGate::<F>::new().evaluate(&[x1, y1, z1]);

        vec![acc_x, acc_y, acc_z, res_x, res_y, res_z]
    }

    pub fn degree(&self) -> usize {
        5
    }

    pub fn nb_inputs(&self) -> usize {
        7
    }

    pub fn nb_outputs(&self) -> usize {
        1
    }

    pub fn name(&self) -> String {
        "dbladdselect".to_string()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ScalarMulGate<F: Field> {
    _marker: PhantomData<F>,
}

impl<F: PrimeField> ScalarMulGate<F> {
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
            let outputs = DblAddSelectGate::new().evaluate_full(&[inputs[0], inputs[1], inputs[2], inputs[3], inputs[4], inputs[5], scalar_bits[i]]);
            inputs = outputs[..6].to_vec();
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
    fn test_gkr_double_add_gate() {

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
        let p4_terms: Vec<(usize, usize)> = vec![(0, 1), (1, 5)];
        let p5_terms: Vec<(usize, usize)> = vec![(0, 1), (1, 6)];

		let input_polys = [
			MultivariatePolynomial::new(vec![p0_terms.clone()], vec![Fr::ONE], 2, 2, m).unwrap(), 
			MultivariatePolynomial::new(vec![p1_terms.clone()], vec![Fr::ONE], 2, 3, m).unwrap(),
            MultivariatePolynomial::new(vec![p2_terms.clone()], vec![Fr::ONE], 2, 4, m).unwrap(),
            MultivariatePolynomial::new(vec![p3_terms.clone()], vec![Fr::ONE], 2, 5, m).unwrap(),
            MultivariatePolynomial::new(vec![p4_terms.clone()], vec![Fr::ONE], 2, 6, m).unwrap(),
            MultivariatePolynomial::new(vec![p5_terms.clone()], vec![Fr::ONE], 2, 7, m).unwrap()
		];
        let output_poly = MultivariatePolynomial::new(vec![p0_terms, p1_terms, p2_terms, p3_terms, p4_terms, p5_terms], 
            vec![Fr::ONE; 6], 2, 7, m).unwrap();

        let c = {
            let wires = (0..6).map(|_| Wire::new(AnyGate::new_identity(), vec![], 1)).collect_vec();
            vec![wires[0].clone(), wires[1].clone(), wires[2].clone(), wires[3].clone(), wires[4].clone(), wires[5].clone(), Wire::new(AnyGate::new_dbl_add(), 
            vec![wires[0].clone(), wires[1].clone(), wires[2].clone(), wires[3].clone(), wires[4].clone(), wires[5].clone()], 6)]
        };

        let mut assignment = HashMap::new();
        for i in 0..6 {
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

    #[test]
    fn test_gkr_scalar_mul_gate() {

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
        let p4_terms: Vec<(usize, usize)> = vec![(0, 1), (1, 5)];
        let p5_terms: Vec<(usize, usize)> = vec![(0, 1), (1, 6)];

		let input_polys = [
			MultivariatePolynomial::new(vec![p0_terms.clone()], vec![Fr::ONE], 2, 2, m).unwrap(), 
			MultivariatePolynomial::new(vec![p1_terms.clone()], vec![Fr::ONE], 2, 3, m).unwrap(),
            MultivariatePolynomial::new(vec![p2_terms.clone()], vec![Fr::ONE], 2, 4, m).unwrap(),
            MultivariatePolynomial::new(vec![p3_terms.clone()], vec![Fr::ONE], 2, 5, m).unwrap(),
            MultivariatePolynomial::new(vec![p4_terms.clone()], vec![Fr::ONE], 2, 6, m).unwrap(),
            MultivariatePolynomial::new(vec![p5_terms.clone()], vec![Fr::ONE], 2, 7, m).unwrap()
		];
        let output_poly = MultivariatePolynomial::new(vec![p0_terms, p1_terms, p2_terms, p3_terms, p4_terms, p5_terms], 
            vec![Fr::ONE; 6], 2, 7, m).unwrap();

        let c = {
            let wires = (0..6).map(|_| Wire::new(AnyGate::new_identity(), vec![], 1)).collect_vec();
            vec![wires[0].clone(), wires[1].clone(), wires[2].clone(), wires[3].clone(), wires[4].clone(), wires[5].clone(), Wire::new(AnyGate::new_scalar_mul(), 
            vec![wires[0].clone(), wires[1].clone(), wires[2].clone(), wires[3].clone(), wires[4].clone(), wires[5].clone()], 6)]
        };

        let mut assignment = HashMap::new();
        for i in 0..6 {
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