use std::cmp::max_by;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::hash::Hash;
use itertools::Itertools;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::halo2curves::ff::PrimeField;

use crate::poly::multivariate::{eq_poly_fix_first_var_univariate, eq_poly_univariate, lagrange_bases, make_subgroup_elements, MultivariatePolynomial};
use crate::poly::univariate::{CoefficientBasis, UnivariatePolynomial};
use crate::util::arithmetic::fe_to_bits_le;
use crate::util::transcript::{FieldTranscriptRead, FieldTranscriptWrite};
use crate::Error;

use super::hash::poseidon2_gkr::Poseidon2T4Gate;
use super::hash::poseidon2_params::Poseidon2Params;
use super::scalar_mul::{DblAddSelectGate, ScalarMulGate};
//pub const M: u64 = 20;
use super::sumcheck::{sumcheck_prove, sumcheck_verify, Claims, LazyClaims, SumCheckProof};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IdentityGate<F: Field>{
    _marker: PhantomData<F>,
}

impl<F: Field> IdentityGate<F> {
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }

    pub fn evaluate(&self, inputs: &[F]) -> F {
        inputs[0]
    }

    fn degree(&self) -> usize {
        1
    }

    fn nb_inputs(&self) -> usize {
        1
    }

    fn nb_outputs(&self) -> usize {
        1
    }

    fn name(&self) -> String {
        "identity".to_string()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AddGate<F: Field>{
    _marker: PhantomData<F>,
}

impl<F: Field> AddGate<F> {
    pub fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }

    pub fn evaluate(&self, inputs: &[F]) -> F {
        inputs.iter().sum()
    }

    fn degree(&self) -> usize {
        1
    }

    fn nb_inputs(&self) -> usize {
        2
    }

    fn nb_outputs(&self) -> usize {
        1
    }

    fn name(&self) -> String {
        "add".to_string()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MulGate<F: Field>{
    _marker: PhantomData<F>,
}

impl<F: Field> MulGate<F> {
    fn new() -> Self {
        Self {
            _marker: PhantomData,
        }
    }

    fn evaluate(&self, inputs: &[F]) -> F {
        inputs.iter().product()
    }

    fn degree(&self) -> usize {
        1
    }

    fn nb_inputs(&self) -> usize {
        2
    }

    fn nb_outputs(&self) -> usize {
        1
    }

    fn name(&self) -> String {
        "mul".to_string()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AnyGate<F: PrimeField> {
    Add(AddGate<F>),
    Identity(IdentityGate<F>),
    Mul(MulGate<F>),
    DblAdd(DblAddSelectGate<F>),
    ScalarMul(ScalarMulGate<F>),
    Poseidon2T4(Poseidon2T4Gate<F>),
}

impl<F: PrimeField> GateInstructions<F> for AnyGate<F> {
    fn evaluate(&self, inputs: &[F], index: Option<usize>) -> F {
        match self {
            AnyGate::Add(gate) => gate.evaluate(inputs),
            AnyGate::Identity(gate) => gate.evaluate(inputs),
            AnyGate::Mul(gate) => gate.evaluate(inputs),
            AnyGate::DblAdd(gate) => gate.evaluate(inputs, index),
            AnyGate::ScalarMul(gate) => gate.evaluate(inputs, index),
            AnyGate::Poseidon2T4(gate) => gate.evaluate(inputs, index),
        }
    }

    fn degree(&self) -> usize {
        match self {
            AnyGate::Add(gate) => gate.degree(),
            AnyGate::Identity(gate) => gate.degree(),
            AnyGate::Mul(gate) => gate.degree(),
            AnyGate::DblAdd(gate) => gate.degree(),
            AnyGate::ScalarMul(gate) => gate.degree(),
            AnyGate::Poseidon2T4(gate) => gate.degree(),
        }
    }   

    fn nb_inputs(&self) -> usize {
        match self {
            AnyGate::Add(gate) => gate.nb_inputs(),
            AnyGate::Identity(gate) => gate.nb_inputs(),
            AnyGate::Mul(gate) => gate.nb_inputs(),
            AnyGate::DblAdd(gate) => gate.nb_inputs(),
            AnyGate::ScalarMul(gate) => gate.nb_inputs(),
            AnyGate::Poseidon2T4(gate) => gate.nb_inputs(),
        }
    }

    fn nb_outputs(&self) -> usize {
        match self {
            AnyGate::Add(gate) => gate.nb_outputs(),
            AnyGate::Identity(gate) => gate.nb_outputs(),
            AnyGate::Mul(gate) => gate.nb_outputs(),
            AnyGate::DblAdd(gate) => gate.nb_outputs(),
            AnyGate::ScalarMul(gate) => gate.nb_outputs(),
            AnyGate::Poseidon2T4(gate) => gate.nb_outputs(),
        }
    }

    fn name(&self) -> String {
        match self {
            AnyGate::Add(gate) => gate.name(),
            AnyGate::Identity(gate) => gate.name(),
            AnyGate::Mul(gate) => gate.name(),
            AnyGate::DblAdd(gate) => gate.name(),
            AnyGate::ScalarMul(gate) => gate.name(),
            AnyGate::Poseidon2T4(gate) => gate.name(),
        }
    }
}

impl<F: PrimeField> AnyGate<F> {
    pub fn new_add() -> Self {
        Self::Add(AddGate::new())
    }
    
    pub fn new_identity() -> Self {
        Self::Identity(IdentityGate::new()) 
    }
    
    pub fn new_mul() -> Self {
        Self::Mul(MulGate::new())
    }

    pub fn new_dbl_add() -> Self {
        Self::DblAdd(DblAddSelectGate::new())
    }

    pub fn new_scalar_mul() -> Self {
        Self::ScalarMul(ScalarMulGate::new())
    }

    pub fn new_poseidon2_t4(params: &Poseidon2Params<F>) -> Self {
        Self::Poseidon2T4(Poseidon2T4Gate::new(params))
    }
}

pub trait GateInstructions<F: PrimeField> {
    fn evaluate(&self, input: &[F], index: Option<usize>) -> F;
    fn degree(&self) -> usize;
    fn nb_inputs(&self) -> usize;
    fn nb_outputs(&self) -> usize;
    fn name(&self) -> String;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Wire<F: PrimeField + Hash> {
    gate: AnyGate<F>,
    inputs: Vec<Wire<F>>,
    nb_unique_outputs: usize,
    _marker: PhantomData<F>,
}

pub type GKRCircuit<F> = Vec<Wire<F>>;

impl<F: PrimeField + Hash> Wire<F> {
    pub fn new(gate: AnyGate<F>, inputs: Vec<Wire<F>>, nb_unique_outputs: usize) -> Self {
        Self {
            gate,
            inputs,
            nb_unique_outputs,
            _marker: PhantomData,
        }
    }

    fn is_input(&self) -> bool {
        self.inputs.is_empty()
    }

    fn is_output(&self) -> bool {
        self.nb_unique_outputs == 0
    }

    fn nb_claims(&self) -> usize {
        if self.is_output() {
            1
        } else {
            self.nb_unique_outputs
        }
    }

    fn nb_unique_inputs(&self) -> usize {
        todo!()
        // let set: HashSet<_> = self.inputs.iter().collect();
        // set.len()
    }

    fn no_proof(&self) -> bool {
        self.is_input() && self.nb_claims() == 1
    }

    fn max_gate_degree(c: &GKRCircuit<F>) -> usize {
        let mut res = 1;
        for i in c.iter() {
            if !i.is_input() {
                res = max_by(res, i.gate.degree(), Ord::cmp);
            }
        }
        res
    }
}

// WireAssignment is assignment of values to the same wire across many instances of the circuit
pub type WireAssignment<F> = HashMap<Wire<F>, MultivariatePolynomial<F, CoefficientBasis>>;

pub type Proof<F> = Vec<SumCheckProof<F>>; // for each layer, for each wire, a sumcheck (for each variable, a polynomial)

#[derive(Debug, Clone)]
pub struct EqTimesGateEvalSumcheckLazyClaims<F: PrimeField + Hash> {
    wire: Wire<F>,
    domain: Vec<Vec<F>>,
    evaluation_points: Vec<Vec<F>>,
    claimed_evaluations: Vec<F>,
    manager: ClaimsManager<F>,
}

impl<F: PrimeField + Hash> LazyClaims<F> for EqTimesGateEvalSumcheckLazyClaims<F> {
    fn input_preprocessors(&self) -> Vec<MultivariatePolynomial<F, CoefficientBasis>> {
        self.wire.inputs.iter().map(|input| self.manager.assignment[input].clone()).collect_vec()
    }

    fn gate(&self) -> AnyGate<F> {
        self.wire.gate.clone()
    }

    fn verify_final_eval(&mut self, r: &[F], combination_coeff: F, purported_value: F, proof: &[F]) -> Result<(), Error> {
		unimplemented!()
    }

    fn claims_num(&self) -> usize {
        self.evaluation_points.len()
    }

    fn vars_num(&self) -> usize {
        self.evaluation_points[0].len()
    }

    fn combined_sum(&self, poly_evaluation: &[F], var_idx: usize) -> F {
		// already have evals over the full domain, so we can just sum over respective domain
		// note that full domain is distributed over variables respectively
		let partition = poly_evaluation.len()/self.vars_num();
		poly_evaluation[(var_idx)*partition..(var_idx+1)*partition].iter().sum::<F>()
    }

    fn claimed_sum(&self) -> F {
        // use rlc to combine the evaluations
        self.claimed_evaluations[0]
    }

    fn domain(&self) -> Vec<Vec<F>> {
        self.domain.clone()
    }

    fn full_domain(&self) -> Vec<F> {
        self.domain.iter().flatten().cloned().collect_vec()
    }

    fn degree(&self) -> usize {
        1 + self.wire.gate.degree()
    }
}

struct EqTimesGateEvalSumcheckClaims<F: PrimeField + Hash> {
	wire:                Wire<F>,
	evaluation_points:   Vec<Vec<F>>, // x in the paper
	claimed_evaluations: Vec<F>,   // y in the paper
    domain:              Vec<Vec<F>>, // same domain for all claims
	manager:             ClaimsManager<F>,
    /// We denote input_preprocessors, P_i(x, y) as a multivariate polynomial 
    /// which represents all the ith input to the gate across the data parallel circuits  
    /// s.t. deg of sum_check_poly f'(P_0(x, y), ..., P_k(x, y)) in each variable <= |H| - 1
    /// while the overall degree should be low s.t.  d/|F| << 1
	input_preprocessors: Vec<MultivariatePolynomial<F, CoefficientBasis>>, 
	eq: Vec<Vec<F>>,     // ∑_i τ_i eq(x_i, -)
}

impl<F: PrimeField + Hash> EqTimesGateEvalSumcheckClaims<F> {
    pub fn compute_gj(&self, 
        input_preprocessors: Vec<UnivariatePolynomial<F, CoefficientBasis>>, 
        eq_evals_univariate: Vec<F>
    ) -> Vec<F> { // can use fft here
		let full_domain = self.domain.iter().flatten().cloned().collect_vec();
		full_domain.iter()
		.zip(&eq_evals_univariate)
		.map(|(p, eq)| self.gate().evaluate(&input_preprocessors.iter().map(|prep| prep.evaluate(p)).collect_vec(), None)) //*eq * 
		.collect()
    }
}

impl<F: PrimeField + Hash> Claims<F> for EqTimesGateEvalSumcheckClaims<F> {
    fn input_preprocessors(&self) -> Vec<MultivariatePolynomial<F, CoefficientBasis>> {
        self.input_preprocessors.clone()
    }

    fn eq(&self) -> Vec<Vec<F>> {
        self.eq.clone()
    }

    fn gate(&self) -> AnyGate<F> {
        self.wire.gate.clone()
    }

    fn combine_and_first_poly(&mut self, domain: &[&[F]], a: F) -> Vec<F> { //eq combining algo    
		let vars_num = self.vars_num();
        let eq_length  = vars_num;
		assert_eq!(domain.len(), eq_length);
		let full_domain = self.full_domain();
		let full_domain_vec = vec![full_domain.as_slice(); vars_num];
        let claims_num = self.claims_num();

		// Batching subprotocol for GKR, section 6.3 in paper
		// initialize the eq tables where lagrange bases are evaluations for all x in H at a_k
		let eq = lagrange_bases(&full_domain_vec, &self.evaluation_points[0]);
		assert_eq!(eq.len(), eq_length);
		assert_eq!(eq[0].len(), full_domain.len());
        let eq_acc = (1..claims_num).fold(eq, |mut acc, k| {
            let eq = lagrange_bases(&full_domain_vec, &self.evaluation_points[k]);
			acc[k].iter_mut().zip(&eq[k]).for_each(|(acc, eq)| *acc = *eq * a.pow([k as u64]));
			acc
        });
		self.eq = eq_acc.clone();
		
        // from this point on the claim is a rather simple one: g = E(h) × R_v (P_u0(h), ...) 
        // where E and the P_u are multilinear and R_v is of low-degree
		let mut input_preprocessors = Vec::new();
        for (i, preprocessor) in &mut self.input_preprocessors.iter_mut().enumerate() {
            input_preprocessors.push(preprocessor.univariate_poly_first_summed(domain));
        }
		let eq_evals_univariate = eq_poly_univariate(&eq_acc); 
        self.compute_gj(input_preprocessors, eq_evals_univariate)
    }

    fn next(&mut self, domain: &[&[F]], element: F, var_idx: usize) -> Vec<F> {
		let mut input_preprocessors = Vec::new();
        for preprocessor in &mut self.input_preprocessors {
            input_preprocessors.push(preprocessor.univariate_poly_fix_var(domain, &element));
        }
        let eq = eq_poly_fix_first_var_univariate(&self.full_domain(), &self.eq, &element); // domain for second variable
        self.compute_gj(input_preprocessors, eq)
    }

    fn prove_final_eval(&self, r: &[F]) -> Vec<F> {
        todo!()
    }

    fn domain(&self) -> Vec<Vec<F>> {
        self.domain.clone()
    }

    fn full_domain(&self) -> Vec<F> {
        self.domain.iter().flatten().cloned().collect_vec()
    }

    fn claims_num(&self) -> usize {
        self.evaluation_points.len()
    }

    fn claimed_sum(&self) -> F {
        unimplemented!()
    }

    fn vars_num(&self) -> usize {
        self.evaluation_points[0].len()
    }

    fn degree(&self) -> usize {
        1 + self.wire.gate.degree()
    }

}

#[derive(Debug, Clone)]
struct ClaimsManager<F: PrimeField + Hash> {
    claims_map: HashMap<Wire<F>, EqTimesGateEvalSumcheckLazyClaims<F>>,
    assignment: WireAssignment<F>,
}

impl<F: PrimeField + Hash> ClaimsManager<F> {
    fn new(c: &GKRCircuit<F>, assignment: &WireAssignment<F>) -> Self {
        let mut claims = ClaimsManager {
            assignment: assignment.clone(),
            claims_map: HashMap::with_capacity(c.len()),
        };
        let num_vars = assignment[&c[0]].num_vars;
        let domain = assignment[&c[0]].domain.clone();
        for wire in c {
            claims.claims_map.insert(wire.clone(), EqTimesGateEvalSumcheckLazyClaims {
                wire: wire.clone(),
                domain: domain.clone(),
                evaluation_points: vec![vec![F::ZERO; num_vars]; wire.nb_claims()],
                claimed_evaluations: vec![F::ZERO; wire.nb_claims()],
                manager: claims.clone(),
            });
        }
        claims
    }

    fn add(&mut self, wire: &Wire<F>, evaluation_point: &[F], evaluation: F) {
        let claim = self.claims_map.get_mut(wire).unwrap();
        let i = claim.evaluation_points.len();
        claim.claimed_evaluations[i - 1] = evaluation; // todo check this, gnark code assumes evaluation_points starts from 0 length
        claim.evaluation_points[i - 1] = evaluation_point.to_vec();
    }

    fn get_lazy_claim(&mut self, wire: &Wire<F>) -> &mut EqTimesGateEvalSumcheckLazyClaims<F> {
        self.claims_map.get_mut(wire).unwrap()
    }

    fn get_claim(&self, wire: &Wire<F>) -> EqTimesGateEvalSumcheckClaims<F> {
        let lazy = self.claims_map.get(wire).unwrap();
        let mut res = EqTimesGateEvalSumcheckClaims {
            wire: wire.clone(),
            evaluation_points:   lazy.evaluation_points.clone(),
            claimed_evaluations: lazy.claimed_evaluations.clone(),
            manager:             self.clone(),
            domain:              lazy.domain.clone(),
            input_preprocessors: vec![MultivariatePolynomial::default(); wire.inputs.len()],
            eq: Vec::new(),
        };
    
        if wire.is_input() {
            res.input_preprocessors = vec![self.assignment[wire].clone()];
        } else {
            res.input_preprocessors = vec![MultivariatePolynomial::default(); wire.inputs.len()];
    
            for (input_i, input_w) in wire.inputs.iter().enumerate() {
                res.input_preprocessors[input_i] = self.assignment[input_w].clone();
            }
        }
        res
    }

    fn delete_claim(&mut self, wire: Wire<F>) {
        self.claims_map.remove(&wire);
    }
}

// Prove consistency of the claimed assignment
pub fn gkr_prove<F: PrimeField + Hash>(c: GKRCircuit<F>, assignment: &WireAssignment<F>, transcript: &mut impl FieldTranscriptWrite<F>) -> Result<Proof<F>, Error> {
	let mut claims = ClaimsManager::new(&c, assignment);
	let mut proof = vec![SumCheckProof::<F>::new(); c.len()];
    let domain = assignment[&c[0]].domain.clone();
    let input_values = domain[0].iter()
        .cartesian_product(domain[1].iter())
        .map(|(x, y)| vec![*x, *y])
        .collect_vec();
    let num_vars = assignment[&c[0]].num_vars; //num_vars should be the same for all wires
	let first_challenge = transcript.squeeze_challenges(num_vars);

	for i in (0..c.len()).rev() {
		let wire = c[i].clone();    
		if wire.is_output() {
            let inputs = input_values.iter().map(|d| wire.inputs.iter().map(|input| assignment[input].evaluate(d)).collect_vec()).collect_vec();
            let evaluation = inputs.iter().map(|input| wire.gate.evaluate(input, None)).sum();
			claims.add(&wire, &first_challenge, evaluation)
		}

        let claim = claims.get_claim(&wire);
		if wire.no_proof() { // input wires with one claim only
			proof[i] = SumCheckProof::<F>::new();
		} else {
            proof[i] = sumcheck_prove(claim, transcript)?;
		}
		// the verifier checks a single claim about input wires itself
		claims.delete_claim(wire);
	}

	Ok(proof)
}

// Verify the consistency of the claimed output with the claimed input
// Unlike in Prove, the assignment argument need not be complete
pub fn gkr_verify<F: PrimeField + Hash>(c: GKRCircuit<F>, assignment: WireAssignment<F>, transcript: &mut impl FieldTranscriptRead<F>, proof: &Proof<F>) -> Result<(), Error> {
	let mut claims = ClaimsManager::new(&c, &assignment);
    let domain = assignment[&c[0]].domain.clone();
    let input_values = domain[0].iter()
        .cartesian_product(domain[1].iter())
        .map(|(x, y)| vec![*x, *y])
        .collect_vec();
    let num_vars = assignment[&c[0]].num_vars; //num_vars should be the same for all wires
	let first_challenge = transcript.squeeze_challenges(num_vars);

	for i in (0..c.len()).rev() {
		let wire = c[i].clone();
		if wire.is_output() {
            let inputs = input_values.iter().map(|d| wire.inputs.iter().map(|input| assignment[input].evaluate(d)).collect_vec()).collect_vec();
            let evaluation = inputs.iter().map(|input| wire.gate.evaluate(input, None)).sum();
			claims.add(&wire, &first_challenge, evaluation)
		}

		let proof_i = &proof[i];
		let final_eval_proof = proof_i.final_eval_proof.clone();
		let claim = claims.get_lazy_claim(&wire);
		if wire.no_proof() { // input wires with one claim only
			// make sure the proof is empty
			if !final_eval_proof.is_empty() || !proof_i.partial_sum_polys.is_empty() {
				return Err(Error::InvalidSumcheck("no proof allowed for input wire with a single claim".to_string()));
			}

			if wire.nb_claims() == 1 { // input wire
				// simply evaluate and see if it matches
				let evaluation = assignment[&wire].evaluate(&claim.evaluation_points[0]);
				assert_eq!(claim.claimed_evaluations[0], evaluation);
			}
		} else { 
            sumcheck_verify(claim, transcript)?;
        }
		claims.delete_claim(wire);
	}
	Ok(())
}

mod tests {
    use std::io;
    use poseidon::Spec;
    use itertools::Itertools;
    use std::collections::HashMap;
    use crate::plain::gkr::gkr_verify;

    use halo2_proofs::{arithmetic::Field, halo2curves::bn256::Fr};
    use super::{gkr_prove, AddGate, AnyGate, GKRCircuit, Wire, WireAssignment};
    use crate::poly::multivariate::{make_subgroup_elements, MultivariatePolynomial};

    use crate::util::transcript::InMemoryTranscript;
	use crate::util::transcript::PoseidonNativeTranscript;

	const T: usize = 4;
	const RATE: usize = 3;
	const R_F: usize = 8;
	const R_P: usize = 56;

    #[test]
    fn test_gkr_add_gate() {

        let m: usize = 8;
		let num_vars = 2;
		let points = make_subgroup_elements::<Fr>(m as u64);
		let domain = points.chunks(m/num_vars).take(num_vars).map(|chunk| chunk.to_vec()).collect_vec(); 
		
		// add gate polynomial with input preprocessors f(P_0(x, y),..,P_n(x, y)) = P_0(x, y) + P_1(x, y) + .. + P_n(x, y)
		// consider fan in 2 so f(P_0(x, y), P_1(x, y)) = P_0(x, y) + P_1(x, y)
		// we can model input preprocessors as P_0(x, y) = x*y and P_1(x, y) = x*y^3
		let p0_terms: Vec<(usize, usize)> = vec![(0, 1), (1, 1)];
		let p1_terms: Vec<(usize, usize)> = vec![(0, 1), (1, 2)];
		let mut p1_values = vec![Fr::ZERO; 16];
		let mut p0_values = vec![Fr::ZERO; 16];
        let mut sum = vec![Fr::ZERO; 16];
		for i in 0..4 { // m/num_vars
			for j in 0..4 {
			  let fx = domain[0][i];
			  let fy = domain[1][j];
			  p0_values[i*4+j] = fx*fy;
			  p1_values[i*4+j] = fx*fy*fy;
              sum[i*4+j] = p0_values[i*4+j] + p1_values[i*4+j]; 
			}
		}

		let input_polys = 
		[
			MultivariatePolynomial::new(vec![p0_terms.clone()], vec![Fr::ONE], 2, 2, m).unwrap(), 
			MultivariatePolynomial::new(vec![p1_terms.clone()], vec![Fr::ONE], 2, 3, m).unwrap()
		];
        let output_poly = MultivariatePolynomial::new(vec![p0_terms, p1_terms], vec![Fr::ONE, Fr::ONE], 2, 3, m).unwrap();

        let c = {
            let w1 = Wire::new(AnyGate::new_identity(), vec![], 1);
            let w2 = Wire::new(AnyGate::new_identity(), vec![], 1);
            vec![w1.clone(), w2.clone(), Wire::new(AnyGate::new_add(), vec![w1, w2], 6)]
        };

        let mut assignment = HashMap::new();
        assignment.insert(c[0].clone(), input_polys[0].clone());
        assignment.insert(c[1].clone(), input_polys[1].clone());

        let spec = Spec::<Fr, T, RATE>::new(R_F, R_P); 
		let mut prover_transcript = PoseidonNativeTranscript::<Fr, io::Cursor<Vec<u8>>>::new(spec.clone());
		// each layer has 4*4 = 16 gates => each variable can have domain size, |H| = 4
		// degree of each variable is at most, |H| - 1 = 3

        let proof = gkr_prove(c.clone(), &assignment, &mut prover_transcript);
        assert!(proof.is_ok());
        let proof_bytes = prover_transcript.into_proof();

        let mut verifier_transcript = PoseidonNativeTranscript::<Fr, io::Cursor<Vec<u8>>>::from_proof(spec, &proof_bytes);
        gkr_verify(c, assignment, &mut verifier_transcript, &proof.unwrap()).unwrap();
    }
}