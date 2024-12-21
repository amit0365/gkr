use std::cmp::max_by;
use std::collections::HashMap;
use std::marker::PhantomData;
use std::hash::Hash;
use itertools::Itertools;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::halo2curves::ff::PrimeField;

use crate::poly::multivariate::{eq_poly_fix_first_var_univariate, eq_poly_univariate, lagrange_bases, make_subgroup_elements, MultivariatePolynomial};
use crate::poly::univariate::{CoefficientBasis, UnivariatePolynomial};
use crate::util::transcript::{FieldTranscriptRead, FieldTranscriptWrite};
use crate::Error;

//pub const M: u64 = 20;
use super::sumcheck::{sumcheck_prove, sumcheck_verify, Claims, LazyClaims, SumCheckProof};

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
pub struct MulGate;
// Implementations of GateInstructions<F> for each gate

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AnyGate<F: Field> {
    AddGate(AddGate<F>),
    // MulGate(MulGate),
    // Other gate variants
}

impl<F: Field> GateInstructions<F> for AnyGate<F> {
    fn evaluate(&self, inputs: &[F]) -> F {
        match self {
            AnyGate::AddGate(gate) => gate.evaluate(inputs),
            // AnyGate::MulGate(gate) => gate.evaluate(inputs),
            // Other variants
        }
    }

    fn degree(&self) -> usize {
        match self {
            AnyGate::AddGate(gate) => gate.degree(),
            // AnyGate::MulGate(gate) => gate.degree(),
            // Other variants
        }
    }   

    fn nb_inputs(&self) -> usize {
        match self {
            AnyGate::AddGate(gate) => gate.nb_inputs(),
            // AnyGate::MulGate(gate) => gate.nb_inputs(),
            // Other variants
        }
    }

    fn nb_outputs(&self) -> usize {
        match self {
            AnyGate::AddGate(gate) => gate.nb_outputs(),
            // AnyGate::MulGate(gate) => gate.nb_outputs(),
            // Other variants
        }
    }

    fn name(&self) -> String {
        match self {
            AnyGate::AddGate(gate) => gate.name(),
            // AnyGate::MulGate(gate) => gate.name(),
            // Other variants
        }
    }
}


pub trait GateInstructions<F: Field> {
    fn evaluate(&self, input: &[F]) -> F;
    fn degree(&self) -> usize;
    fn nb_inputs(&self) -> usize;
    fn nb_outputs(&self) -> usize;
    fn name(&self) -> String;
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Wire<F: Field + Hash> {
    gate: AnyGate<F>,
    inputs: Vec<Wire<F>>,
    nb_unique_outputs: usize,
    _marker: PhantomData<F>,
}

pub type GKRCircuit<F> = Vec<Wire<F>>;

impl<F: Field + Hash> Wire<F> {
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
type WireAssignment<F> = HashMap<Wire<F>, MultivariatePolynomial<F, CoefficientBasis>>;

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
    fn verify_final_eval(&mut self, r: &[F], combination_coeff: F, purported_value: F, proof: &[F]) -> Result<(), Error> {
        let input_evaluations_no_redundancy = proof;

        // // the eq terms
        // let num_claims = self.evaluation_points.len();
        // let mut evaluation = eval_eq(&self.evaluation_points[num_claims - 1], r, M);
        // for i in (0..num_claims - 1).rev() {
        //     evaluation.mul_assign(combination_coeff);
        //     let eq = eval_eq(&self.evaluation_points[i], r, M);
        //     evaluation.add_assign(eq);
        // }

        // // the g(...) term
        // let gate_evaluation = if self.wire.is_input() {
        //     self.manager.assignment[&self.wire].evaluate(r)
        // } else {
        //     let mut input_evaluations = vec![F::default(); self.wire.inputs.len()];
        //     let mut indexes_in_proof = HashMap::new();

        //     let mut proof_i = 0;
        //     for (in_i, input) in self.wire.inputs.iter().enumerate() {
        //         let index_in_proof = if let Some(&index) = indexes_in_proof.get(&(input.clone())) {
        //             index
        //         } else {
        //             let index = proof_i;
        //             indexes_in_proof.insert(input, index);

        //             // defer verification, store new claim
        //             self.manager.add(input.clone(), r, input_evaluations_no_redundancy[index]);
        //             proof_i += 1;
        //             index
        //         };
        //         input_evaluations[in_i] = input_evaluations_no_redundancy[index_in_proof];
        //     }
        //     if proof_i != input_evaluations_no_redundancy.len() {
        //         return Err(Error::InvalidSumcheck(format!("{} input wire evaluations given, {} expected", input_evaluations_no_redundancy.len(), proof_i)));
        //     }
        //     self.wire.gate.evaluate(&input_evaluations)
        // };

        // evaluation.mul_assign(gate_evaluation);

        // assert_eq!(evaluation, purported_value);
        Ok(())
    }

    fn claims_num(&self) -> usize {
        self.evaluation_points.len()
    }

    fn vars_num(&self) -> usize {
        self.evaluation_points[0].len()
    }

    fn combined_sum(&self, a: F) -> F {
        //eval_polynomial(&self.claimed_evaluations, a)
        todo!()
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
        let num_evals = 1 + self.eq.len(); // guaranteed to be no smaller than the actual deg(g_j)
        let points = make_subgroup_elements::<F>(num_evals as u64);
        points.iter()
        .zip(&eq_evals_univariate)
        .map(|(p, eq)| *eq * self.wire.gate.evaluate(&input_preprocessors.iter().map(|prep| prep.evaluate(p)).collect_vec()))
        .collect()
    }
}

impl<F: PrimeField + Hash> Claims<F> for EqTimesGateEvalSumcheckClaims<F> {
    fn combine_and_first_poly(&mut self, domain: &[&[F]], combination_coeff: F) -> Vec<F> { //eq combining algo    
        let vars_num = self.vars_num();
        let eq_length = 1 << vars_num;
        let claims_num = self.claims_num();
    
        // initialize the eq tables
        let eq_acc = (1..claims_num).fold(vec![vec![F::ZERO; eq_length]; claims_num], |mut acc, k| {
            let eq = lagrange_bases(&self.domain.iter().map(|v| v.as_slice()).collect_vec(), &self.evaluation_points[k]);
			acc[k].iter_mut().zip(&eq[k]).for_each(|(acc, eq)| *acc = *eq * combination_coeff.pow([k as u64]));
			acc
        });
		self.eq = eq_acc.clone();
    
        // from this point on the claim is a rather simple one: g = E(h) × R_v (P_u0(h), ...) 
        // where E and the P_u are multilinear and R_v is of low-degree
		let mut input_preprocessors = Vec::new();
        for preprocessor in &mut self.input_preprocessors {
            input_preprocessors.push(preprocessor.univariate_poly_first_summed(domain));
        }
		let eq_evals_univariate = eq_poly_univariate(&eq_acc); 
        self.compute_gj(input_preprocessors, eq_evals_univariate)
    }

    fn next(&mut self, domain: &[&[F]], element: F) -> Vec<F> {
		let mut input_preprocessors = Vec::new();
        for preprocessor in &mut self.input_preprocessors {
            input_preprocessors.push(preprocessor.univariate_poly_fix_var(domain, &element));
        }
        let eq = eq_poly_fix_first_var_univariate(&self.domain[1], &self.eq, &element); // domain for second variable
        self.compute_gj(input_preprocessors, eq)
    }

    fn prove_final_eval(&self, r: &[F]) -> Vec<F> {
        todo!()
    }

    fn domain(&self) -> Vec<Vec<F>> {
        self.domain.clone()
    }

    fn claims_num(&self) -> usize {
        self.evaluation_points.len()
    }

    fn vars_num(&self) -> usize {
        self.evaluation_points[0].len()
    }

    fn degree(&self) -> usize {
        1 + self.wire.gate.degree()
    }

}

// func (c *eqTimesGateEvalSumcheckClaims) Combine(combinationCoeff *big.Int) sumcheck.NativePolynomial {
// 	varsNum := c.NbVars()
// 	eqLength := 1 << varsNum
// 	claimsNum := c.NbClaims()

// 	// initialize the eq tables
// 	c.eq = make(sumcheck.NativeMultilinear, eqLength)
// 	for i := 0; i < eqLength; i++ {
// 		c.eq[i] = new(big.Int)
// 	}
// 	c.eq[0] = c.engine.One()
// 	sumcheck.Eq(c.engine, c.eq, sumcheck.ReferenceBigIntSlice(c.evaluationPoints[0]))

// 	newEq := make(sumcheck.NativeMultilinear, eqLength)
// 	for i := 0; i < eqLength; i++ {
// 		newEq[i] = new(big.Int)
// 	}
// 	aI := new(big.Int).Set(combinationCoeff)

// 	for k := 1; k < claimsNum; k++ { // TODO: parallelizable?
// 		// define eq_k = aᵏ eq(x_k1, ..., x_kn, *, ..., *) where x_ki are the evaluation points
// 		newEq[0].Set(aI)
// 		sumcheck.EqAcc(c.engine, c.eq, newEq, sumcheck.ReferenceBigIntSlice(c.evaluationPoints[k]))
// 		if k+1 < claimsNum {
// 			aI.Mul(aI, combinationCoeff)
// 		}
// 	}

// 	// from this point on the claim is a rather simple one: g = E(h) × R_v (P_u0(h), ...) where E and the P_u are multilinear and R_v is of low-degree
// 	return c.computeGJ()
// }

// func (c *eqTimesGateEvalSumcheckClaims) ProverFinalEval(r []*big.Int) sumcheck.NativeEvaluationProof {

// 	//defer the proof, return list of claims
// 	evaluations := make([]big.Int, 0, len(c.wire.Inputs))
// 	noMoreClaimsAllowed := make(map[*Wire]struct{}, len(c.inputPreprocessors))
// 	noMoreClaimsAllowed[c.wire] = struct{}{}

// 	for inI, in := range c.wire.Inputs {
// 		puI := c.inputPreprocessors[inI]
// 		if _, found := noMoreClaimsAllowed[in]; !found {
// 			noMoreClaimsAllowed[in] = struct{}{}
// 			sumcheck.Fold(c.engine, puI, r[len(r)-1])
// 			puI0 := new(big.Int).Set(puI[0])
// 			c.manager.add(in, sumcheck.DereferenceBigIntSlice(r), *puI0)
// 			evaluations = append(evaluations, *puI0)
// 		}
// 	}

// 	return evaluations
// }

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

        for wire in c {
            claims.claims_map.insert(wire.clone(), EqTimesGateEvalSumcheckLazyClaims {
                wire: wire.clone(),
                domain: Vec::new(),
                evaluation_points: Vec::with_capacity(wire.nb_claims()),
                claimed_evaluations: vec![F::default(); wire.nb_claims()],
                manager: claims.clone(),
            });
        }
        claims
    }

    fn add(&mut self, wire: &Wire<F>, evaluation_point: &[F], evaluation: F) {
        let claim = self.claims_map.get_mut(wire).unwrap();
        let i = claim.evaluation_points.len();
        claim.claimed_evaluations[i] = evaluation;
        claim.evaluation_points.push(evaluation_point.to_vec());
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
    let num_vars = assignment[&c[0]].num_vars; //num_vars should be the same for all wires
	let first_challenge = transcript.squeeze_challenges(num_vars);

	for i in (0..c.len()).rev() {
		let wire = c[i].clone();
		if wire.is_output() {
			claims.add(&wire, &first_challenge, assignment[&wire].evaluate(&first_challenge))
		}

		let claim = claims.get_claim(&wire);
		if wire.no_proof() { // input wires with one claim only
			proof[i] = SumCheckProof::<F>::new();
		} else {
            sumcheck_prove(claim, transcript)?;
		}
		// the verifier checks a single claim about input wires itself
		claims.delete_claim(wire);
	}

	Ok(proof)
}

// Verify the consistency of the claimed output with the claimed input
// Unlike in Prove, the assignment argument need not be complete
fn gkr_verify<F: PrimeField + Hash>(c: GKRCircuit<F>, assignment: WireAssignment<F>, transcript: &mut impl FieldTranscriptRead<F>, proof: &Proof<F>) -> Result<(), Error> {
	let mut claims = ClaimsManager::new(&c, &assignment);
    let num_vars = assignment[&c[0]].num_vars; //num_vars should be the same for all wires
	let first_challenge = transcript.squeeze_challenges(num_vars);

	for i in (0..c.len()).rev() {
		let wire = c[i].clone();
		if wire.is_output() {
			claims.add(&wire, &first_challenge, assignment[&wire].evaluate(&first_challenge))
		}

		let proof_i = &proof[i];
		let final_eval_proof = proof_i.final_eval_proof.clone();
		let claim = claims.get_lazy_claim(&wire);
		if wire.no_proof() { // input wires with one claim only
			// make sure the proof is empty
			if final_eval_proof.is_empty() || proof_i.partial_sum_polys.is_empty() {
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
    // #[test]
    // fn test_gkr_prove_and_verify() {
    //     let c = vec![];
    //     let assignment = HashMap::new();
    //     let transcript = vec![];
    //     let proof = vec![];
    //     gkr_prove(c, assignment, transcript).unwrap();
    // }
}