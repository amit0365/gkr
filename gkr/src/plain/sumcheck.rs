use std::hash::Hash;
use itertools::Itertools;
use halo2_proofs::{arithmetic::{eval_polynomial, lagrange_interpolate, Field}, halo2curves::ff::PrimeField};
use crate::{poly::{multivariate::{eq_poly_fix_first_var_univariate, eq_poly_univariate, lagrange_bases, lagrange_pi_eval_verifier, make_subgroup_elements, power_matrix_generator, MultivariatePolynomial}, univariate::{CoefficientBasis, UnivariatePolynomial}}, util::transcript::{FieldTranscriptRead, FieldTranscriptWrite}, Error};
use super::gkr::{AddGate, AnyGate};
use crate::plain::gkr::GateInstructions;

// Claims to a multi-sumcheck statement. i.e. one of the form ∑_{0≤i<2ⁿ} fⱼ(i) = cⱼ for 1 ≤ j ≤ m.
// Later evolving into a claim of the form gⱼ = ∑_{0≤i<2ⁿ⁻ʲ} g(r₁, r₂, ..., rⱼ₋₁, Xⱼ, i...)
pub trait Claims<F: Field> {
	fn combine_and_first_poly(&mut self, domain: &[&[F]], a: F) -> Vec<F>;        // Combine into the 0ᵗʰ sumcheck subclaim. Create g := ∑_{1≤j≤m} aʲ⁻¹fⱼ for which now we seek to prove ∑_{0≤i<2ⁿ} g(i) = c := ∑_{1≤j≤m} aʲ⁻¹cⱼ. Return g₁.
	fn next(&mut self, domain: &[&[F]], element: F, var_idx: usize) -> Vec<F>;          // Return the evaluations gⱼ(k) for 1 ≤ k < degⱼ(g). Update the claim to gⱼ₊₁ for the input value as rⱼ
	fn vars_num(&self) -> usize;                	// number of variables
	fn degree(&self) -> usize;                 		// degree of the j'th claim
	fn claims_num(&self) -> usize;            		// number of claims
	fn domain(&self) -> Vec<Vec<F>>;		 		// domain of the polynomial wrt each variable
	fn full_domain(&self) -> Vec<F>;				// full domain of the polynomial, for all x in H
	fn claimed_sum(&self) -> F;
	fn input_preprocessors(&self) -> Vec<MultivariatePolynomial<F, CoefficientBasis>>;
	fn eq(&self) -> Vec<Vec<F>>;
	fn gate(&self) -> AnyGate<F>;
	fn prove_final_eval(&self, r: &[F]) -> Vec<F>;  // in case it is difficult for the verifier to compute g(r₁, ..., rₙ) on its own, the prover can provide the value and a proof
}

// LazyClaims is the Claims data structure on the verifier side. It is "lazy" in that it has to compute fewer things.
pub trait LazyClaims<F: Field> {
	fn claimed_sum(&self) -> F;
	fn claims_num(&self) -> usize;
	fn vars_num(&self) -> usize;
	fn combined_sum(&self, round_poly_evaluation: &[F], var_idx: usize) -> F; // Interploate input preprocessors on the full domain, H and then evaluate and sum them in their respective domains. i.e. G1, G2 in paper
	fn degree(&self) -> usize;    			// Degree of the ith claim
	fn domain(&self) -> Vec<Vec<F>>;        // domain of the polynomial wrt each variable
	fn full_domain(&self) -> Vec<F>;				// full domain of the polynomial, for all x in H
	fn input_preprocessors(&self) -> Vec<MultivariatePolynomial<F, CoefficientBasis>>;
	fn gate(&self) -> AnyGate<F>;
	fn verify_final_eval(&mut self, r: &[F], combination_coeff: F, purported_value: F, proof: &[F]) -> Result<(), Error>;
}

// Proof of a multi-sumcheck statement.
#[derive(Debug, Clone)]
pub struct SumCheckProof<F: Field> {
	pub partial_sum_polys: Vec<Vec<F>>,
	pub final_eval_proof: Vec<F>, //in case it is difficult for the verifier to compute gate polynomial g(r₁, ..., rₙ) on its own, the prover can provide the value and a proof
}

impl<F: Field> SumCheckProof<F> {
	pub fn new() -> Self {
		SumCheckProof {
			partial_sum_polys: Vec::new(),
			final_eval_proof: Vec::new(),
		}
	}
}

// Subprotocol 6.2 in paper
// Prove create a non-interactive sumcheck proof
pub fn sumcheck_prove<F: PrimeField + Hash>(
    mut claims: impl Claims<F>, 
    transcript: &mut impl FieldTranscriptWrite<F>,
) -> Result<SumCheckProof<F>, Error> {

	let mut proof = SumCheckProof::new();
	let mut combination_coeff: F = F::ZERO;
	if claims.claims_num() >= 2 {
        combination_coeff = transcript.squeeze_challenge();
	}

	let vars_num = claims.vars_num();
	let m = claims.full_domain().len();
	let domain_vec = claims.domain();
	let full_domain_vec = vec![claims.full_domain(); vars_num];
	let domain = domain_vec.iter().map(|v| v.as_slice()).collect_vec();
	let full_domain = full_domain_vec.iter().map(|v| v.as_slice()).collect_vec();

	proof.partial_sum_polys = vec![vec![]; vars_num];
	proof.partial_sum_polys[0] = claims.combine_and_first_poly(&domain, combination_coeff); // first partial sum poly
	let mut challenges = vec![F::ZERO; vars_num - 1];
	for (j, challenge) in challenges.iter_mut().enumerate() {
		transcript.write_field_elements(&proof.partial_sum_polys[j])?;
		*challenge = transcript.squeeze_challenge();
		proof.partial_sum_polys[j+1] = claims.next(&domain, *challenge, j + 2);
	}
	transcript.write_field_elements(&proof.partial_sum_polys[vars_num-1])?;
	challenges.push(transcript.squeeze_challenge()); // last challenge
	// directly use f_2(y) and evaluate at y = b, rather than interpolating f_2(y) from f_2(w) and then evaluating at y = b

	let t_star_poly = lagrange_interpolate(full_domain[vars_num-1], &proof.partial_sum_polys[vars_num-1]); 
	let t_star = eval_polynomial(&t_star_poly, challenges[vars_num-1]);
	transcript.write_field_element(&t_star)?;
	
	// Subprotocol 6.1 prover side in paper
	// start pi_eval
	// prover computes lagrange_bases and power vector for each variable
	for (j, challenge) in challenges.iter().enumerate() {
		let lagrange_bases = lagrange_bases::<F>(&[&full_domain[j]], &[*challenge],); 
		assert_eq!(lagrange_bases[0].len(), m);
		let power_vector = power_matrix_generator(&[*challenge], m as u64);
		assert_eq!(power_vector[0].len(), ((64 - (m).leading_zeros() - 1) + 1) as usize); // length k*(logm + 1), k = 1 for bivariate sumcheck. can optimize this to k*logm
		transcript.write_field_elements(&lagrange_bases[0])?;
		transcript.write_field_elements(&power_vector[0])?; 
	}

	// not used in this implementation of bivariate sumcheck but we keep it for future use
	// proof.final_eval_proof = claims.prove_final_eval(&challenges); 

	Ok(proof)
}

pub fn sumcheck_verify<F: PrimeField + Hash>(
    claims: &mut impl LazyClaims<F>, 
    transcript: &mut impl FieldTranscriptRead<F>,
) -> Result<(), Error> {

	let vars_num = claims.vars_num();
	let domain_vec = claims.domain();
	let domain_len = claims.full_domain().len(); //m
	let full_domain = vec![claims.full_domain(); vars_num];
	let domain = domain_vec.iter().map(|v| v.as_slice()).collect_vec();

	let mut round_poly_evaluation = vec![vec![F::ZERO; domain_len]; claims.vars_num()];
	if claims.claims_num() >= 2 {
        let _ = transcript.squeeze_challenge();
	}

	let mut challenges = vec![F::ZERO; vars_num]; 
	let mut g = vec![vec![F::ZERO; domain_len]; vars_num]; // At the end of iteration j, gJ = ∑_{i < 2ⁿ⁻ʲ⁻¹} g(X₁, ..., Xⱼ₊₁, i...)
	for j in 0..claims.vars_num() - 1 {
		round_poly_evaluation[j] = transcript.read_field_elements(domain_len)?;
		g[j].copy_from_slice(&round_poly_evaluation[j]); // g check deferred to pi_eval

		// Prepare for the next iteration
		challenges[j] = transcript.squeeze_challenge();
    }

	round_poly_evaluation[vars_num-1] = transcript.read_field_elements(domain_len)?;
	g[vars_num-1].copy_from_slice(&round_poly_evaluation[vars_num-1]);
	challenges[vars_num-1] = transcript.squeeze_challenge();
	let t_star = transcript.read_field_element()?;

	// Subprotocol 6.1 verifier side in paper
	// start pi_eval
	let mut evaluations = vec![F::ZERO; vars_num + 1];
	evaluations[0] = claims.claimed_sum(); // T
	for j in 0..vars_num {
		// partitioning the g[j], round_poly_evaluation into vars_num partitions and summing them up, i.e. G_1, G_2 in paper
		let sum = claims.combined_sum(&g[j], j);
		assert_eq!(evaluations[j], sum); // jth check, so total 2 checks for bivariate sumcheck

		// length klogm, k = 1 for bivariate sumcheck, reads lagrange_bases
		let log_m = 64 - (domain_len).leading_zeros() - 1;
		let lagrange_bases = transcript.read_field_elements(domain_len)?;
		let power_vector = transcript.read_field_elements((log_m + 1) as usize)?; 
		evaluations[j+1] = lagrange_pi_eval_verifier(&[power_vector], &g[j], &[lagrange_bases], &[&full_domain[j]], &[challenges[j]]);
	}

	assert_eq!(t_star, *evaluations.last().unwrap()); //third check
	let input_evals = claims.input_preprocessors().iter().map(|prep| prep.evaluate(&challenges)).collect_vec();
	let gate_eval = claims.gate().evaluate(&input_evals);
	assert_eq!(t_star, gate_eval); //fourth check

	// can defer evaluating gate at challenges to the prover, if costly for the fourth and last check
	// claims.verify_final_eval(&r, combination_coeff, gjr, &[])
	Ok(())

}

#[derive(Clone)]
pub struct SingleClaim<F: PrimeField> {
	input_preprocessors: Vec<MultivariatePolynomial<F, CoefficientBasis>>,
	// vector of eq polys, where eq are the lagrange basis polynomials evaluated at the j'th evaluation point for all x_j
	eq: Vec<Vec<F>>, 
	claimed_sum: F,
	evaluation_points: Vec<Vec<F>>, // evaluation points for each claim with respect to each variable as the inner vector
	domain: Vec<Vec<F>>,
	gate: AnyGate<F>,
}

impl<F: PrimeField + Hash> SingleClaim<F> {
    pub fn compute_gj(&self, 
		input_preprocessors: Vec<UnivariatePolynomial<F, CoefficientBasis>>, 
		eq_evals_univariate: Vec<F>,
		eq_acc: Vec<Vec<F>>,
		var_idx: usize
	) -> Vec<F> { // can use fft here
		self.full_domain()
		.iter()
		.zip(&eq_evals_univariate)
		.map(|(p, eq)| self.gate.evaluate(&input_preprocessors.iter().map(|prep| prep.evaluate(p)).collect_vec()))
		.collect_vec()
    }

	pub fn new(
		input_preprocessors: Vec<MultivariatePolynomial<F, CoefficientBasis>>, 
		evaluation_points: Vec<Vec<F>>, 
		domain: Vec<Vec<F>>, 
		gate: AnyGate<F>,
		claimed_sum: F
	) -> Self {
		SingleClaim {
			input_preprocessors,
			eq: Vec::new(),
			evaluation_points,
			domain,
			gate,
			claimed_sum,
		}
	}
	
}

impl<F: PrimeField + Hash> Claims<F> for SingleClaim<F> {
	fn eq(&self) -> Vec<Vec<F>> {
		self.eq.clone()
	}

	fn claimed_sum(&self) -> F {
		self.claimed_sum
	}

	fn input_preprocessors(&self) -> Vec<MultivariatePolynomial<F, CoefficientBasis>> {
		self.input_preprocessors.clone()
	}

	fn gate(&self) -> AnyGate<F> {
		self.gate.clone()
	}

	fn prove_final_eval(&self, r: &[F]) -> Vec<F> {
		unimplemented!()
	}

	fn vars_num(&self) -> usize {
		self.input_preprocessors[0].num_vars
	}

	fn claims_num(&self) -> usize {
		1
	}

	fn domain(&self) -> Vec<Vec<F>> {
		self.domain.clone()
	}

	fn full_domain(&self) -> Vec<F> {
		self.domain.iter().flatten().cloned().collect_vec()
	}

	fn combine_and_first_poly(&mut self, domain: &[&[F]], a: F) -> Vec<F> {
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
        self.compute_gj(input_preprocessors, eq_evals_univariate, eq_acc, 1) // summing over the second variable
	}

	fn next(&mut self, domain: &[&[F]], element: F, var_idx: usize) -> Vec<F> {
		let mut input_preprocessors = Vec::new();
        for preprocessor in &mut self.input_preprocessors {
            input_preprocessors.push(preprocessor.univariate_poly_fix_var(domain, &element));
        }
        let eq = eq_poly_fix_first_var_univariate(&self.full_domain(), &self.eq, &element); 
        self.compute_gj(input_preprocessors, eq, self.eq.clone(), var_idx) 
	}

	fn degree(&self) -> usize {
		self.input_preprocessors.iter().map(|preprocessor| preprocessor.degree()).max().unwrap()
	}

}

pub struct SingleClaimLazyClaim<F: PrimeField> {
	gate: AnyGate<F>,
	input_preprocessors: Vec<MultivariatePolynomial<F, CoefficientBasis>>,
	claims_num: usize,
	vars_num: usize,
	domain: Vec<Vec<F>>,
	degree: usize,
	claimed_sum: F,
}

impl<F: PrimeField + Hash> SingleClaimLazyClaim<F> {
	pub fn from_claim(claims: impl Claims<F>) -> Self {
		SingleClaimLazyClaim {
			input_preprocessors: claims.input_preprocessors(),
			gate: claims.gate(),
			claims_num: claims.claims_num(),
			vars_num: claims.vars_num(),
			domain: claims.domain(),
			degree: claims.degree(),
			claimed_sum: claims.claimed_sum(),
		}
	}
}

impl<F: PrimeField + Hash> LazyClaims<F> for SingleClaimLazyClaim<F> {
	fn claimed_sum(&self) -> F {
		self.claimed_sum
	}

	fn input_preprocessors(&self) -> Vec<MultivariatePolynomial<F, CoefficientBasis>> {
		self.input_preprocessors.clone()
	}

	fn gate(&self) -> AnyGate<F> {
		self.gate.clone()
	}

	fn claims_num(&self) -> usize {
		self.claims_num
	}

	fn vars_num(&self) -> usize {
		self.vars_num
	}

	fn combined_sum(&self, poly_evaluation: &[F], var_idx: usize) -> F {
		// already have evals over the full domain, so we can just sum over respective domain
		// note that full domain is distributed over variables respectively
		let partition = poly_evaluation.len()/self.vars_num;
		poly_evaluation[(var_idx)*partition..(var_idx+1)*partition].iter().sum::<F>()

		// let domain = self.full_domain(); // evaluations are on the full domain, m = |H|
		// let var_domain = self.domain[var_idx].clone();
		// let poly = UnivariatePolynomial::new(lagrange_interpolate(&domain, poly_evaluation));
		// var_domain.iter().map(|p| poly.evaluate(p)).sum::<F>()
	}

	fn degree(&self) -> usize {
		self.degree
	}

	fn domain(&self) -> Vec<Vec<F>> {
		self.domain.clone()
	}

	fn full_domain(&self) -> Vec<F> {
		self.domain.iter().flatten().cloned().collect_vec()
	}

	fn verify_final_eval(&mut self, r: &[F], combination_coeff: F, purported_value: F, proof: &[F]) -> Result<(), Error> {
		unimplemented!()
	}

}

#[cfg(test)]
mod tests {
	use std::io;
	use std::io::Cursor;
	use super::*;
	use ethereum_types::U256;
	use poseidon::Spec;
	use halo2_proofs::halo2curves::bn256::Fr;
	use crate::plain::gkr::EqTimesGateEvalSumcheckLazyClaims;
	use crate::plain::gkr::IdentityGate;
	use crate::util::transcript::InMemoryTranscript;
	use crate::util::transcript::PoseidonNativeTranscript;

	const T: usize = 4;
	const RATE: usize = 3;
	const R_F: usize = 8;
	const R_P: usize = 56;

	#[test]
	fn test_sumcheck_identity_gate() {
		let spec = Spec::<Fr, T, RATE>::new(R_F, R_P); 
		let mut prover_transcript = PoseidonNativeTranscript::<Fr, io::Cursor<Vec<u8>>>::new(spec.clone());
		// each layer has 4*4 = 16 gates => each variable can have domain size, |H| = 4
		// degree of each variable is at most, |H| - 1 = 3

		let m: usize = 8;
		let num_vars = 2;
		let points = make_subgroup_elements::<Fr>(m as u64);
		let domain = points.chunks(m/num_vars).take(num_vars).map(|chunk| chunk.to_vec()).collect_vec(); //points.len()/num_vars
		
		// identity gate polynomial with input preprocessors f(P_0(x, y)) = P_0(x, y)
		// consider fan in 1 so f(P_0(x, y)) = P_0(x, y)
		// we can model input preprocessors as P_0(x, y) = x*y
		let p0_terms: Vec<(usize, usize)> = vec![(0, 1), (1, 1)];
		let mut p0_values = vec![Fr::ZERO; m*m];
		for i in 0..m/num_vars { 
			for j in 0..m/num_vars {
			  let fx = domain[0][i];
			  let fy = domain[1][j];
			  p0_values[i*m+j] = fx*fy;
			}
		}

		let claimed_sum = p0_values.iter().sum::<Fr>();
		let input_preprocessors = vec![MultivariatePolynomial::new(vec![p0_terms], vec![Fr::ONE], 2, 2, m).unwrap()];
		// evaluate the gate polynomial at Fr(5) for the first variable and Fr(9) for the second variable
		let evaluation_points = vec![vec![Fr::from(5), Fr::from(9)]];
		let claims = SingleClaim::new(input_preprocessors, evaluation_points, domain, AnyGate::new_identity(), claimed_sum);
		let proof = sumcheck_prove(claims.clone(), &mut prover_transcript);
		assert!(proof.is_ok());

		let proof_bytes = prover_transcript.into_proof();
		let mut verifier_transcript = PoseidonNativeTranscript::<Fr, Cursor<Vec<u8>>>::from_proof(spec, &proof_bytes);
		let mut lazy_claims = SingleClaimLazyClaim::from_claim(claims);
		sumcheck_verify(&mut lazy_claims, &mut verifier_transcript).unwrap();
	}

	#[test]
	fn test_sumcheck_add_gate() {
		let spec = Spec::<Fr, T, RATE>::new(R_F, R_P); 
		let mut prover_transcript = PoseidonNativeTranscript::<Fr, io::Cursor<Vec<u8>>>::new(spec.clone());
		// each layer has 4*4 = 16 gates => each variable can have domain size, |H| = 4
		// degree of each variable is at most, |H| - 1 = 3

		let m: usize = 8;
		let num_vars = 2;
		let points = make_subgroup_elements::<Fr>(m as u64);
		let domain = points.chunks(m/num_vars).take(num_vars).map(|chunk| chunk.to_vec()).collect_vec(); //points.len()/num_vars
		
		// add gate polynomial with input preprocessors f(P_0(x, y),..,P_n(x, y)) = P_0(x, y) + P_1(x, y) + .. + P_n(x, y)
		// consider fan in 2 so f(P_0(x, y), P_1(x, y)) = P_0(x, y) + P_1(x, y)
		// we can model input preprocessors as P_0(x, y) = x*y and P_1(x, y) = x*y^2
		let p0_terms: Vec<(usize, usize)> = vec![(0, 1), (1, 1)];
		let p1_terms: Vec<(usize, usize)> = vec![(0, 1), (1, 2)];
		let mut p1_values = vec![Fr::ZERO; m*m];
		let mut p0_values = vec![Fr::ZERO; m*m];
		for i in 0..4 { // m/num_vars
			for j in 0..4 {
			  let fx = domain[0][i];
			  let fy = domain[1][j];
			  p0_values[i*m+j] = fx*fy;
			  p1_values[i*m+j] = fx*fy*fy;
			}
		}
		let input_preprocessors = 
		vec![
			MultivariatePolynomial::new(vec![p0_terms], vec![Fr::ONE], 2, 2, m).unwrap(), 
			MultivariatePolynomial::new(vec![p1_terms], vec![Fr::ONE], 2, 3, m).unwrap()
		];

		let claimed_sum = p0_values.iter().sum::<Fr>() + p1_values.iter().sum::<Fr>();
		//evaluate the gate polynomial at Fr(5) for the first variable and Fr(9) for the second variable
		let evaluation_points = vec![vec![Fr::from(5), Fr::from(9)]];
		let claims = SingleClaim::new(input_preprocessors, evaluation_points, domain, AnyGate::new_add(), claimed_sum);
		let proof = sumcheck_prove(claims.clone(), &mut prover_transcript);
		assert!(proof.is_ok());
		let proof_bytes = prover_transcript.into_proof();

		let mut verifier_transcript = PoseidonNativeTranscript::<Fr, Cursor<Vec<u8>>>::from_proof(spec, &proof_bytes);
		let mut lazy_claims = SingleClaimLazyClaim::from_claim(claims);
		sumcheck_verify(&mut lazy_claims, &mut verifier_transcript).unwrap();
	}

}