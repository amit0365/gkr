
use std::hash::Hash;
use itertools::Itertools;
use halo2_proofs::{arithmetic::{eval_polynomial, lagrange_interpolate, Field}, halo2curves::ff::PrimeField};
use crate::{poly::{multivariate::{eq_poly_first_summed, init_eq, lagrange_bases, lagrange_bases_poly, lagrange_pi_eval_verifier, make_subgroup_elements, power_matrix_generator, MultivariatePolynomial}, univariate::{CoefficientBasis, UnivariatePolynomial}, Polynomial, SimplePolynomial}, util::{arithmetic::powers, transcript::{FieldTranscriptRead, FieldTranscriptWrite, TranscriptWrite}}, Error};

use super::gkr::AddGate;

// Claims to a multi-sumcheck statement. i.e. one of the form ∑_{0≤i<2ⁿ} fⱼ(i) = cⱼ for 1 ≤ j ≤ m.
// Later evolving into a claim of the form gⱼ = ∑_{0≤i<2ⁿ⁻ʲ} g(r₁, r₂, ..., rⱼ₋₁, Xⱼ, i...)
pub trait Claims<F: Field> {
	fn combine_and_first_poly(&mut self, a: F) -> Vec<F>;        // Combine into the 0ᵗʰ sumcheck subclaim. Create g := ∑_{1≤j≤m} aʲ⁻¹fⱼ for which now we seek to prove ∑_{0≤i<2ⁿ} g(i) = c := ∑_{1≤j≤m} aʲ⁻¹cⱼ. Return g₁.
	fn next(&mut self, k: F) -> Vec<F>;          // Return the evaluations gⱼ(k) for 1 ≤ k < degⱼ(g). Update the claim to gⱼ₊₁ for the input value as rⱼ
	fn vars_num(&self) -> usize;                // number of variables
	fn degree(&self) -> usize;                 // degree of the j'th claim
	fn claims_num(&self) -> usize;            // number of claims
	fn domain(&self) -> Vec<&[F]>;		 // domain of the polynomial
	fn prove_final_eval(&self, r: &[F]) -> Vec<F>; // in case it is difficult for the verifier to compute g(r₁, ..., rₙ) on its own, the prover can provide the value and a proof
}

// LazyClaims is the Claims data structure on the verifier side. It is "lazy" in that it has to compute fewer things.
pub trait LazyClaims<F: Field> {
	fn claims_num(&self) -> usize;
	fn vars_num(&self) -> usize;
	fn combined_sum(&self, a: F) -> F;       // CombinedSum returns c = ∑_{1≤j≤m} aʲ⁻¹cⱼ
	fn degree(&self) -> usize;    			// Degree of the ith claim
	fn verify_final_eval(&mut self, r: &[F], combination_coeff: F, purported_value: F, proof: &[F]) -> Result<(), Error>;
}

// Proof of a multi-sumcheck statement.
#[derive(Debug, Clone)]
pub struct SumCheckProof<F: Field> {
	pub partial_sum_polys: Vec<Vec<F>>,
	pub final_eval_proof: Vec<F>,
}

impl<F: Field> SumCheckProof<F> {
	pub fn new() -> Self {
		SumCheckProof {
			partial_sum_polys: Vec::new(),
			final_eval_proof: Vec::new(),
		}
	}
}

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
	let points = make_subgroup_elements::<F>((claims.degree() + 1) as u64); // j is the last variable here so vars_num - 1
	let chunk_size = points.len()/vars_num;
	let domain = points.chunks(chunk_size).clone().collect_vec();
	proof.partial_sum_polys = vec![vec![]; vars_num];
	proof.partial_sum_polys[0] = claims.combine_and_first_poly(combination_coeff); // first partial sum poly
	
	let mut challenges = vec![F::ZERO; vars_num];
	for (j, partial_sum) in proof.partial_sum_polys.iter_mut().skip(1).take(vars_num - 1).enumerate() {
		transcript.write_field_elements(&*partial_sum)?;
		challenges[j] = transcript.squeeze_challenge();
		*partial_sum = claims.next(challenges[j]);
	}

	transcript.write_field_elements(&proof.partial_sum_polys[vars_num-1])?;
	challenges[vars_num-1] = transcript.squeeze_challenge(); 
	// directly use f_2(y) and evaluate at y = b, rather than interpolating f_2(y) from f_2(w) and then evaluating at y = b
	let t_star_poly = lagrange_interpolate(domain[vars_num-1], &proof.partial_sum_polys[vars_num-1]); 
	let t_star = eval_polynomial(&t_star_poly, challenges[vars_num-1]);
	transcript.write_field_element(&t_star)?;

	// start pi_eval
	// prover computes lagrange_bases and power vector for each variable
	for (j, challenge) in challenges.iter().enumerate() {
		let lagrange_bases = lagrange_bases::<F>(&[&domain[j]], &[*challenge]);
		let m = claims.degree() + 1;
		assert_eq!(lagrange_bases[0].len(), m);
		let power_vector = power_matrix_generator(&[*challenge], m as u64);
		transcript.write_field_elements(&lagrange_bases[0])?; //0 since k = 1 
		transcript.write_field_elements(&power_vector[0])?; //length k*logm, k = 1 for bivariate sumcheck
	}
	// proof.final_eval_proof = claims.prove_final_eval(&challenges);

	Ok(proof)
}

pub fn sumcheck_verify<F: PrimeField + Hash>(
    claims: &mut impl LazyClaims<F>, 
    transcript: &mut impl FieldTranscriptRead<F>,
) -> Result<(), Error> {

	let mut combination_coeff: F = F::ZERO;
	if claims.claims_num() >= 2 {
        combination_coeff = transcript.squeeze_challenge();
	}

	let points = make_subgroup_elements::<F>((claims.degree() + 1) as u64); // j is the last variable here so vars_num - 1
	let mut r = vec![F::ZERO; claims.vars_num()];
	// Just so that there is enough room for gJ to be reused
	let mut max_degree = claims.degree();
    // for j in 1..claims.vars_num() {
    //     if claims.degree() > max_degree {
    //         max_degree = claims.degree();
    //     }
    // }

	let mut g = vec![vec![F::ZERO; max_degree+1]; claims.vars_num()];   // At the end of iteration j, gJ = ∑_{i < 2ⁿ⁻ʲ⁻¹} g(X₁, ..., Xⱼ₊₁, i...)		NOTE: n is shorthand for claims.VarsNum()
	let t = claims.combined_sum(combination_coeff); // At the beginning of iteration j, gJR = ∑_{i < 2ⁿ⁻ʲ} g(r₁, ..., rⱼ, i...)
	for j in 0..claims.vars_num() {
		let round_poly_evaluation = transcript.read_field_elements(claims.degree() + 1)?;
		if round_poly_evaluation.len() != claims.degree() {
			return Err(Error::InvalidSumcheck("Malformed proof".to_string()));
		}

		g[j].copy_from_slice(&round_poly_evaluation); // g check deferred to pi_eval

		// Prepare for the next iteration
		r[j] = transcript.squeeze_challenge();
    }

	let t_star = transcript.squeeze_challenge();

	//start pi_eval
	let mut evaluations = vec![F::ZERO; claims.vars_num() + 1];
	evaluations[0] = t;
	for j in 0..claims.vars_num() { 
		let power_vector = transcript.read_field_elements(claims.degree() + 1)?; // m is max_degree + 1 = |H|, reads power_vector
		// length klogm, k = 1 for bivariate sumcheck, reads lagrange_bases
		let log_m = 64 - (claims.degree() + 1).leading_zeros() - 1;
		let lagrange_bases = vec![transcript.read_field_elements(log_m as usize)?];
	    evaluations[j+1] = lagrange_pi_eval_verifier(&[power_vector], &g[j], &lagrange_bases, &[&points], &[r[j]]);

		// partitioning the g[j], round_poly_evaluation into claims.vars_num() partitions and summing them up, i.e. G_1, G_2 in paper
		let partition = g[j].len()/claims.vars_num();
		let sum_partition = g[j][(j)*partition..(j+1)*partition].iter().sum::<F>();
		assert_eq!(evaluations[j], sum_partition); // jth check, so total 2 checks for bivariate sumcheck
	}

	assert_eq!(t_star, *evaluations.last().unwrap()); //third check
	// todo fourth check
	//claims.verify_final_eval(&r, combination_coeff, gjr, &[])
	Ok(())

}

struct SingleClaim<F: PrimeField> {
	input_preprocessors: Vec<MultivariatePolynomial<F, CoefficientBasis>>,
	eq: Vec<UnivariatePolynomial<F, CoefficientBasis>>, // vector of eq polys, where eq are the lagrange basis polynomials evaluated at the j'th evaluation point for all x_j
	evaluation_points: Vec<Vec<F>>,
	domain: Vec<Vec<F>>,
	gate: AddGate<F>,
}

impl<F: PrimeField> SingleClaim<F> {
    pub fn compute_gj(&self, 
		input_preprocessors: Vec<UnivariatePolynomial<F, CoefficientBasis>>, 
		eq_evals_univariate: Vec<F>
	) -> Vec<F> { // can use fft here
        let num_evals = 1 + self.eq.len(); // guaranteed to be no smaller than the actual deg(g_j)
		let points = make_subgroup_elements::<F>(num_evals as u64);
		points.iter()
		.zip(&eq_evals_univariate)
		.map(|(p, eq)| *eq * self.gate.evaluate(&input_preprocessors.iter().map(|prep| prep.evaluate(p)).collect_vec()))
		.collect()
    }

	pub fn new(input_preprocessors: Vec<MultivariatePolynomial<F, CoefficientBasis>>, evaluation_points: Vec<Vec<F>>, domain: Vec<Vec<F>>, gate: AddGate<F>) -> Self {
		SingleClaim {
			input_preprocessors,
			eq: Vec::new(),
			evaluation_points,
			domain,
			gate,
		}
	}
}

impl<F: PrimeField + Hash> Claims<F> for SingleClaim<F> {
	fn prove_final_eval(&self, r: &[F]) -> Vec<F> {
		unimplemented!()
	}

	fn vars_num(&self) -> usize {
		self.input_preprocessors[0].num_vars
	}

	fn claims_num(&self) -> usize {
		1
	}

	fn domain(&self) -> Vec<&[F]> {
		self.domain.iter().map(|v| v.as_slice()).collect::<Vec<_>>()
	}

	fn combine_and_first_poly(&mut self, a: F) -> Vec<F> {
        let vars_num = self.vars_num();
        let eq_length = 1 << vars_num;
        let claims_num = self.claims_num();
    
        // initialize the eq tables
        let eq_acc = (1..claims_num).fold(vec![vec![F::ZERO; eq_length]; claims_num], |mut acc, k| {
            let eq = lagrange_bases(&self.domain(), &self.evaluation_points[k]);
			acc[k].iter_mut().zip(&eq[k]).for_each(|(acc, eq)| *acc = *eq * a.pow([k as u64]));
			acc
        });
    
        // from this point on the claim is a rather simple one: g = E(h) × R_v (P_u0(h), ...) 
        // where E and the P_u are multilinear and R_v is of low-degree
		let mut input_preprocessors = Vec::new();
        for preprocessor in &mut self.input_preprocessors {
            input_preprocessors.push(preprocessor.univariate_poly_first_summed()); // todo need to input domain from sumcheck
        }
		let eq_evals_univariate = eq_poly_first_summed(&eq_acc); //todo not correct
        self.compute_gj(input_preprocessors, eq_evals_univariate)
	}

	fn next(&mut self, element: F) -> Vec<F> {
		let mut input_preprocessors = Vec::new();
        for preprocessor in &mut self.input_preprocessors {
            input_preprocessors.push(preprocessor.univariate_poly_fix_var(&element)); // todo need to input domain from sumcheck
        }
        //let eq = eq_acc.univariate_poly_fix_var(&element); //fix the first variable and take product on points except second point so univariate
        //self.compute_gj(input_preprocessors, eq)
		vec![F::ZERO; self.degree() + 1]
	}

	fn degree(&self) -> usize {
		self.eq.len() - 1
	}

}


#[cfg(test)]
mod tests {
	use super::*;
	use halo2_proofs::arithmetic::Field;
	use halo2_proofs::halo2curves::ff::PrimeField;

}