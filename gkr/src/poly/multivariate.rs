use crate::{
    poly::Polynomial,
    util::{
        arithmetic::{div_ceil, horner, powers, Field},
        impl_index,
        parallel::{num_threads, parallelize, parallelize_iter},
        Deserialize, Itertools, Serialize,
    }, Error,
};
use halo2_proofs::{arithmetic::{eval_polynomial, lagrange_interpolate}, halo2curves::ff::{BatchInvert, PrimeField}};
use rand::RngCore;
use std::{
    borrow::Borrow, cmp::{max_by, Ordering::{Equal, Greater, Less}}, collections::{HashMap, HashSet}, fmt::Debug, hash::Hash, iter::{self, successors, Sum}, marker::PhantomData, ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign}
};

use super::{univariate::{Basis, CoefficientBasis, UnivariatePolynomial}, SimplePolynomial};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SparseTerm<F> {
  terms: Vec<(usize, usize)>, // variable, power
  domain: Vec<(usize, Vec<F>)>, // variable, domain
  degree: usize,
}

// Monomial representation of a multivariate polynomial
impl<F: PrimeField> SparseTerm<F> {
      /// Sums the powers of any duplicated variables. Assumes `term` is sorted.
      pub fn combine(term: &[(usize, usize)]) -> Vec<(usize, usize)> {
          let mut term_dedup: Vec<(usize, usize)> = Vec::new();
          for (var, pow) in term {
              if let Some(prev) = term_dedup.last_mut() {
                  if prev.0 == *var {
                      prev.1 += pow;
                      continue;
                  }
              }
              term_dedup.push((*var, *pow));
          }
          term_dedup
      }

      pub fn num_vars(&self) -> usize {
          self.terms.len()
      }

      pub fn iter(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.terms.iter().map(|&(a, b)| (a, b))
      }

      pub fn rearrange_after_fix_first_var(&mut self) {
        self.terms = self.terms.iter().skip(1).map(|&(v, p)| (v - 1, p)).collect();
      }

      /// Create a new `Term` from a list of tuples of the form `(variable, power)`
      pub fn new(mut terms: Vec<(usize, usize)>, num_vars: usize, total_degree: usize) -> Self {
          // Remove any terms with power 0
          terms.retain(|(_, pow)| *pow != 0);
          // If there are more than one variables, make sure they are
          // in order and combine any duplicates
          if terms.len() > 1 {
              terms.sort_by(|(v1, _), (v2, _)| v1.cmp(v2));
              terms = Self::combine(&terms);
          }

          let domain = Vec::new();
          let degree = terms.iter().fold(0, |sum, acc| sum + acc.1);
          Self { terms, domain, degree }
      }

      /// Create a new `Term` from a list of tuples of the form `(variable, power)`
      pub fn new_with_domain(mut terms: Vec<(usize, usize)>, num_vars: usize, total_degree: usize, domain: &[&[F]]) -> Self {
          // Remove any terms with power 0
          terms.retain(|(_, pow)| *pow != 0);
          // If there are more than one variables, make sure they are
          // in order and combine any duplicates
          if terms.len() > 1 {
              terms.sort_by(|(v1, _), (v2, _)| v1.cmp(v2));
              terms = Self::combine(&terms);
          }

          let degree = terms.iter().fold(0, |sum, acc| sum + acc.1);
          let mut sparse_term = Self { terms, domain: Vec::new(), degree };
          sparse_term.set_domain(domain);
          sparse_term
      }

      #[allow(clippy::useless_conversion)]
      pub fn set_domain(&mut self, poly_domain: &[&[F]]) {
        self.domain = self.terms.iter()
        .zip(poly_domain.iter().enumerate())
        .map(|((v, _), domain)| {
            assert_eq!(*v, domain.0);
            (*v, domain.1.to_vec())
        })
        .collect_vec();
      }

      pub fn domain(&self) -> Vec<&[F]> {
        self.domain.iter().map(|v| v.1.as_slice()).collect_vec()
      }

      /// Returns the sum of all variable powers in `self`
      pub fn degree(&self) -> usize {
          self.degree
      }

      pub fn degree_of_var(&self, var: usize) -> usize {
        self.iter().find(|&(v, _)| v == var).map(|(_, p)| p).unwrap()
      }
  
      /// Returns a list of variables in `self`
      pub fn vars(&self) -> Vec<usize> {
          self.iter().map(|(v, _)| v).collect()
      }
  
      /// Returns a list of variable powers in `self`
      pub fn powers(&self) -> Vec<usize> {
          self.iter().map(|(_, p)| p).collect()
      }
  
      /// Returns whether `self` is a constant
      pub fn is_constant(&self) -> bool {
          self.num_vars() == 0 || self.degree() == 0
      }

      pub fn compute_contribution(
        vars: &[(usize, usize, Vec<F>)],
        index: usize,
        current_value: &mut F,
        sum: &mut F,
        _first_var_degree: usize,
    ) -> F {
      if index == vars.len() {
        return *sum;
      } else {
        let (other_var_idx, power, domain) = &vars[index];
        assert_eq!(*other_var_idx, index + 1);
        let mut new_value = F::ZERO;
          for &value in domain {
            new_value = value.pow([*power as u64]);
            *sum += new_value;
          }
          Self::compute_contribution(vars, index + 1, &mut new_value, sum, _first_var_degree);
        
        }
        *sum
    }
  
      pub fn univariate_term(&self) -> (F, SparseTerm<F>) {
        // Treat first variable, 0 as the one to fold
        let first_var = 0;
        let first_var_degree = self.terms.first().unwrap().1;
        assert_eq!(first_var_degree, self.degree_of_var(first_var));
        
        // Prepare other variables
        let other_vars = self.terms.clone().into_iter().skip(1)
          .zip(self.domain.iter().skip(1))
          .map(|((v, p), domain)| {
              assert_eq!(v, domain.0);
              (v, p, domain.1.clone())
          })
          .collect_vec();

        // let other_terms = self.terms.clone().into_iter().skip(1).collect_vec();
        // let points = make_subgroup_elements::<F>((self.degree() + 1) as u64);
        // let chunk_size = points.len()/self.num_vars();
        // let other_vars = other_terms.iter()
        //   .zip(points.iter().skip(chunk_size).chunks(chunk_size).into_iter())
        //   .map(|(&(v, p), domain)| {
        //       (v, p, domain.cloned().collect_vec())
        //   })
        //   .collect_vec();

        let mut current_value = F::ONE;
        let mut sum = F::ZERO;
        // Start the recursive computation
        let univariate_coeff = Self::compute_contribution(&other_vars, 0, &mut current_value, &mut sum, first_var_degree);
        let mut sparse_term = SparseTerm::new(vec![(0, first_var_degree)], 1, first_var_degree);
        sparse_term.set_domain(&self.domain());
        (univariate_coeff, sparse_term)
      } 

      /// Evaluates `self` at the given `point` in the field.
      pub fn evaluate(&self, point: &[F]) -> F {
          self.iter()
              .map(|(var, power)| point[var].pow([power as u64]))
              .product()
      }

      /// Fix the first variable to a given value before converting to univariate in sumcheck.
      pub fn fix_first_var(&mut self, point: &F) -> F {
        let first_var_degree = self.terms.first().unwrap().1;
        let first_coeff = self.terms.first().map(|(_, power)| point.pow([*power as u64])).unwrap_or(F::ZERO);
        self.rearrange_after_fix_first_var();
        self.degree -= first_var_degree;
        first_coeff
      }
}

/// A multivariate polynomial of arbitrary degree.
/// // Create a multivariate polynomial in 3 variables, with 4 terms:
/// // 2*x_0^3 + x_0*x_2 + x_1*x_2 + 5
/// let poly = SparsePolynomial::from_coefficients_vec(
///     3,
///     vec![
///         (Fq::from(2), SparseTerm::new(vec![(0, 3)])),
///         (Fq::from(1), SparseTerm::new(vec![(0, 1), (2, 1)])),
///         (Fq::from(1), SparseTerm::new(vec![(1, 1), (2, 1)])),
///         (Fq::from(5), SparseTerm::new(vec![])),
///     ],
/// ); 
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MultivariatePolynomial<F, B> {
    /// The number of variables the polynomial supports
    pub num_vars: usize,
    /// degree of the polynomial
    pub degree: usize,
    /// List of each term along with its coefficient
    pub terms: Vec<(F, SparseTerm<F>)>,
    /// domain of the polynomial
    pub domain: Vec<Vec<F>>,
    _marker: PhantomData<B>,
}

impl<F> Default for MultivariatePolynomial<F, CoefficientBasis> {
    fn default() -> Self {
        Self {
            num_vars: 0,
            degree: 0,
            terms: Vec::new(),
            domain: Vec::new(),
            _marker: PhantomData,
        }
    }
}

impl<F: Field, B: Basis> MultivariatePolynomial<F, B> {
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &(F, SparseTerm<F>)> {
        self.terms.iter()
    }
}

impl<F: PrimeField> SimplePolynomial<F> for MultivariatePolynomial<F, CoefficientBasis> {
    type Point = Vec<F>;

    fn from_evals(_: Vec<F>) -> Self {
      unimplemented!()
    }

    fn into_evals(self) -> Vec<F> {
      unimplemented!()
    }

    fn evals(&self) -> &[F] {
      unimplemented!()
    }

    fn evaluate(&self, point: &Self::Point) -> F {
      MultivariatePolynomial::evaluate(self, point)
    }
}

impl<F: PrimeField> MultivariatePolynomial<F, CoefficientBasis> {
    pub fn new(all_terms: Vec<Vec<(usize, usize)>>, coeffs: Vec<F>, num_vars_given: usize, total_degree_given: usize, m: usize) -> Result<Self, Error> {
      let mut num_vars = 0;
      let mut degree = 0;
      let terms = all_terms.into_iter().zip(coeffs).map(|(term, coeff)| {
        num_vars = term.len();
        degree = degree.max(term.iter().map(|(_, p)| p).sum::<usize>());
        (coeff, SparseTerm::new(term, num_vars, degree))
      }).collect();

      let points = make_subgroup_elements::<F>(m as u64);
      let domain = vec![points; num_vars];
      //let domain = points.iter().chunks(points.len()/num_vars).into_iter().map(|chunk| chunk.cloned().collect_vec()).collect_vec();
      assert_eq!(num_vars, num_vars_given);
      assert_eq!(degree, total_degree_given);
      assert_eq!(domain.len(), num_vars);
      Ok(Self { terms, num_vars, degree, domain, _marker: PhantomData })
    }

    /// Fix the first variable to a given value before converting to univariate in sumcheck.
    pub fn fix_first_var(&mut self, point: &F){
      self.terms.iter_mut()
      .map(|(coeff, term)| (*coeff * term.fix_first_var(point), term))
      .collect_vec();
    }

    pub fn evaluate(&self, r: &[F]) -> F {
      //assert!(point.len() >= self.num_vars, "Invalid evaluation domain");
      if self.is_zero() {
          return F::ZERO;
      }
      self.iter()
          .map(|(coeff, term)| *coeff * term.evaluate(r))
          .sum()
    }

    pub fn univariate_poly_first_summed(&mut self, domain: &[&[F]]) -> UnivariatePolynomial<F, CoefficientBasis> {
      let mut poly = self.terms.iter_mut()
        .map(|(coeff, term)| {
          term.set_domain(domain);
          let (univariate_coeff, univariate_term) = term.univariate_term();
          (*coeff * univariate_coeff, univariate_term)
        }).collect_vec();

      let degree = self.terms.iter().map(|(_, term)| term.degree_of_var(0)).max().unwrap_or(0);
      // Sort the polynomial terms by degree of SparseTerm
      let mut degree_map: HashMap<usize, (F, SparseTerm<F>)> = HashMap::new();
      for (coeff, term) in poly {
        degree_map.entry(term.degree())
            .and_modify(|(c, _)| *c += coeff)
            .or_insert((coeff, term));
      }
      
      for i in 1..=degree {
        if degree_map.get(&i).is_none() {
          println!("inserting zero term for degree: {:?}", i);
          degree_map.insert(i, (F::ZERO, SparseTerm::new(vec![], self.num_vars, i)));
        }
      }

      poly = degree_map.into_values().collect();
      poly.sort_by(|(_, term1), (_, term2)| term1.degree().cmp(&term2.degree()));      
      UnivariatePolynomial::new(poly.into_iter().map(|(coeff, _)| coeff).collect())
    }

    pub fn univariate_poly_fix_var(&mut self, domain: &[&[F]], r: &F) -> UnivariatePolynomial<F, CoefficientBasis> {
      self.terms.iter_mut()
        .for_each(|(_, term)| term.set_domain(domain)); 
      self.fix_first_var(r);

      assert_ne!(self.num_vars, 1); // should not be called for univariate polynomials as it is dealt in the first round of sumcheck
      if self.num_vars == 2 { // special case when polynomial becomes bivariate
        self.terms.sort_by(|(_, term1), (_, term2)| term1.degree().cmp(&term2.degree()));
        return UnivariatePolynomial::new(self.terms.iter().map(|(coeff, _)| *coeff).collect_vec());
      }

      let mut poly = self.terms.iter_mut()
          .map(|(coeff, term)| {
            let (univariate_coeff, univariate_term) = term.univariate_term();
            (*coeff * univariate_coeff, univariate_term)
          }).collect_vec();

      let degree = self.terms.iter().map(|(_, term)| term.degree_of_var(0)).max().unwrap();
      // Sort the polynomial terms by degree of SparseTerm
      let mut degree_map: HashMap<usize, (F, SparseTerm<F>)> = HashMap::new();
      for (coeff, term) in poly {
          degree_map.entry(term.degree())
              .and_modify(|(c, _)| *c += coeff)
              .or_insert((coeff, term));
      }

      for i in 1..=degree {
        if degree_map.get(&i).is_none() {
          println!("inserting zero term for degree: {:?}", i);
          degree_map.insert(i, (F::ZERO, SparseTerm::new(vec![], self.num_vars, i)));
        }
      }

      poly = degree_map.into_values().collect();
      poly.sort_by(|(_, term1), (_, term2)| term1.degree().cmp(&term2.degree()));      
      UnivariatePolynomial::new(poly.into_iter().map(|(coeff, _)| coeff).collect())
    }
}

/// Computes eq(x, a) = product_{j=1}^k L_{x_j}^{H}(a_j) ∀ x ∈ H
/// where L_{x_j}^{H}(u) = c_{x_j} * (u^m - 1) / (u - x_j)
///
/// - `x`: Vector of length k where each element represents a variable which is a 
/// vector of all values of that variable in subgroup H i.e. x_j ∀ j ∈ [k] , x_j_i ∀ i ∈ [m]
/// - `a`: evaluation points (length k)
/// - `m`: Order of the subgroup H = length of x
/// - `H`: Vector containing elements of the subgroup H
/// Returns an element of the field F.
/// x and a are single elements in bivariate sumcheck case
// pub fn eval_eq<F: PrimeField + Hash>(x: &[F], a: &[F]) -> F {
//     assert_eq!(x.len(), a.len(), "Vectors x and a must have the same length.");
//     let m = x.len() as u64;
//     let mut result = F::ONE;

//     // Precompute barycentric weights c_x for each x_j in x
//     let c_x = compute_barycentric_weights::<F>(x);
//     for (j, (&x_j, &a_j)) in x.iter().zip(a.iter()).enumerate() {
//         let c_xj = c_x.get(&x_j).expect("x_j not in H");
//         let numerator = a_j.pow(&[m]) - F::ONE;
//         let denominator = a_j - x_j;
//         let inv_denominator = denominator.invert().unwrap_or_else(|| panic!("Inversion failed"));
//         let l_xj = *c_xj * numerator * inv_denominator;
//         result *= l_xj;
//     }

//     result
// }

#[allow(unused)]
pub fn power_matrix_generator<F: PrimeField + Hash>(a: &[F], m: u64) -> Vec<Vec<F>> {
  let log_m = 64 - m.leading_zeros() - 1; // Compute log2(m)
  let mut power_matrix = Vec::with_capacity(a.len());
  for &base in a {
      let mut power_vector = Vec::with_capacity((log_m + 1) as usize);
      let mut current_power = base;
      for _ in 0..log_m + 1 { 
          power_vector.push(current_power);
          current_power = current_power * current_power;
      }
      power_matrix.push(power_vector);
  }

  power_matrix
}

/// - `x`: Vector of length k where each element represents a variable which is a 
/// vector of all values of that variable in subgroup H i.e. x_j ∀ j ∈ [k] , x_j_i ∀ i ∈ [m]
/// - `a`: k evaluation points representing k variables 
/// bases are lagrange basis polynomials evaluated at some a_k for all x_k, i.e bases_k = lagrange_basis(a_k)
#[allow(unused)]
pub fn lagrange_bases<F: PrimeField + Hash>(x: &[&[F]], a: &[F]) -> Vec<Vec<F>> {
    assert_eq!(x.len(), a.len(), "Vectors x and a must have the same length.");
    let m = x[0].len() as u64; //todo check this
    let mut vanishing_idx = 0;
    // Precompute barycentric weights c_x for each x_j in x
    let c_x = x.iter().map(|x_j| compute_barycentric_weights::<F>(x_j)).collect_vec();
    let rational: Vec<Vec<Option<(F, F, F)>>> = x.iter().zip(a.iter()).enumerate().map(|(k, (x_j, &a_j))| {
        x_j.iter().enumerate().map(|(i, &x_ji)| {
            let c_xj = c_x[k].get(&x_ji).expect("x_j not in H");
            let numerator = a_j.pow([m]) - F::ONE;
            let denominator = a_j - x_ji;
            if numerator == denominator { // lagrange basis evaluated at a group element
              vanishing_idx = i;
              None
          } else {
              Some((*c_xj, numerator, denominator))
          }
        }).collect_vec()
    }).collect_vec();

    if rational.iter().any(|v| v.iter().any(|opt| opt.is_none())) {
      return vec![vec![F::ZERO; m as usize].iter().enumerate().map(|(i, _)| if i == vanishing_idx { F::ONE } else { F::ZERO }).collect_vec()];
    }

    // Batch invert denominators
    let mut denominators: Vec<F> = rational.iter().flatten().filter_map(|opt| opt.map(|(_, _, d)| d)).collect();
    denominators.batch_invert();

    // Unflatten denominators back into chunks
    let mut denominator_chunks = Vec::new();
    let chunk_size = denominators.len() / rational.len();
    for chunk in denominators.chunks(chunk_size) {
        denominator_chunks.push(chunk.to_vec());
    }

    // Initialize lagrange bases
    let mut bases = vec![Vec::new(); rational.len()];
    // Compute lagrange bases
    for k in 0..rational.len() {
      for (opt, inv_denominator) in rational[k].iter().zip(denominator_chunks[k].clone()) {
        if let Some((c_xj, numerator, _)) = opt {
          bases[k].push(*c_xj * numerator * inv_denominator);
        }
      }
    } 

    bases
}

// eq is a vector of vectors of lagrange basis polynomials evaluated at diff variables of a, bases_k = lagrange_basis(a_k)
// just return the first vector of eq which represents lagrange bases for first variable, other lagrange bases for rest of variables will sum to 1 when x_i = a_i
pub fn eq_poly_univariate<F: PrimeField + Hash>(eq: &[Vec<F>]) -> Vec<F> {
  eq.first().unwrap().to_vec()
}

// similar as above instead returns evals at element a, todo
pub fn eq_poly_fix_first_var_univariate<F: PrimeField + Hash>(points: &[F], eq: &[Vec<F>], a: &F) -> Vec<F> {
  let eq_first = eq.first().unwrap();
  let eq_first_poly = lagrange_interpolate(points, eq_first);
  let eq_first_eval = eval_polynomial(&eq_first_poly, *a);
  let eq_second = eq[1].to_vec();
  eq_second.iter().map(|evals| *evals * eq_first_eval).collect_vec() //scale by eq_first_eval
}

/// - `x`: Vector of length k where each element represents a variable which is a 
/// vector of all values of that variable in subgroup H i.e. x_j ∀ j ∈ [k] , x_j_i ∀ i ∈ [m]
/// - `a`: k evaluation points representing k variables 
/// bases are lagrange basis polynomials evaluations at diff variables of a, i.e bases_k = lagrange_basis(a_k)
// #[allow(unused)]
// pub fn lagrange_bases_coeff<F: PrimeField + Hash>(x: &[&[F]], a: &[F]) -> Vec<UnivariatePolynomial<F, CoefficientBasis>> {
//     assert_eq!(x.len(), a.len(), "Vectors x and a must have the same length.");
//     let m = x[0].len() as u64;
//     let mut vanishing_idx = 0;
//     // Precompute barycentric weights c_x for each x_j in x
//     let c_x = x.iter().map(|x_j| compute_barycentric_weights::<F>(x_j)).collect_vec();
//     let rational: Vec<Vec<Option<(F, F, F)>>> = x.iter().zip(a.iter()).enumerate().map(|(k, (x_j, &a_j))| {
//         x_j.iter().enumerate().map(|(i, &x_ji)| {
//             let c_xj = c_x[k].get(&x_ji).expect("x_j not in H");
//             let numerator = a_j.pow([m]) - F::ONE;
//             let denominator = a_j - x_ji;
//             if numerator == denominator { // lagrange basis evaluated at a group element
//               vanishing_idx = i;
//               None
//           } else {
//               Some((*c_xj, numerator, denominator))
//           }
//         }).collect_vec()
//     }).collect_vec();

//     if rational.iter().any(|v| v.iter().any(|opt| opt.is_none())) {
//       return vec![UnivariatePolynomial::new(vec![F::ZERO; m as usize].iter().enumerate().map(|(i, _)| if i == vanishing_idx { F::ONE } else { F::ZERO }).collect_vec())];
//     }

//     // Batch invert denominators
//     let mut denominators: Vec<F> = rational.iter().flatten().filter_map(|opt| opt.map(|(_, _, d)| d)).collect();
//     denominators.batch_invert();

//     // Unflatten denominators back into chunks
//     let mut denominator_chunks = Vec::new();
//     let chunk_size = denominators.len() / rational.len();
//     for chunk in denominators.chunks(chunk_size) {
//         denominator_chunks.push(chunk.to_vec());
//     }

//     // Initialize lagrange bases
//     let mut bases = vec![Vec::new(); rational.len()];
//     // Compute lagrange bases
//     for k in 0..rational.len() {
//       for (opt, inv_denominator) in rational[k].iter().zip(denominator_chunks[k].clone()) {
//         if let Some((c_xj, numerator, _)) = opt {
//           bases[k].push(*c_xj * numerator * inv_denominator);
//         }
//       }
//     } 

//     assert_eq!(bases[0].len(), m as usize);
//     bases.iter()
//         .map(|poly| UnivariatePolynomial::new(lagrange_interpolate(&eval_points, poly)))
//         .collect_vec()
// }

/// - `x`: Vector of length k where each element represents a variable which is a 
/// vector of all values of that variable in subgroup H i.e. x_j ∀ j ∈ [k] , x_j_i ∀ i ∈ [m]
/// - `a`: k evaluation points representing k variables 
/// bases are lagrange basis polynomials evaluations at diff variables of a, i.e bases_k = lagrange_basis(a_k)
#[allow(unused)]
pub fn lagrange_bases_poly<F: PrimeField + Hash>(x: &[&[F]]) -> Vec<UnivariatePolynomial<F, CoefficientBasis>> {
  let m = x[0].len() as u64;
  let eval_points = make_outside_subgroup_elements::<F>(m);
  let mut vanishing_idx = 0;
  // Precompute barycentric weights c_x for each x_j in x
  let c_x = x.iter().map(|x_j| compute_barycentric_weights::<F>(x_j)).collect_vec();
  let rational: Vec<Vec<Option<(F, F, F)>>> = x.iter().enumerate().map(|(k, x_j)| {
      x_j.iter().zip(eval_points.iter()).enumerate().map(|(i, (&x_ji, &a_j))| {
          let c_xj = c_x[k].get(&x_ji).expect("x_j not in H");
          let numerator = a_j.pow([m]) - F::ONE;
          let denominator = a_j - x_ji;
          if numerator == denominator { // lagrange basis evaluated at a group element
            vanishing_idx = i;
            None
          } else {
            Some((*c_xj, numerator, denominator))
          }
        }).collect_vec()
  }).collect_vec();

  if rational.iter().any(|v| v.iter().any(|opt| opt.is_none())) {      
    return vec![UnivariatePolynomial::new(vec![F::ZERO; m as usize].iter().enumerate().map(|(i, _)| if i == vanishing_idx { F::ONE } else { F::ZERO }).collect_vec()  )];
  }

    // Batch invert denominators
    let mut denominators: Vec<F> = rational.iter().flatten().filter_map(|opt| opt.map(|(_, _, d)| d)).collect();
    denominators.batch_invert();

    // Unflatten denominators back into chunks
    let mut denominator_chunks = Vec::new();
    let chunk_size = denominators.len() / rational.len();
    for chunk in denominators.chunks(chunk_size) {
        denominator_chunks.push(chunk.to_vec());
    }

    // Initialize lagrange bases
    let mut bases = vec![Vec::new(); rational.len()];
    // Compute lagrange bases
    for k in 0..rational.len() {
      for (opt, inv_denominator) in rational[k].iter().zip(denominator_chunks[k].clone()) {
        if let Some((c_xj, numerator, _)) = opt {
          bases[k].push(*c_xj * numerator * inv_denominator);
        }
      }
    } 

    assert_eq!(bases[0].len(), m as usize);
    bases.iter()
        .map(|poly| UnivariatePolynomial::new(lagrange_interpolate(&eval_points, poly)))
        .collect_vec()
}

/// Computes barycentric weights c_x for all x in H.
/// - `H`: Vector containing elements of the subgroup H.
/// Returns a map from elements in H to their barycentric weights.
fn compute_barycentric_weights<F: PrimeField + Hash>(h: &[F]) -> std::collections::HashMap<F, F> {
    let mut c_x = HashMap::new();
    let mut inv_denominator_vec = Vec::new();

    // Precompute the denominators for each x in H
    for &x in h {
        let mut denominator = F::ONE;
        for &y in h {
            if y != x {
                denominator *= x - y;
            }
        }
        inv_denominator_vec.push(denominator);
    }
    inv_denominator_vec.batch_invert();

    for (i, &x) in h.iter().enumerate() {
      c_x.insert(x, inv_denominator_vec[i]);
    }

    c_x
}

// eval_at = a is single element in bivariate sumcheck case
// power vector = A is a vector of logm elements in bivariate sumcheck case, 
// where each element can be a vector of k elements but k = 1 in bivariate sumcheck case
// takes power vector and lagrange bases from transcript
#[allow(unused)]
pub fn lagrange_pi_eval_verifier<F: PrimeField + Hash>(
  power_vector: &[Vec<F>],
  f_poly_evals: &[F],
  lagrange_poly_evals: &[Vec<F>], 
  points: &[&[F]],
  eval_at: &[F], 
) -> F {
  for i in 0..power_vector.len() {
    assert_eq!(power_vector[i][0], eval_at[i]);
    for j in 0..power_vector[i].len() - 1 {
      assert_eq!(power_vector[i][j]*power_vector[i][j], power_vector[i][j+1]);
    }
  }
      
  //assert_eq!(power_vector.len(), log2(m));
  let (mut f_polys_sum, mut f_sum) = (F::ZERO, F::ZERO);
  let lagrange_multipliers = points.iter().map(|x_i| compute_barycentric_weights::<F>(x_i)).collect_vec();

  assert_eq!(points[0].len(), lagrange_poly_evals[0].len()); // lagrange polynomials are defined for each x ∈ H, points are collection of all x in H
  for i in 0..lagrange_poly_evals[0].len() { // i runs through all lagrange polynomials defined for each x ∈ H
    let (mut lagrange_poly_prod, mut diff_points, mut rhs) = (F::ONE, F::ONE, F::ONE);
    for k in 0..eval_at.len() { // k runs through all eval points, k = 1 in bivariate sumcheck case
      lagrange_poly_prod *= lagrange_poly_evals[k][i];
      diff_points *= eval_at[k] - points[k][i]; // should be i ?
      rhs *= *lagrange_multipliers[k].get(&points[k][i]).unwrap() * (*power_vector[k].last().unwrap() - F::ONE);
      f_sum += f_poly_evals[i] * lagrange_poly_evals[k][i];
    }
    assert_eq!(rhs, lagrange_poly_prod*diff_points);
  }

  f_sum      
}

pub fn init_eq<F: PrimeField + Hash>(domain: &[&[F]], evaluation_point: &[F]) -> Vec<F> {
  let bases = lagrange_bases(domain, evaluation_point);
  (0..bases[0].len())
  .map(|i| bases.iter().map(|v| v[i]).product())
  .collect()
}

pub fn make_subgroup_elements<F: PrimeField>(m: u64) -> Vec<F> {
  assert!(m.is_power_of_two(), "Order of the multiplicative subgroup H must be a power of 2");
  //assert!(m > 2, "choose m > 2"); //todo is this required?
  let exponent = (-F::ONE) * F::from(m).invert().unwrap(); // (r - 1) / m
  let exponent_u64: [u64; 4] = exponent.to_repr().as_ref()
    .chunks_exact(8)
    .map(|chunk| u64::from_le_bytes(chunk.try_into().unwrap()))
    .collect::<Vec<_>>()
    .try_into()
    .unwrap();
  let root_of_unity = F::MULTIPLICATIVE_GENERATOR.pow(exponent_u64);
  successors(Some(F::ONE), |&x| Some(x * root_of_unity))
  .take(m as usize)
  .collect_vec()
}

pub fn make_outside_subgroup_elements<F: PrimeField + Hash>(m: u64) -> Vec<F> {
  let subgroup_elements = make_subgroup_elements::<F>(m);
  let excluded_set: HashSet<F> = subgroup_elements.into_iter().collect();
  (2..).map(|x| F::from(x)).filter(|&x| !excluded_set.contains(&x)).take(m as usize).collect() //todo check to be safe start from 0, 1
}
    
use nalgebra::{Matrix4, Vector4};

fn vandermonde_4(points: &[f64; 4]) -> Matrix4<f64> {
    Matrix4::from_fn(|i, j| points[i].powi(j as i32))
}

/// Interpolates a bivariate polynomial f(x,y) of degree at most 3 in each variable
/// given 16 evaluations at a 4x4 grid of points.
/// 
/// xs: [x0, x1, x2, x3] distinct x-values
/// ys: [y0, y1, y2, y3] distinct y-values
/// f_values: 16 values of f(x_i, y_j), arranged in row-major order:
///           f_values[i*4 + j] = f(x_i, y_j)
/// 
/// Returns a 4x4 matrix A of coefficients a_{r,s}, where:
/// f(x,y) = sum_{r=0}^3 sum_{s=0}^3 A[r,s] * x^r * y^s
fn interpolate_bivariate(
    xs: &[f64; 4], 
    ys: &[f64; 4],
    f_values: &[f64;16]
) -> Option<Matrix4<f64>> {
    let vx = vandermonde_4(xs);  // 4x4
    let vy = vandermonde_4(ys);  // 4x4
    
    // F is a 4x4 matrix of f(x_i,y_j)
    let f_matrix = Matrix4::from_row_slice(f_values);

    // Invert Vx and Vy
    let vx_inv = vx.try_inverse()?;
    let vy_inv = vy.try_inverse()?;

    // A = Vx^{-1} * F * (Vy^{-1})^T
    // First do M = Vx^{-1} * F
    let m = vx_inv * f_matrix;
    // Then A = M * (Vy^{-1})^T
    let a = m * vy_inv.transpose();

    Some(a)
}

#[cfg(test)]
mod tests {
  use bitvec::domain;
  use halo2_proofs::halo2curves::bn256::Fr;
  use halo2_proofs::arithmetic::Field;
  use itertools::Itertools;
  use num_traits::ToPrimitive;
  use rand::Rng;
  use crate::poly::multivariate::{compute_barycentric_weights, interpolate_bivariate, lagrange_bases, make_subgroup_elements, power_matrix_generator, MultivariatePolynomial};
  use crate::poly::univariate::UnivariatePolynomial;
  use halo2_proofs::halo2curves::ff::PrimeField;
  use super::{lagrange_pi_eval_verifier, SparseTerm};


  #[test]
  fn test_sparse_term() {
    let term = SparseTerm::<Fr>::new(vec![(0, 4), (1, 3)], 2, 7);
    assert_eq!(term.degree_of_var(0), 3);
    assert_eq!(term.degree_of_var(1), 4);
  }

  #[test]
  fn test_sparse_term_fix_var() {
    let mut term = SparseTerm::<Fr>::new(vec![(0, 4), (1, 3)], 2, 7);
    let coeff = term.fix_first_var(&Fr::from(2));
    assert_eq!(coeff, Fr::from(16));
    assert_eq!(term.degree(), 3);
    assert_eq!(term.terms.len(), 1);
    assert_eq!(term.terms[0], (1, 3));
  }

  #[test]
  fn test_sparse_term_fold_univariate() {
    let num_vars = 2;
    let points = make_subgroup_elements::<Fr>(8);
    let domain = points.chunks(points.len()/num_vars).collect_vec();
    let mut term = SparseTerm::<Fr>::new(vec![(0, 4), (1, 3)], 2, 7);
    term.set_domain(&domain);
    let (coeff, univariate_term) = term.univariate_term();
    assert_eq!(univariate_term.terms.len(), 1);
  }

  // #[test]
  // fn test_univariate_poly_first_summed() {
  //   let mut multivariate_poly = MultivariatePolynomial::new(vec![vec![(0, 4), (1, 3), (2, 2), (3, 6)]], vec![Fr::ONE], 4, 15).unwrap();
  //   let domain_owned: Vec<Vec<Fr>> = multivariate_poly.domain.clone();
  //   let domain: Vec<&[Fr]> = domain_owned.iter().map(|v| v.as_slice()).collect();
  //   let univariate_poly = multivariate_poly.univariate_poly_first_summed(&domain);
  //   assert_eq!(univariate_poly.degree(), 4);
  //   assert_eq!(univariate_poly.coeffs().len(), univariate_poly.degree() + 1);
  // }

  // #[test]
  // fn test_univariate_poly_fix_var() {
  //   let mut multivariate_poly = MultivariatePolynomial::new(vec![vec![(0, 4), (1, 3), (2, 2), (3, 6)]], vec![Fr::ONE], 4, 15).unwrap();
  //   let domain_owned: Vec<Vec<Fr>> = multivariate_poly.domain.clone();
  //   let domain: Vec<&[Fr]> = domain_owned.iter().map(|v| v.as_slice()).collect();
  //   let univariate_poly = multivariate_poly.univariate_poly_fix_var(&domain, &Fr::from(2));
  //   assert_eq!(univariate_poly.degree(), 3);
  //   assert_eq!(univariate_poly.coeffs().len(), univariate_poly.degree() + 1);
  // }

  // #[test]
  // fn test_univariate_poly_first_summed_deg1() {
  //   let mut multivariate_poly = MultivariatePolynomial::new(vec![vec![(0, 1), (1, 1), (2, 1), (3, 1)]], vec![Fr::ONE], 4, 15).unwrap();
  //   let domain_owned: Vec<Vec<Fr>> = multivariate_poly.domain.clone();
  //   let domain: Vec<&[Fr]> = domain_owned.iter().map(|v| v.as_slice()).collect();
  //   let univariate_poly = multivariate_poly.univariate_poly_first_summed(&domain);
  //   assert_eq!(univariate_poly.degree(), 4);
  //   assert_eq!(univariate_poly.coeffs().len(), univariate_poly.degree() + 1);
  // }

  // #[test]
  // fn test_univariate_poly_fix_var_deg1() {
  //   let mut multivariate_poly = MultivariatePolynomial::new(vec![vec![(0, 1), (1, 1), (2, 1), (3, 1)]], vec![Fr::ONE], 4, 15).unwrap();
  //   let domain_owned: Vec<Vec<Fr>> = multivariate_poly.domain.clone();
  //   let domain: Vec<&[Fr]> = domain_owned.iter().map(|v| v.as_slice()).collect();
  //   let univariate_poly = multivariate_poly.univariate_poly_fix_var(&domain, &Fr::from(2));
  //   assert_eq!(univariate_poly.degree(), 3);
  //   assert_eq!(univariate_poly.coeffs().len(), univariate_poly.degree() + 1);
  // }

  #[test]
  fn test_power_matrix_generator() {
    let a = vec![Fr::ONE, Fr::ROOT_OF_UNITY, Fr::ROOT_OF_UNITY.square(), Fr::ROOT_OF_UNITY.pow([4])];
    let m: u64 = 4;
    let log_m = 64 - m.leading_zeros() - 1; // Compute log2(m)
    let power_matrix = power_matrix_generator(&a, m);
    assert_eq!(power_matrix.len(), a.len());
    assert_eq!(power_matrix[0].len(), (log_m + 1) as usize);
    assert_eq!(power_matrix[0][0], Fr::ONE);
    assert_eq!(power_matrix[0][1], Fr::ONE.square());
    assert_eq!(power_matrix[0][2], Fr::ONE.pow([4]));
    assert_eq!(power_matrix[1][0], Fr::ROOT_OF_UNITY);
    assert_eq!(power_matrix[1][1], Fr::ROOT_OF_UNITY.square());
    assert_eq!(power_matrix[1][2], Fr::ROOT_OF_UNITY.pow([4]));
    assert_eq!(power_matrix[2][0], Fr::ROOT_OF_UNITY.square());
    assert_eq!(power_matrix[2][1], Fr::ROOT_OF_UNITY.pow([4]));
    assert_eq!(power_matrix[2][2], Fr::ROOT_OF_UNITY.pow([8]));
    assert_eq!(power_matrix[3][0], Fr::ROOT_OF_UNITY.pow([4]));
    assert_eq!(power_matrix[3][1], Fr::ROOT_OF_UNITY.pow([8]));
    assert_eq!(power_matrix[3][2], Fr::ROOT_OF_UNITY.pow([16]));
  }

  #[test]
  fn test_barycentric_weights() {
    // x is single element in bivariate sumcheck case, takes only four values
    let x: &[Fr] = &[Fr::ONE, Fr::from(2), Fr::from(3), Fr::from(4)];
    // w_0 = -1/6, w_1 = 1/2, w_2 = -1/2, w_3 = 1/6
    let weights = compute_barycentric_weights(x);
    assert_eq!(weights.get(&Fr::ONE).unwrap(), &Fr::from(6).invert().unwrap().neg());
    assert_eq!(weights.get(&Fr::from(2)).unwrap(), &Fr::from(2).invert().unwrap());
    assert_eq!(weights.get(&Fr::from(3)).unwrap(), &Fr::from(2).invert().unwrap().neg());
    assert_eq!(weights.get(&Fr::from(4)).unwrap(), &Fr::from(6).invert().unwrap());
  }

  #[test]
  fn test_make_subgroup() {
    let m = 1 << rand::thread_rng().gen_range(2..10); // order must be a power of 2
    let subgroup_elements = make_subgroup_elements::<Fr>(m);
    assert_eq!(subgroup_elements.len(), m as usize);
    assert_eq!(subgroup_elements[0], Fr::ONE); // subgroup elements wrap around
    assert_eq!(subgroup_elements.last().unwrap() * subgroup_elements[1], Fr::ONE);
  }

  #[test]
  fn test_root_of_unity() {
    // x is a single outer vector in bivariate sumcheck case
    let m = 4; // order of the multiplicative subgroup H
    let exponent = (-Fr::ONE) * Fr::from(m).invert().unwrap(); // (r - 1) / m
    let exponent_bytes = exponent.to_repr();
    let exponent_u64: [u64; 4] = [
        u64::from_le_bytes(exponent_bytes[0..8].try_into().unwrap()),
        u64::from_le_bytes(exponent_bytes[8..16].try_into().unwrap()),
        u64::from_le_bytes(exponent_bytes[16..24].try_into().unwrap()),
        u64::from_le_bytes(exponent_bytes[24..32].try_into().unwrap()),
    ];
    let root_of_unity = Fr::MULTIPLICATIVE_GENERATOR.pow(exponent_u64);
    assert_eq!(Fr::ONE, root_of_unity.pow([m]));
  }

  #[test]
  fn test_lagrange_bases() {
    // x is a single outer vector in bivariate sumcheck case
    let m = 1 << rand::thread_rng().gen_range(2..10); // order of the multiplicative subgroup H
    let x: &[&[Fr]] = &[&make_subgroup_elements::<Fr>(m)];

    for i in 0..x[0].len() {
      let lagrange_poly = lagrange_bases(x, &[x[0][i]]);
      assert_eq!(lagrange_poly.len(), x.len());
      assert_eq!(lagrange_poly[0].len(), x[0].len());
      assert!(lagrange_poly[0].iter().enumerate().all(|(j, &value)| 
          if i == j { value == Fr::ONE } else { value == Fr::ZERO } //lagrange basis vanishes at all other points
      ));
    }
  }

  #[test]
  fn test_poly_eval() {
    // x is a single outer vector in bivariate sumcheck case
    let m = 1 << rand::thread_rng().gen_range(2..10); // order of the multiplicative subgroup H
    let x: &[&[Fr]] = &[&make_subgroup_elements::<Fr>(m)];
    let a: &[Fr] = &[Fr::from(2)]; // a is single element in bivariate sumcheck case
    let lagrange_poly = lagrange_bases(x, a);
    //simple poly x^3 + x^2 + x + 1
    let f_poly = UnivariatePolynomial::new(vec![Fr::ONE, Fr::ONE, Fr::ONE, Fr::ONE]);
    let mut f_evaluated = Fr::ZERO;
    for i in 0..x[0].len() {
      f_evaluated += lagrange_poly[0][i] * f_poly.evaluate(&x[0][i]);
    }
    assert_eq!(f_evaluated, Fr::from(15));
  }

  #[test]
  fn test_lagrange_pi_eval_verifier() {
    let m = 1 << rand::thread_rng().gen_range(2..10); // order of the multiplicative subgroup H
    let x: &[&[Fr]] = &[&make_subgroup_elements::<Fr>(m)];
    let a: &[Fr] = &[Fr::from(2)]; // a is single element in bivariate sumcheck case
    let power_vector = power_matrix_generator(a, m);
    let lagrange_poly = lagrange_bases(x, a);
    //simple poly x^3 + x^2 + x + 1
    let f_poly = UnivariatePolynomial::new(vec![Fr::ONE, Fr::ONE, Fr::ONE, Fr::ONE]);
    let f_poly_evals = x[0].iter().map(|x_i| f_poly.evaluate(x_i)).collect_vec();
    let result = lagrange_pi_eval_verifier(&power_vector, &f_poly_evals, &lagrange_poly, x, a);
    assert_eq!(result, Fr::from(15));
  }

  #[test]
  fn test_interpolate_bivariate() {
    let xs = [1.0, 2.0, 3.0, 4.0];
    let ys = [10.0, 20.0, 30.0, 40.0];
    // Let's pick a test polynomial: f(x,y) = x^2 + y^2
    let mut f_values = [0.0; 16];
    for i in 0..4 {
      for j in 0..4 {
        let fx = xs[i];
        let fy = ys[j];
        f_values[i*4+j] = fx*fx + fy*fy;
      }
    }

    let a = interpolate_bivariate(&xs, &ys, &f_values).unwrap();

    let test_x: f64 = 5.0;
    let test_y: f64 = 60.0;
    let mut val: f64 = 0.0;
    for r in 0..4 {
        for s in 0..4 {
            val += a[(r,s)] * test_x.powi(r as i32) * test_y.powi(s as i32);
        }
    }

    assert_eq!(val.to_i64().unwrap(), 3625);
  }
}
