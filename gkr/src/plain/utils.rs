use halo2_proofs::halo2curves::{
    bn256, grumpkin,
    pasta::{pallas, vesta},
    CurveAffine,
};

pub trait TwoChainCurve: CurveAffine {
    type Secondary: TwoChainCurve<ScalarExt = Self::Base, Base = Self::ScalarExt, Secondary = Self>;
}

impl TwoChainCurve for bn256::G1Affine {
    type Secondary = grumpkin::G1Affine;
}

impl TwoChainCurve for grumpkin::G1Affine {
    type Secondary = bn256::G1Affine;
}

impl TwoChainCurve for pallas::Affine {
    type Secondary = vesta::Affine;
}

impl TwoChainCurve for vesta::Affine {
    type Secondary = pallas::Affine;
}

use hex::FromHex;

pub fn from_hex<F: PrimeField>(s: &str) -> F {
    let a = Vec::from_hex(&s[2..]).expect("Invalid Hex String");
    from_be_bytes_mod_order(&a as &[u8])
}

use halo2_proofs::halo2curves::ff::PrimeField;

use crate::util::arithmetic::from_be_bytes_mod_order;
// guassian elimination
pub fn mat_inverse<F: PrimeField>(mat: &[Vec<F>]) -> Vec<Vec<F>> {
    let n = mat.len();
    assert!(mat[0].len() == n);

    let mut m = mat.to_owned();
    let mut inv = vec![vec![F::ZERO; n]; n];
    for (i, invi) in inv.iter_mut().enumerate() {
        invi[i] = F::ONE;
    }

    // upper triangle
    for row in 0..n {
        for j in 0..row {
            // subtract from these rows
            let el = m[row][j];
            for col in 0..n {
                // do subtraction for each col
                if col < j {
                    m[row][col] = F::ZERO;
                } else {
                    let mut tmp = m[j][col];
                    tmp.mul_assign(&el);
                    m[row][col].sub_assign(&tmp);
                }
                if col > row {
                    inv[row][col] = F::ZERO;
                } else {
                    let mut tmp = inv[j][col];
                    tmp.mul_assign(&el);
                    inv[row][col].sub_assign(&tmp);
                }
            }
        }
        // make 1 in diag
        let el_inv = m[row][row].invert().unwrap();
        for col in 0..n {
            match col.cmp(&row) {
                std::cmp::Ordering::Less => inv[row][col].mul_assign(&el_inv),
                std::cmp::Ordering::Equal => {
                    m[row][col] = F::ONE;
                    inv[row][col].mul_assign(&el_inv)
                }
                std::cmp::Ordering::Greater => m[row][col].mul_assign(&el_inv),
            }
        }
    }

    // upper triangle
    for row in (0..n).rev() {
        for j in (row + 1..n).rev() {
            // subtract from these rows
            let el = m[row][j];
            for col in 0..n {
                // do subtraction for each col

                #[cfg(debug_assertions)]
                {
                    if col >= j {
                        m[row][col] = F::ZERO;
                    }
                }
                let mut tmp = inv[j][col];
                tmp.mul_assign(&el);
                inv[row][col].sub_assign(&tmp);
            }
        }
    }

    #[cfg(debug_assertions)]
    {
        for (row, mrow) in m.iter().enumerate() {
            for (col, v) in mrow.iter().enumerate() {
                if row == col {
                    debug_assert!(*v == F::ONE);
                } else {
                    debug_assert!(*v == F::ZERO);
                }
            }
        }
    }

    inv
}

pub fn mat_transpose<F: PrimeField>(mat: &[Vec<F>]) -> Vec<Vec<F>> {
    let rows = mat.len();
    let cols = mat[0].len();
    let mut transpose = vec![vec![F::ZERO; rows]; cols];

    for (row, matrow) in mat.iter().enumerate() {
        for col in 0..cols {
            transpose[col][row] = matrow[col];
        }
    }
    transpose
}