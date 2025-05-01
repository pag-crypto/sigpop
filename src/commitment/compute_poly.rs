use ark_secp256r1::{Fr as Scalar};
use std::ops::{Add, Mul};
use ark_std::{Zero, One, UniformRand};

pub struct PolynomialEval {
    pub eval: Scalar, // evaluation result
}

impl PolynomialEval {
    // Create a new polynomial evaluation result
    fn new(eval: Scalar) -> Self {
        PolynomialEval { eval }
    }

    // Multiply two polynomials
    fn multiply(&self, other: &PolynomialEval) -> Self {
        PolynomialEval::new(self.eval * other.eval)
    }
    
}

#[derive(Debug)]
pub struct Polynomial {
    pub coeffs: Vec<Scalar>, // Vector to store coefficients
}

impl Polynomial {
    // Create a new polynomial from coefficients
    fn new(coeffs: Vec<Scalar>) -> Self {
        Polynomial { coeffs }
    }

    // Multiply two polynomials
    fn multiply(&self, other: &Polynomial) -> Polynomial {
        let mut result = vec![Scalar::zero(); self.coeffs.len() + other.coeffs.len() - 1];
        
        for (i, &coeff1) in self.coeffs.iter().enumerate() {
            for (j, &coeff2) in other.coeffs.iter().enumerate() {
                result[i + j] += coeff1 * coeff2;
            }
        }

        Polynomial::new(result)
    }

    // Evaluate the polynomial at a point x
    pub fn eval(&self, x: &Scalar) -> Scalar {
        let mut result = Scalar::zero();
        let mut x_power = Scalar::one();

        for &coeff in self.coeffs.iter() {
            result += coeff * x_power;
            x_power *= x;
        }

        result
    }
}

fn compute_p_i(n: usize, a: &[Scalar], l: &[Scalar]) -> Vec<Polynomial> {
    let mut polynomials = Vec::new();

    // Generate all combinations of polynomials
    for i in 0..(1 << n) {
        let mut p_i = Polynomial::new(vec![Scalar::one()]); // Start with p_i(x) = 1

        for j in 0..n {
            let i_j = (i >> j) & 1; // Get the j-th bit of i to determine f_{j, i_j}
            let a_j = if i_j == 1 {a[j]} else {-a[j]};
            let scalar_i_j = if i_j == 1 {Scalar::one()} else {Scalar::zero()};
            let f_j_i_j = if scalar_i_j == l[j] {
                Polynomial::new(vec![a_j, Scalar::one()]) // x + a_j or x - a_j depending on i_j
            } else {
                Polynomial::new(vec![a_j])    // 1 + a_j or 1 - a_j
            };

            p_i = p_i.multiply(&f_j_i_j);
        }

        polynomials.push(p_i);
    }

    polynomials
}

// Assume n is power of 2
// Output: Coefficients of p0(x), p1(x), ..., p_{2^n-1}(x)
pub fn compute_pi_dp(a: &[Scalar], l: &[bool]) -> Vec<Polynomial> {
    let len_l = l.len();
    let mut l_reverse = l.to_vec();
    l_reverse.reverse();
    let mut polynomials = if l_reverse[0]{
        vec![Polynomial::new(vec![-a[len_l-1], Scalar::zero()]), Polynomial::new(vec![a[len_l-1], Scalar::one()])]
    } else {
        vec![Polynomial::new(vec![-a[len_l-1], Scalar::one()]), Polynomial::new(vec![a[len_l-1], Scalar::zero()])]
    };
    for (i, l_i) in l_reverse.iter().enumerate().skip(1) {
        let mut cur_poly = Vec::new();
        for poly in polynomials.iter() {
            if *l_i {
                cur_poly.push(poly.multiply(&Polynomial::new(vec![-a[len_l-i-1], Scalar::zero()])));
                cur_poly.push(poly.multiply(&Polynomial::new(vec![a[len_l-i-1], Scalar::one()])));
            } else {
                cur_poly.push(poly.multiply(&Polynomial::new(vec![-a[len_l-i-1], Scalar::one()])));
                cur_poly.push(poly.multiply(&Polynomial::new(vec![a[len_l-i-1], Scalar::zero()])));
            }
        }
        polynomials = cur_poly;
    }
    polynomials
}


pub fn compute_pi_eval_dp(f: &[Scalar], x: &Scalar) -> Vec<Scalar> {
    let len_l = f.len();
    let mut polynomials = vec![
        PolynomialEval::new(*x - f[len_l-1]), 
        PolynomialEval::new(f[len_l-1])
    ];
    for (i, _) in f.iter().enumerate().skip(1) {
        let mut cur_poly = Vec::new();
        for poly in polynomials.iter() {
            cur_poly.push(poly.multiply(&PolynomialEval::new(*x - f[len_l-i-1])));
            cur_poly.push(poly.multiply(&PolynomialEval::new(f[len_l-i-1])));
        }
        polynomials = cur_poly;
    }

    polynomials.iter().map(|x| x.eval).collect::<Vec<_>>()
}

fn main() {
    let n = 3;
    let a = vec![1, -2, 3]; // Example coefficients a_j
    let a = a.iter().map(|&x| Scalar::from(x)).collect::<Vec<_>>();
    let l = vec![1, 0, 1]; // l_j values {0, 1}
    let l = l.iter().map(|&x| Scalar::from(x)).collect::<Vec<_>>();
    let result_polynomials = compute_p_i(n, &a, &l);

    for (index, poly) in result_polynomials.iter().enumerate() {
        println!("p_{}(x) = {}", index, poly.coeffs.iter()
                 .enumerate()
                 .map(|(i, &coeff)| format!("{}x^{}", coeff, i))
                 .collect::<Vec<_>>()
                 .join(" + "));
    }

    let l_bool = vec![true, false, true];
    let result_polynomials_dp = compute_pi_dp(&a, &l_bool);
    // for (index, poly) in result_polynomials_dp.iter().enumerate() {
    //     println!("p_{}(x) = {}", index, poly.coeffs.iter()
    //              .enumerate()
    //              .map(|(i, &coeff)| format!("{}x^{}", coeff, i))
    //              .collect::<Vec<_>>()
    //              .join(" + "));
    // }
}
