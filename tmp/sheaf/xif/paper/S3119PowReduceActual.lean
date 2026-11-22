import tmp.sheaf.xif.paper.S3119YDecompositionActual
import tmp.sheaf.xif.paper.S3119NegInvolutionCoreActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
open LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
open LeanFormal.IUT.XiFPaper.S3119YDecompositionActual
namespace LeanFormal.IUT.XiFPaper.S3119PowReduceActual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
variable {l : PrimeGeFive}

theorem S3119_curve_relation (l : PrimeGeFive) :
    S3119y0 (l := l) ^ 2 + S3119x0 (l := l) * S3119y0 (l := l) =
      S3119x0 (l := l) ^ 3 +
        algebraMap (S1348K l) (S1348CoordinateRing l) (5 : S1348K l) := by
  have hp : S1348AffinePolynomial l =
      MvPolynomial.X 1 ^ 2 +
        MvPolynomial.C (1 : S1348K l) * MvPolynomial.X 0 * MvPolynomial.X 1 -
        (MvPolynomial.X 0 ^ 3 + MvPolynomial.C (5 : S1348K l)) := by
    simp [S1348AffinePolynomial, weierstrassAffinePolynomial,
      S3119_curve_a1, S3119_curve_a2, S3119_curve_a3, S3119_curve_a4, S3119_curve_a6]
  have hzero' : Ideal.Quotient.mk (Ideal.span {S1348AffinePolynomial l})
      (MvPolynomial.X 1 ^ 2 +
        MvPolynomial.C (1 : S1348K l) * MvPolynomial.X 0 * MvPolynomial.X 1 -
        (MvPolynomial.X 0 ^ 3 + MvPolynomial.C (5 : S1348K l))) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [← hp]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hsub : S3119y0 (l := l) ^ 2 + S3119x0 (l := l) * S3119y0 (l := l) -
      (S3119x0 (l := l) ^ 3 + (5 : S1348CoordinateRing l)) = 0 := by
    simpa [S3119x0, S3119y0, map_add, map_sub, map_mul, map_pow, map_ofNat] using hzero'
  have h' : S3119y0 (l := l) ^ 2 + S3119x0 (l := l) * S3119y0 (l := l) =
      S3119x0 (l := l) ^ 3 + (5 : S1348CoordinateRing l) :=
    sub_eq_zero.mp hsub
  have h5 : algebraMap (S1348K l) (S1348CoordinateRing l) (5 : S1348K l) =
      (5 : S1348CoordinateRing l) := by
    change (algebraMap (S1348K l) (S1348CoordinateRing l)) ((5 : ℕ) : S1348K l) =
      ((5 : ℕ) : S1348CoordinateRing l)
    exact map_natCast (algebraMap (S1348K l) (S1348CoordinateRing l)) 5
  rw [h5]
  exact h'

noncomputable def S3119PowReduce (l : PrimeGeFive)
    (A B : Polynomial (K l)) : ℕ → Polynomial (K l) × Polynomial (K l)
  | 0 => (1, 0)
  | n + 1 =>
    let R := S3119PowReduce l A B n
    ( R.1 * A + R.2 * B * (Polynomial.X ^ 3 + Polynomial.C (5 : K l)),
      R.1 * B + R.2 * A - R.2 * B * Polynomial.X )

noncomputable def S3119PolyP (l : PrimeGeFive)
    (A B p : Polynomial (K l)) : Polynomial (K l) :=
  p.sum fun n c => Polynomial.C c * (S3119PowReduce l A B n).1

noncomputable def S3119PolyQ (l : PrimeGeFive)
    (A B p : Polynomial (K l)) : Polynomial (K l) :=
  p.sum fun n c => Polynomial.C c * (S3119PowReduce l A B n).2

def S3119PowReduceSpecTarget (l : PrimeGeFive) : Prop :=
  ∀ (A B : Polynomial (K l)) (n : ℕ),
    (S3119Kx0 (l := l) A + S3119Kx0 (l := l) B * S3119y0 (l := l)) ^ n =
      S3119Kx0 (l := l) (S3119PowReduce l A B n).1 +
        S3119Kx0 (l := l) (S3119PowReduce l A B n).2 * S3119y0 (l := l)

theorem S3119PowReduce_spec (l : PrimeGeFive) :
    S3119PowReduceSpecTarget (l := l) := by
  intro A B n
  induction n with
  | zero =>
    simp [S3119PowReduce, S3119Kx0]
  | succ n ih =>
    rw [pow_succ, ih, S3119PowReduce]
    have h5 : algebraMap (S1348K l) (S1348CoordinateRing l) (5 : S1348K l) =
        (5 : S1348CoordinateRing l) := by
      change (algebraMap (S1348K l) (S1348CoordinateRing l))
          ((5 : ℕ) : S1348K l) = ((5 : ℕ) : S1348CoordinateRing l)
      exact map_natCast (algebraMap (S1348K l) (S1348CoordinateRing l)) 5
    have hy2 : S3119y0 (l := l) ^ 2 =
        -S3119x0 (l := l) * S3119y0 (l := l) + S3119x0 (l := l) ^ 3 +
          (5 : S1348CoordinateRing l) := by
      have h := S3119_curve_relation (l := l)
      rw [h5] at h
      linear_combination h
    simp only [S3119Kx0, Polynomial.aeval_add, Polynomial.aeval_sub,
      Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      map_pow, map_one, map_zero]
    ring_nf
    rw [hy2]
    ring_nf
    rw [h5]
    ring_nf

lemma S3119_aeval_monomial (l : PrimeGeFive)
    (A B : Polynomial (K l)) (c : K l) (n : ℕ) :
    Polynomial.aeval (S3119Kx0 (l := l) A + S3119Kx0 (l := l) B * S3119y0 (l := l))
        (Polynomial.C c * Polynomial.X ^ n) =
      S3119Kx0 (l := l) (Polynomial.C c * (S3119PowReduce l A B n).1) +
        S3119Kx0 (l := l) (Polynomial.C c * (S3119PowReduce l A B n).2) *
          S3119y0 (l := l) := by
  rw [map_mul, map_pow]
  simp only [Polynomial.aeval_C, Polynomial.aeval_X]
  rw [S3119PowReduce_spec (l := l) A B n]
  simp only [S3119Kx0, Polynomial.aeval_C, map_mul]
  ring_nf

theorem S3119Poly_spec (l : PrimeGeFive)
    (A B p : Polynomial (K l)) :
    Polynomial.aeval (S3119Kx0 (l := l) A +
        S3119Kx0 (l := l) B * S3119y0 (l := l)) p =
      S3119Kx0 (l := l) (S3119PolyP l A B p) +
        S3119Kx0 (l := l) (S3119PolyQ l A B p) * S3119y0 (l := l) := by
  conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow p]
  rw [map_sum, S3119PolyP, S3119PolyQ, Polynomial.sum, Polynomial.sum]
  simp only [S3119Kx0, map_sum]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact S3119_aeval_monomial (l := l) A B (p.coeff n) n

#check S3119Poly_spec
#print axioms S3119Poly_spec
#check S3119_aeval_monomial
#check S3119PowReduce_spec
#print axioms S3119PowReduce_spec
#check S3119PowReduce
#check S3119PolyP
#check S3119PolyQ
#check S3119PowReduceSpecTarget
end LeanFormal.IUT.XiFPaper.S3119PowReduceActual
end
