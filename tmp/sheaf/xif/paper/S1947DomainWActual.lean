/-
# S1947: the homogeneous coordinate ring of the projective closure is a domain

S1937 reduced the density residual `S1925DenseChart` of the projective closure of the
actual S1726 affine model to the single algebraic statement

    S1937DenseChart_of_domain : IsDomain W → S1925DenseChart,

where

    W = F'[X,Y,Z]/(Wang),
    Wang = Y^2 Z - (X^3 + (61/64) X^2 Z - (125/64) X Z^2)
         = Y^2 Z - X (X - Z) (X + (125/64) Z).

The present file proves `IsDomain W` unconditionally, hence removes the second missing
datum of S1937 and yields the density of the affine chart.

## Proof

View `Wang` as a polynomial in `X` with coefficients in `F'[Y,Z]`.  After the
algebra equivalence `MvPolynomial.finSuccEquiv`,

    -Wang = X^3 + (61/64) Z X^2 - (125/64) Z^2 X - Y^2 Z.

The right-hand side is monic in `X`, and it is Eisenstein at the prime ideal `(Z)` of
`F'[Y,Z]`: the leading coefficient `1` is not divisible by `Z`, all lower
coefficients are divisible by `Z`, and the constant coefficient `-Y^2 Z` is not
divisible by `Z^2`.  Eisenstein's criterion (Mathlib's
`Polynomial.IsEisensteinAt.irreducible`) therefore gives the irreducibility of
`Wang`, first after the algebra equivalence `finSuccEquiv`, then in `F'[X,Y,Z]`.
Since a multivariate polynomial ring over a field is a UFD, `Wang` is prime, so the
principal ideal `(Wang)` is prime and the quotient `W` is a domain.

Nothing is assumed: no axiom, no `sorry`, and no additional hypothesis is introduced.

## Main results

* `S1947WangPoly_isEisenstein` : the monic cubic presentation of `-Wang` is Eisenstein
  at `(Z)`.
* `S1947Wang_irreducible` : `Irreducible Wang`.
* `S1947Wang_prime` : `Prime Wang`.
* `S1947_isDomain_W` : `IsDomain W`.
* `S1947DenseChart` : the density residual `S1925DenseChart` of S1925, now
  unconditional.
-/

import tmp.sheaf.xif.paper.S1936GradedResidualActual
import tmp.sheaf.xif.paper.S1937ProjectiveClosureGeometryActual
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1947DomainWActual

open MvPolynomial
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1925ProjectiveClosureActual
open LeanFormal.IUT.XiFPaper.S1937ProjectiveClosureGeometryActual

/-! ## 1. `Wang` as a monic cubic in `X` over `F'[Y,Z]` -/

/-- The coefficient ring `F'[Y,Z]`, with the two variable indices of the ambient
`Fin 3` presentation. -/
abbrev S1947CoeffRing : Type := MvPolynomial (Fin 2) S1726K

/-- The variable `Y` of the ambient presentation (`X 1` in `Fin 3`), used as the
first variable of the coefficient ring. -/
abbrev S1947Y : S1947CoeffRing := MvPolynomial.X 0

/-- The variable `Z` of the ambient presentation (`X 2` in `Fin 3`), used as the
second variable of the coefficient ring and as the Eisenstein prime. -/
abbrev S1947Z : S1947CoeffRing := MvPolynomial.X 1

/-- The monic cubic in `X = X 0` over `F'[Y,Z]` whose negative is the image of
`Wang` under `MvPolynomial.finSuccEquiv`. -/
def S1947WangPoly : Polynomial S1947CoeffRing :=
  Polynomial.X ^ 3 +
    Polynomial.C (MvPolynomial.C (61 / 64 : S1726K) * S1947Z) *
      Polynomial.X ^ 2 +
    Polynomial.C (MvPolynomial.C (-125 / 64 : S1726K) * S1947Z ^ 2) *
      Polynomial.X -
    Polynomial.C (S1947Y ^ 2 * S1947Z)

@[simp]
theorem S1947WangPoly_coeff_zero :
    S1947WangPoly.coeff 0 = -(S1947Y ^ 2 * S1947Z) := by
  unfold S1947WangPoly
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_one,
    Polynomial.coeff_zero]
  norm_num

@[simp]
theorem S1947WangPoly_coeff_one :
    S1947WangPoly.coeff 1 =
      MvPolynomial.C (-125 / 64 : S1726K) * S1947Z ^ 2 := by
  unfold S1947WangPoly
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_one,
    Polynomial.coeff_zero]
  norm_num

@[simp]
theorem S1947WangPoly_coeff_two :
    S1947WangPoly.coeff 2 =
      MvPolynomial.C (61 / 64 : S1726K) * S1947Z := by
  unfold S1947WangPoly
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_one,
    Polynomial.coeff_zero]
  norm_num

@[simp]
theorem S1947WangPoly_coeff_three : S1947WangPoly.coeff 3 = 1 := by
  unfold S1947WangPoly
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X, Polynomial.coeff_one,
    Polynomial.coeff_zero]
  norm_num

/-- The monic cubic presentation is monic. -/
theorem S1947WangPoly_monic : S1947WangPoly.Monic := by
  unfold S1947WangPoly
  monicity!

/-- The monic cubic presentation has degree three. -/
theorem S1947WangPoly_natDegree : S1947WangPoly.natDegree = 3 := by
  unfold S1947WangPoly
  compute_degree!

/-- **The monic cubic presentation is the negative of the `finSuccEquiv` image of
`Wang`.** -/
theorem S1947Wang_finSucc :
    MvPolynomial.finSuccEquiv S1726K 2 Wang = -S1947WangPoly := by
  have hC : ∀ c : S1726K,
      MvPolynomial.finSuccEquiv S1726K 2 (MvPolynomial.C c) =
        Polynomial.C (MvPolynomial.C c) := by
    intro c
    simpa [MvPolynomial.algebraMap_eq] using
      (MvPolynomial.finSuccEquiv S1726K 2).commutes c
  simp only [Wang]
  rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl,
    show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl]
  simp only [map_sub, map_add, map_mul, map_pow, map_one,
    MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ, hC]
  simp only [S1947WangPoly, S1947Y, S1947Z, Polynomial.C_mul, Polynomial.C_pow]
  ring_nf

/-! ## 2. Eisenstein at the prime `(Z)` -/

/-- The ideal `(Z)` of the coefficient ring `F'[Y,Z]` is prime. -/
theorem S1947PrimeIdeal :
    (Ideal.span ({S1947Z} : Set S1947CoeffRing)).IsPrime := by
  have hZne : S1947Z ≠ 0 := MvPolynomial.X_ne_zero 1
  exact (Ideal.span_singleton_prime hZne).mpr
    (MvPolynomial.X_prime (i := (1 : Fin 2)))

/-- **Eisenstein's criterion at `(Z)`.**  The monic cubic presentation of `Wang` is
Eisenstein at the prime `(Z)`: the leading coefficient is `1`, all lower
coefficients are multiples of `Z`, and the constant coefficient `-Y^2 Z` is not a
multiple of `Z^2`. -/
theorem S1947WangPoly_isEisenstein :
    S1947WangPoly.IsEisensteinAt
      (Ideal.span ({S1947Z} : Set S1947CoeffRing)) := by
  refine Polynomial.Monic.isEisensteinAt_of_mem_of_notMem S1947WangPoly_monic
    S1947PrimeIdeal.ne_top ?_ ?_
  · intro n hn
    rw [S1947WangPoly_natDegree] at hn
    interval_cases n
    · rw [S1947WangPoly_coeff_zero, Ideal.mem_span_singleton]
      exact ⟨-(S1947Y ^ 2), by ring⟩
    · rw [S1947WangPoly_coeff_one, Ideal.mem_span_singleton]
      exact ⟨MvPolynomial.C (-125 / 64 : S1726K) * S1947Z, by ring⟩
    · rw [S1947WangPoly_coeff_two, Ideal.mem_span_singleton]
      exact ⟨MvPolynomial.C (61 / 64 : S1726K), by ring⟩
  · rw [S1947WangPoly_coeff_zero, Ideal.span_singleton_pow]
    intro hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hZne : S1947Z ≠ 0 := MvPolynomial.X_ne_zero 1
    have hZprime : Prime S1947Z := MvPolynomial.X_prime
    have hcancel : S1947Z * (S1947Z * c) = S1947Z * (-(S1947Y ^ 2)) := by
      calc
        S1947Z * (S1947Z * c) = S1947Z ^ 2 * c := by ring
        _ = -(S1947Y ^ 2 * S1947Z) := hc.symm
        _ = S1947Z * (-(S1947Y ^ 2)) := by ring
    have hc' : S1947Z * c = -(S1947Y ^ 2) := mul_left_cancel₀ hZne hcancel
    have hdvd : S1947Z ∣ S1947Y ^ 2 := ⟨-c, by rw [mul_neg, hc', neg_neg]⟩
    have hdvdY : S1947Z ∣ S1947Y := hZprime.dvd_of_dvd_pow hdvd
    have hbad : (1 : Fin 2) = 0 :=
      (MvPolynomial.X_dvd_X (R := S1726K) (i := (1 : Fin 2)) (j := (0 : Fin 2))).mp
        hdvdY
    exact one_ne_zero hbad

/-! ## 3. Irreducibility and primality of `Wang` -/

/-- The monic cubic presentation is irreducible, by Eisenstein's criterion. -/
theorem S1947WangPoly_irreducible : Irreducible S1947WangPoly :=
  S1947WangPoly_isEisenstein.irreducible S1947PrimeIdeal
    (Polynomial.Monic.isPrimitive S1947WangPoly_monic)
    (by rw [S1947WangPoly_natDegree]; norm_num)

/-- **`Wang` is irreducible in `F'[X,Y,Z]`.** -/
theorem S1947Wang_irreducible : Irreducible Wang := by
  have hIrredNeg : Irreducible (-S1947WangPoly) :=
    (Associated.rfl : Associated S1947WangPoly S1947WangPoly).neg_right.irreducible
      S1947WangPoly_irreducible
  have hIrredFinSucc :
      Irreducible (MvPolynomial.finSuccEquiv S1726K 2 Wang) := by
    rw [S1947Wang_finSucc]
    exact hIrredNeg
  have hiff :
      Irreducible (MvPolynomial.finSuccEquiv S1726K 2 Wang) ↔ Irreducible Wang :=
    MulEquiv.irreducible_iff
      (f := (MvPolynomial.finSuccEquiv S1726K 2 :
        MvPolynomial (Fin 3) S1726K ≃* Polynomial S1947CoeffRing))
  exact hiff.mp hIrredFinSucc

/-- **`Wang` is prime.**  A multivariate polynomial ring over a field is a UFD, and in
a UFD irreducible elements are prime. -/
theorem S1947Wang_prime : Prime Wang :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp S1947Wang_irreducible

/-- The principal ideal `(Wang)` is prime. -/
theorem S1947Wang_ideal_prime : (Ideal.span {Wang}).IsPrime :=
  (Ideal.span_singleton_prime Wang_ne_zero).mpr S1947Wang_prime

/-! ## 4. The homogeneous coordinate ring is a domain and the chart is dense -/

/-- **The homogeneous coordinate ring `W = F'[X,Y,Z]/(Wang)` is a domain.** -/
theorem S1947_isDomain_W : IsDomain W := by
  have h : IsDomain (MvPolynomial (Fin 3) S1726K ⧸ Ideal.span {Wang}) :=
    (Ideal.Quotient.isDomain_iff_prime (Ideal.span {Wang})).mpr S1947Wang_ideal_prime
  exact h

/-- **The affine chart `D_+(Z)` is dense in the projective closure.**  This is the
second missing datum of S1925/S1937, now unconditional (the first missing chart
identification is not addressed here). -/
theorem S1947DenseChart : S1925DenseChart :=
  S1937DenseChart_of_domain S1947_isDomain_W

/-! ## 5. Axiom audit -/

#print axioms S1947WangPoly_coeff_zero
#print axioms S1947WangPoly_monic
#print axioms S1947WangPoly_natDegree
#print axioms S1947Wang_finSucc
#print axioms S1947PrimeIdeal
#print axioms S1947WangPoly_isEisenstein
#print axioms S1947WangPoly_irreducible
#print axioms S1947Wang_irreducible
#print axioms S1947Wang_prime
#print axioms S1947Wang_ideal_prime
#print axioms S1947_isDomain_W
#print axioms S1947DenseChart

end LeanFormal.IUT.XiFPaper.S1947DomainWActual
