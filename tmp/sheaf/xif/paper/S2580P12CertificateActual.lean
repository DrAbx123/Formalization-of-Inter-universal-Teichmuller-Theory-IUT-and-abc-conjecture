/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2579Kummer613Actual

/-!
# S2580: the explicit degree-twelve polynomial of theta = a*y + i

This file treats the certificate recorded in
tmp.sheaf.xif.paper.S2579Kummer613Actual:

  S2579P12Certificate : minpoly Z S2579Theta = S2579P12

## What is proved here (all unconditional, no sorry/axiom)

* S2579Hmonic is the even sextic f(X^2) for an explicit cubic f (S2580Hmonic_eq);
* the explicit degree-six polynomial S2580G satisfies S2580G = aT^2 + X * bT^2
  (S2580G_eq) and S2579P12 = S2580G.comp (X^2) (S2579P12_eq_comp);
* S2580_aeval_candidate : aeval (a*y + i) S2579P12 = 0, hence
  S2580_aeval_Theta : aeval S2579Theta S2579P12 = 0;
* S2580_minpoly_dvd : minpoly Z S2579Theta divides S2579P12, the minimal polynomial
  is monic (S2580_minpoly_monic) of degree at most twelve
  (S2580_minpoly_natDegree_le), and equals S2579P12 iff its degree is twelve
  (S2580_certificate_iff); the certificate is in turn equivalent to the
  irreducibility of S2579P12 over Q (S2580_certificate_iff_irreducible);
* S2580G613_eq and S2579P12_mod613_eq: modulo 613 the polynomial S2579P12 is the
  product of the twelve linear factors (X - 21)(X - 49)(X - 154)(X - 199)(X - 224)
  (X - 269)(X + 21)(X + 49)(X + 154)(X + 199)(X + 224)(X + 269);
* S2580LinearFactor613 : S2579LinearFactor613, i.e. the minimal polynomial of
  S2579Theta has a root in ZMod 613.  This is the linear-factor input consumed by
  S2579_prime613_of_arithmetic.

## Method of the computation of aeval S2579Theta S2579P12 = 0

Let f(T) = T^3 + A T^2 + B T + C with the integral coefficients of the sextic,
so that S2579Hmonic = f(X^2), and put z = a*y, i = S2579I, theta = z + i.
Taylor expansion of the cubic at s = theta^2 - 1 in the direction v = -2*i*theta
gives

  f(s + v) = f(s) + f'(s) v + (3 s + A) v^2 + v^3
           = [f(s) - 4 theta^2 (3 s + A)] + i [8 theta^3 - 2 theta (3 s^2 + 2 A s + B)],

and s + v = (theta - i)^2 = z^2, so the left hand side is
aeval (z^2) f = aeval z (f(X^2)) = aeval z S2579Hmonic = 0.
The two brackets are exactly aeval (theta^2) aT and aeval (theta^2) bT, so
aT(t) + i theta bT(t) = 0 with t = theta^2, and therefore
P12(theta) = G(t) = aT(t)^2 + t bT(t)^2 = 0.
The identity S2579P12 = G(X^2) = aT(X^2)^2 + X^2 bT(X^2)^2 is the integral
polynomial identity S2580G_eq, checked coefficientwise.

## What remains (not proved here)

1. The certificate S2579P12Certificate itself.  By S2580_certificate_iff_irreducible
   it is equivalent to the irreducibility of S2579P12 over Q, which is TRUE
   (verified externally) but is not proved here.  Reduction modulo a prime cannot
   prove it: every automorphism of the splitting field F' = F(i) maps
   i to +-i and hence preserves the six pairs {a*y_j + i, a*y_j - i} of roots of
   S2579P12 (these are exactly the pairs whose difference is +-2i).  Therefore the
   Galois group is contained in the wreath product S_2 wr S_6 and contains no
   12-cycle, so by Dedekind's theorem S2579P12 has reducible reduction modulo
   EVERY prime (this was also checked externally for all primes below 300).
   A proof must therefore be algebraic: for example via the Galois-theoretic
   degree computation [Q(theta):Q] = 12 (theta generates F(i) over Q because its
   stabilizer under Gal(F'/Q) = Gal(F/Q) x {1, iota} is trivial), together with
   the identification of the product of the twelve conjugates of theta with
   S2579P12 = S2580G(X^2).
2. S2579Conductor613 : 613 does not divide RingOfIntegers.exponent S2579Theta.
   The external computation gives disc(S2579P12) = 403 mod 613; the missing
   Mathlib ingredient is the relation between the conductor exponent, the index
   [O_F' : Z[theta]] and the discriminant (disc(O_F') * index^2 = disc(theta)),
   so this is left open.
3. S2579Primitive follows from 1. but is not formalised.

No sorry, axiom, True/PUnit gate or native_decide is used.
-/

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2580P12CertificateActual

open LeanFormal.IUT.XiFPaper.S2579Kummer613Actual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual

local instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

/-! ## 1. The sextic as f(X^2) -/

/-- The coefficient of T^2 in the cubic f. -/
def S2580A : ℤ := 3973952045056 * 463856467968

/-- The coefficient of T^1 in the cubic f. -/
def S2580B : ℤ := 1991485440000 * 463856467968 ^ 3

/-- The constant coefficient of the cubic f. -/
def S2580CC : ℤ := 6153500390625 * 463856467968 ^ 5

/-- The cubic f with S2579Hmonic = f(X^2). -/
def S2580f : ℤ[X] := X ^ 3 + C S2580A * X ^ 2 + C S2580B * X + C S2580CC

theorem S2580Hmonic_eq : S2579Hmonic = S2580f.comp (X ^ 2) := by
  unfold S2579Hmonic S2580f S2580A S2580B S2580CC
  simp only [add_comp, mul_comp, pow_comp, C_comp, X_comp]
  norm_num
  ring

/-! ## 2. The even decomposition of the degree-twelve polynomial -/

/-- The cubic aT with A'(X) = aT(X^2), where A' is the real part of
S2579Hmonic(X - i). -/
def S2580aT : ℤ[X] :=
  X ^ 3 + C 1843343359493886556766193 * X ^ 2 +
    C 198759541288399625960719992183022055152001482767 * X +
    C 132141829763228311302713160126471762220607256944797929091168996014686207

/-- The quadratic bT with B'(X) = X * bT(X^2), where B' is the imaginary
part of S2579Hmonic(X - i). -/
def S2580bT : ℤ[X] :=
  C (-6) * X ^ 2 + C (-7373373437975546227064812) * X +
    C (-397519082576799251921454731112920061396457095174)

/-- The degree-six polynomial G with S2579P12 = G(X^2). -/
def S2580G : ℤ[X] :=
  X ^ 6 + C 3686686718987773113532422 * X ^ 5 +
    C 3795433823567007142194129160326239797448395456527 * X ^ 4 +
    C 997047820666501462053751168487623450855112506104272112674336787438501908 * X ^ 3 +
    C 526670884064012082338601412686825197828814168607551341522761345584496744723849057857765220810767 * X ^ 2 +
    C 52528898937498104220425280396744414010535592369189759840509931021767640039634491648742817305763558849812346150540279814 * X +
    C 17461463173174011582761234456954928886602725098127406596813431452619322589360189151409387505478783853884785910317333751256475494692028676046849

/-- G is aT^2 + X * bT^2. -/
theorem S2580G_eq : S2580G = S2580aT * S2580aT + X * (S2580bT * S2580bT) := by
  ext k
  by_cases hk : k ≤ 6
  · interval_cases k <;>
      (simp [S2580G, S2580aT, S2580bT, coeff_add, coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, coeff_C, coeff_X_pow, coeff_X, coeff_one] <;> norm_num)
  · have h1 : S2580G.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      unfold S2580G
      compute_degree!
      omega
    have h3 : S2580aT.natDegree ≤ 3 := by unfold S2580aT; compute_degree!
    have h2 : (S2580aT * S2580aT).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h4 : (S2580aT * S2580aT).natDegree ≤ 6 := by
        calc (S2580aT * S2580aT).natDegree ≤ S2580aT.natDegree + S2580aT.natDegree :=
              natDegree_mul_le
          _ ≤ 6 := by omega
      omega
    have h6 : S2580bT.natDegree ≤ 2 := by unfold S2580bT; compute_degree!
    have h5 : (X * (S2580bT * S2580bT) : ℤ[X]).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h7 : (S2580bT * S2580bT).natDegree ≤ 4 := by
        calc (S2580bT * S2580bT).natDegree ≤ S2580bT.natDegree + S2580bT.natDegree :=
              natDegree_mul_le
          _ ≤ 4 := by omega
      have h8 : (X * (S2580bT * S2580bT) : ℤ[X]).natDegree ≤ 5 := by
        calc (X * (S2580bT * S2580bT) : ℤ[X]).natDegree
            ≤ (X : ℤ[X]).natDegree + (S2580bT * S2580bT).natDegree := natDegree_mul_le
          _ ≤ 5 := by rw [natDegree_X]; omega
      omega
    rw [h1, coeff_add, h2, h5, add_zero]

/-- S2579P12 is G(X^2). -/
theorem S2579P12_eq_comp : S2579P12 = S2580G.comp (X ^ 2) := by
  unfold S2579P12 S2580G
  simp only [add_comp, mul_comp, pow_comp, C_comp, X_comp]
  norm_num
  ring

/-- The numeric relation c4 = A - 15. -/
theorem S2580c4 : (1843343359493886556766193 : ℤ) = S2580A - 15 := by
  unfold S2580A; norm_num

/-- The numeric relation c2 = B + 15 - 6 A. -/
theorem S2580c2 :
    (198759541288399625960719992183022055152001482767 : ℤ) = S2580B + 15 - 6 * S2580A := by
  unfold S2580A S2580B; norm_num

/-- The numeric relation c0 = A - B + C - 1. -/
theorem S2580c0 :
    (132141829763228311302713160126471762220607256944797929091168996014686207 : ℤ) =
      S2580A - S2580B + S2580CC - 1 := by
  unfold S2580A S2580B S2580CC; norm_num

/-- The numeric relation b1 = 20 - 4 A. -/
theorem S2580b1 : (-7373373437975546227064812 : ℤ) = 20 - 4 * S2580A := by
  unfold S2580A; norm_num

/-- The numeric relation b0 = 4 A - 2 B - 6. -/
theorem S2580b0 :
    (-397519082576799251921454731112920061396457095174 : ℤ) = 4 * S2580A - 2 * S2580B - 6 := by
  unfold S2580A S2580B; norm_num

/-! ## 3. The field computation in F' = S1720Field -/

/-- The Taylor form of the cubic f at s in the direction v. -/
theorem S2580_taylor (s v : S1720Field) :
    aeval (s + v) S2580f =
      aeval s S2580f + (3 * s ^ 2 + 2 * algebraMap ℤ S1720Field S2580A * s + algebraMap ℤ S1720Field S2580B) * v +
        (3 * s + algebraMap ℤ S1720Field S2580A) * v ^ 2 + v ^ 3 := by
  simp only [S2580f, map_add, map_mul, map_pow, aeval_X, aeval_C, aeval_X_pow]
  ring

/-- The value of aT at theta^2, in terms of f. -/
theorem S2580_val_aT :
    aeval (S2579Candidate ^ 2) S2580aT =
      aeval (S2579Candidate ^ 2 - 1) S2580f -
        4 * S2579Candidate ^ 2 * (3 * (S2579Candidate ^ 2 - 1) + algebraMap ℤ S1720Field S2580A) := by
  have e4 : algebraMap ℤ S1720Field (1843343359493886556766193 : ℤ) = algebraMap ℤ S1720Field S2580A - 15 := by
    have h : (1843343359493886556766193 : ℤ) = S2580A - 15 := S2580c4
    rw [h]; push_cast; norm_num
  have e2 : algebraMap ℤ S1720Field (198759541288399625960719992183022055152001482767 : ℤ) =
      algebraMap ℤ S1720Field S2580B + 15 - 6 * algebraMap ℤ S1720Field S2580A := by
    have h : (198759541288399625960719992183022055152001482767 : ℤ) = S2580B + 15 - 6 * S2580A :=
      S2580c2
    rw [h]; push_cast; norm_num
  have e0 : algebraMap ℤ S1720Field (132141829763228311302713160126471762220607256944797929091168996014686207 : ℤ) =
      algebraMap ℤ S1720Field S2580A - algebraMap ℤ S1720Field S2580B + algebraMap ℤ S1720Field S2580CC - 1 := by
    have h : (132141829763228311302713160126471762220607256944797929091168996014686207 : ℤ) =
        S2580A - S2580B + S2580CC - 1 := S2580c0
    rw [h]; push_cast; norm_num
  simp only [S2580aT, S2580f, map_add, map_mul, map_pow, aeval_X, aeval_C, aeval_X_pow]
  rw [e4, e2, e0]
  ring

/-- The value of bT at theta^2, in terms of f. -/
theorem S2580_val_bT :
    aeval (S2579Candidate ^ 2) S2580bT =
      8 * S2579Candidate ^ 2 -
        2 * (3 * (S2579Candidate ^ 2 - 1) ^ 2 + 2 * algebraMap ℤ S1720Field S2580A * (S2579Candidate ^ 2 - 1) +
          algebraMap ℤ S1720Field S2580B) := by
  have f1 : algebraMap ℤ S1720Field (-7373373437975546227064812 : ℤ) = 20 - 4 * algebraMap ℤ S1720Field S2580A := by
    have h : (-7373373437975546227064812 : ℤ) = 20 - 4 * S2580A := S2580b1
    rw [h]; push_cast; norm_num
  have f0 : algebraMap ℤ S1720Field (-397519082576799251921454731112920061396457095174 : ℤ) =
      4 * algebraMap ℤ S1720Field S2580A - 2 * algebraMap ℤ S1720Field S2580B - 6 := by
    have h : (-397519082576799251921454731112920061396457095174 : ℤ) = 4 * S2580A - 2 * S2580B - 6 :=
      S2580b0
    rw [h]; push_cast; norm_num
  simp only [S2580bT, map_add, map_mul, map_pow, aeval_X, aeval_C, aeval_X_pow]
  rw [f1, f0]
  norm_num
  ring

/-- The central vanishing: aT(t) + i * theta * bT(t) = 0 for t = theta^2. -/
theorem S2580_key :
    aeval (S2579Candidate ^ 2) S2580aT +
      S2579I * (S2579Candidate * aeval (S2579Candidate ^ 2) S2580bT) = 0 := by
  have hii : S2579I * S2579I = -1 := S2579I_sq
  have hroot : aeval ((S2579a : S1720Field) * S2579Y) S2579Hmonic = 0 := S2579Hmonic_eval
  have hsub : S2579Candidate - S2579I = (S2579a : S1720Field) * S2579Y := by
    unfold S2579Candidate
    ring
  have hsv : (S2579Candidate ^ 2 - 1) + (-2 * S2579I * S2579Candidate) =
      (S2579Candidate - S2579I) ^ 2 := by
    rw [sub_sq]
    have hsq : S2579I ^ 2 = -1 := by rw [pow_two, hii]
    rw [hsq]
    ring
  have hfv : aeval ((S2579Candidate - S2579I) ^ 2) S2580f = 0 := by
    have hc : aeval (S2579Candidate - S2579I) (S2580f.comp (X ^ 2)) =
        aeval ((S2579Candidate - S2579I) ^ 2) S2580f := by
      rw [aeval_comp, aeval_X_pow]
    rw [← hc, ← S2580Hmonic_eq, hsub]
    exact hroot
  have hzero :
      aeval (S2579Candidate ^ 2 - 1) S2580f +
        (3 * (S2579Candidate ^ 2 - 1) ^ 2 +
          2 * algebraMap ℤ S1720Field S2580A * (S2579Candidate ^ 2 - 1) + algebraMap ℤ S1720Field S2580B) *
          (-2 * S2579I * S2579Candidate) +
        (3 * (S2579Candidate ^ 2 - 1) + algebraMap ℤ S1720Field S2580A) *
          (-2 * S2579I * S2579Candidate) ^ 2 + (-2 * S2579I * S2579Candidate) ^ 3 = 0 := by
    rw [← S2580_taylor (S2579Candidate ^ 2 - 1) (-2 * S2579I * S2579Candidate), hsv, hfv]
  have hv2 : (-2 * S2579I * S2579Candidate) ^ 2 = -4 * S2579Candidate ^ 2 := by
    calc (-2 * S2579I * S2579Candidate) ^ 2
        = 4 * S2579Candidate ^ 2 * (S2579I * S2579I) := by ring
      _ = -4 * S2579Candidate ^ 2 := by rw [hii]; ring
  have hv3 : (-2 * S2579I * S2579Candidate) ^ 3 = 8 * S2579I * S2579Candidate ^ 3 := by
    calc (-2 * S2579I * S2579Candidate) ^ 3
        = (-4 * S2579Candidate ^ 2) * (-2 * S2579I * S2579Candidate) := by
          rw [← hv2]; ring
      _ = 8 * S2579I * S2579Candidate ^ 3 := by ring
  have hz := hzero
  rw [hv2, hv3] at hz
  rw [S2580_val_aT, S2580_val_bT]
  linear_combination hz

/-- S2579P12 vanishes at the candidate a * S1687Y + i. -/
theorem S2580_aeval_candidate : aeval S2579Candidate S2579P12 = 0 := by
  have hii : S2579I * S2579I = -1 := S2579I_sq
  have hP : aeval S2579Candidate S2579P12 = aeval (S2579Candidate ^ 2) S2580G := by
    rw [S2579P12_eq_comp, aeval_comp, aeval_X_pow]
  have hG : aeval (S2579Candidate ^ 2) S2580G =
      (aeval (S2579Candidate ^ 2) S2580aT) ^ 2 +
        S2579Candidate ^ 2 * (aeval (S2579Candidate ^ 2) S2580bT) ^ 2 := by
    rw [S2580G_eq]
    simp only [map_add, map_mul, map_pow, aeval_X]
    ring
  have hkey := S2580_key
  have hA : aeval (S2579Candidate ^ 2) S2580aT =
      -(S2579I * (S2579Candidate * aeval (S2579Candidate ^ 2) S2580bT)) := by
    linear_combination hkey
  rw [hP, hG]
  calc (aeval (S2579Candidate ^ 2) S2580aT) ^ 2 +
        S2579Candidate ^ 2 * (aeval (S2579Candidate ^ 2) S2580bT) ^ 2
      = (-(S2579I * (S2579Candidate * aeval (S2579Candidate ^ 2) S2580bT))) ^ 2 +
        S2579Candidate ^ 2 * (aeval (S2579Candidate ^ 2) S2580bT) ^ 2 := by rw [hA]
    _ = 0 := by
        linear_combination (S2579Candidate * aeval (S2579Candidate ^ 2) S2580bT) ^ 2 * hii

/-- S2579P12 vanishes at the algebraic integer S2579Theta. -/
theorem S2580_aeval_Theta : aeval S2579Theta S2579P12 = 0 := by
  have hinj : Function.Injective (algebraMap C S1720Field) := by
    intro x y h
    exact Subtype.ext h
  rw [← Polynomial.aeval_algebraMap_eq_zero_iff_of_injective hinj]
  show aeval (S2579Theta : S1720Field) S2579P12 = 0
  rw [S2579Theta_coe]
  exact S2580_aeval_candidate

/-! ## 4. Consequences for the minimal polynomial -/

theorem S2579P12_monic : S2579P12.Monic := by
  unfold S2579P12
  monicity!

theorem S2579P12_natDegree : S2579P12.natDegree = 12 := by
  unfold S2579P12
  compute_degree!

instance S2580TorsionFree : Module.IsTorsionFree ℤ C := inferInstance

theorem S2580_minpoly_dvd : minpoly ℤ S2579Theta ∣ S2579P12 :=
  minpoly.isIntegrallyClosed_dvd S2579Theta.isIntegral S2580_aeval_Theta

theorem S2580_minpoly_monic : (minpoly ℤ S2579Theta).Monic :=
  minpoly.monic S2579Theta.isIntegral

theorem S2580_minpoly_natDegree_le : (minpoly ℤ S2579Theta).natDegree ≤ 12 := by
  calc (minpoly ℤ S2579Theta).natDegree
      ≤ S2579P12.natDegree := natDegree_le_of_dvd S2580_minpoly_dvd S2579P12_monic.ne_zero
    _ = 12 := S2579P12_natDegree

/-- The minimal polynomial over Q of the element theta of F'. -/
theorem S2580_minpoly_rat :
    minpoly ℚ (S2579Theta : S1720Field) =
      (minpoly ℤ S2579Theta).map (algebraMap ℤ ℚ) :=
  minpoly.isIntegrallyClosed_eq_field_fractions ℚ S1720Field S2579Theta.isIntegral

theorem S2580_minpoly_rat_natDegree :
    (minpoly ℚ (S2579Theta : S1720Field)).natDegree = (minpoly ℤ S2579Theta).natDegree := by
  rw [S2580_minpoly_rat]
  exact Polynomial.natDegree_map_eq_of_injective (f := algebraMap ℤ ℚ) (fun a b h => by
    exact_mod_cast h) _

/-- The certificate is equivalent to the minimal polynomial having degree twelve. -/
theorem S2580_certificate_iff : S2579P12Certificate ↔ (minpoly ℤ S2579Theta).natDegree = 12 := by
  constructor
  · intro h
    rw [S2579P12Certificate] at h
    rw [h, S2579P12_natDegree]
  · intro h
    rw [S2579P12Certificate]
    exact (eq_of_monic_of_dvd_of_natDegree_le S2580_minpoly_monic S2579P12_monic
      S2580_minpoly_dvd (by rw [h, S2579P12_natDegree])).symm


/-! ## 5. The twelve linear factors modulo 613 and the linear residue factor -/

/-- The six roots of `S2580G` modulo 613: the squares of the twelve roots of
`S2579P12` modulo 613. -/
def S2580w : Fin 6 → ZMod 613 := ![441, 562, 422, 369, 523, 27]

/-- Chosen square roots of the six values `S2580w`. -/
def S2580r : Fin 6 → ZMod 613 := ![21, 49, 154, 199, 224, 269]

theorem S2580r_sq (k : Fin 6) : S2580r k * S2580r k = S2580w k := by
  fin_cases k <;> decide

theorem S2580w_injective : Function.Injective S2580w := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (exfalso; revert h; decide)

theorem S2580G_monic : S2580G.Monic := by
  unfold S2580G
  monicity!

theorem S2580G_natDegree : S2580G.natDegree = 6 := by
  unfold S2580G
  compute_degree!

/-- `S2580G` reduced modulo 613. -/
def S2580G613 : (ZMod 613)[X] := S2580G.map (Int.castRingHom (ZMod 613))

theorem S2580G613_monic : S2580G613.Monic :=
  S2580G_monic.map _

theorem S2580G613_natDegree : S2580G613.natDegree = 6 := by
  rw [S2580G613, S2580G_monic.natDegree_map, S2580G_natDegree]

theorem S2580G613_root (k : Fin 6) : S2580G613.IsRoot (S2580w k) := by
  fin_cases k <;>
    (simp [S2580G613, S2580G, S2580w, Polynomial.IsRoot, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
     decide)

/-- The product of the six linear factors of `S2580G` modulo 613 divides it. -/
theorem S2580Q_dvd : (∏ k : Fin 6, (X - C (S2580w k))) ∣ S2580G613 := by
  have hpair : (↑(Finset.univ : Finset (Fin 6)) : Set (Fin 6)).Pairwise
      (Function.onFun IsCoprime (fun k => (X - C (S2580w k)))) := by
    intro a _ b _ hab
    apply isCoprime_X_sub_C_of_isUnit_sub
    rw [isUnit_iff_ne_zero]
    intro hsub
    exact hab (S2580w_injective (sub_eq_zero.mp hsub))
  have hdvd : ∀ k ∈ (Finset.univ : Finset (Fin 6)), (X - C (S2580w k)) ∣ S2580G613 := by
    intro k _
    rw [Polynomial.dvd_iff_isRoot]
    exact S2580G613_root k
  simpa using Finset.prod_dvd_of_coprime hpair hdvd

theorem S2580G613_eq : S2580G613 = ∏ k : Fin 6, (X - C (S2580w k)) := by
  have hQ_monic : (∏ k : Fin 6, (X - C (S2580w k))).Monic :=
    monic_prod_X_sub_C _ _
  have hQ_deg : (∏ k : Fin 6, (X - C (S2580w k))).natDegree = 6 := by
    rw [natDegree_finsetProd_X_sub_C_eq_card]
    simp
  exact eq_of_monic_of_dvd_of_natDegree_le hQ_monic S2580G613_monic S2580Q_dvd
    (by rw [S2580G613_natDegree, hQ_deg])

/-- The full factorisation of `S2579P12` modulo 613 into twelve linear factors. -/
theorem S2579P12_mod613_eq :
    S2579P12.map (Int.castRingHom (ZMod 613)) =
      ∏ k : Fin 6, ((X - C (S2580r k)) * (X + C (S2580r k))) := by
  have hmap : S2579P12.map (Int.castRingHom (ZMod 613)) = S2580G613.comp (X ^ 2) := by
    rw [S2579P12_eq_comp, Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
    rfl
  rw [hmap, S2580G613_eq]
  have hcomp : (∏ k : Fin 6, (X - C (S2580w k))).comp (X ^ 2) =
      ∏ k : Fin 6, ((X - C (S2580w k)).comp (X ^ 2)) := by
    simp only [Polynomial.comp_eq_aeval]
    rw [map_prod]
  rw [hcomp]
  refine Finset.prod_congr rfl ?_
  intro k _
  have hw : C (S2580w k) = C (S2580r k) * C (S2580r k) := by
    rw [← Polynomial.C_mul, ← S2580r_sq k]
  rw [Polynomial.sub_comp, Polynomial.C_comp, Polynomial.X_comp, hw]
  ring

/-- A linear factor gives a root. -/
theorem S2580_root_of_dvd {p : (ZMod 613)[X]} {c : ZMod 613} (h : (X - C c) ∣ p) : p.IsRoot c := by
  obtain ⟨h', rfl⟩ := h
  simp [Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- A monic irreducible divisor of a linear polynomial is that linear polynomial. -/
theorem S2580_eq_linear_of_dvd {g : (ZMod 613)[X]} (hg : g.Monic) (hgirr : Irreducible g)
    {c : ZMod 613} (h : g ∣ X - C c) : g = X - C c := by
  have hle : g.natDegree ≤ 1 := by
    have h1 := natDegree_le_of_dvd h (monic_X_sub_C c).ne_zero
    rwa [natDegree_X_sub_C] at h1
  have hpos : 0 < g.natDegree := hgirr.natDegree_pos
  have h1 : g.natDegree = 1 := by omega
  exact (eq_of_monic_of_dvd_of_natDegree_le hg (monic_X_sub_C c) h
    (by rw [natDegree_X_sub_C]; omega)).symm

/-- `S2579LinearFactor613`: the minimal polynomial of theta has a root modulo 613.

This is proved from the factorisation `S2579P12` into twelve linear factors modulo 613 and
the divisibility `minpoly Z S2579Theta ∣ S2579P12`; the argument is that any monic
irreducible factor of the minimal polynomial modulo 613 divides one of the twelve linear
factors, hence is linear. -/
theorem S2580LinearFactor613 : S2579LinearFactor613 := by
  unfold S2579LinearFactor613
  have hdvd : S2579minpolyMod S2579Theta ∣ S2579P12.map (Int.castRingHom (ZMod 613)) := by
    unfold S2579minpolyMod
    exact Polynomial.map_dvd _ S2580_minpoly_dvd
  rw [S2579P12_mod613_eq] at hdvd
  have hmonic : (S2579minpolyMod S2579Theta).Monic := S2580_minpoly_monic.map _
  have hnotunit : ¬ IsUnit (S2579minpolyMod S2579Theta) := by
    rw [hmonic.isUnit_iff]
    intro h1
    have hdeg : (S2579minpolyMod S2579Theta).natDegree = 0 := by rw [h1]; simp
    have hdeg' : (minpoly ℤ S2579Theta).natDegree = 0 := by
      rw [← S2580_minpoly_monic.natDegree_map (Int.castRingHom (ZMod 613))]
      exact hdeg
    have hpos : 0 < (minpoly ℤ S2579Theta).natDegree := by
      have h := minpoly.degree_pos S2579Theta.isIntegral
      rw [Polynomial.degree_eq_natDegree S2580_minpoly_monic.ne_zero] at h
      exact WithBot.coe_lt_coe.mp h
    omega
  obtain ⟨g, hgmonic, hgirr, hgdvd⟩ := Polynomial.exists_monic_irreducible_factor _ hnotunit
  have hgdvd' : g ∣ ∏ k : Fin 6, ((X - C (S2580r k)) * (X + C (S2580r k))) :=
    hgdvd.trans hdvd
  have hprime : Prime g := hgirr.prime
  obtain ⟨k, _, hk⟩ :=
    (Prime.dvd_finsetProd_iff hprime (fun k : Fin 6 => (X - C (S2580r k)) * (X + C (S2580r k)))).mp
      hgdvd'
  rcases (Prime.dvd_mul hprime).mp hk with hk | hk
  · refine ⟨S2580r k, ?_⟩
    rw [S2580_eq_linear_of_dvd hgmonic hgirr hk] at hgdvd
    exact S2580_root_of_dvd hgdvd
  · have hk' : g ∣ X - C (-(S2580r k)) := by
      rwa [show X - C (-(S2580r k)) = X + C (S2580r k) from by
        rw [Polynomial.C_neg]; ring]
    refine ⟨-(S2580r k), ?_⟩
    rw [S2580_eq_linear_of_dvd hgmonic hgirr hk'] at hgdvd
    exact S2580_root_of_dvd hgdvd


/-! ## 6. The certificate as irreducibility over Q -/

theorem S2579P12_rat_monic : (S2579P12.map (algebraMap ℤ ℚ)).Monic :=
  S2579P12_monic.map _

theorem S2579P12_rat_natDegree : (S2579P12.map (algebraMap ℤ ℚ)).natDegree = 12 := by
  rw [Polynomial.natDegree_map_eq_of_injective (f := algebraMap ℤ ℚ) (fun a b h => by
    exact_mod_cast h), S2579P12_natDegree]

theorem S2580_aeval_Theta_rat :
    aeval (S2579Theta : S1720Field) (S2579P12.map (algebraMap ℤ ℚ)) = 0 := by
  rw [Polynomial.aeval_map_algebraMap, S2579Theta_coe]
  exact S2580_aeval_candidate

/-- The element theta is integral over Q (it is an algebraic integer). -/
theorem S2580_isIntegral_rat : IsIntegral ℚ (S2579Theta : S1720Field) := by
  obtain ⟨P, hPmonic, hP⟩ := S2579Theta.isIntegral
  refine ⟨P.map (algebraMap ℤ ℚ), hPmonic.map _, ?_⟩
  show Polynomial.aeval (S2579Theta : S1720Field) (P.map (algebraMap ℤ ℚ)) = 0
  rw [Polynomial.aeval_map_algebraMap]
  show aeval (algebraMap C S1720Field S2579Theta) P = 0
  rw [Polynomial.aeval_algebraMap_apply, show aeval S2579Theta P = 0 from hP, map_zero]

/-- The certificate is equivalent to the irreducibility of `S2579P12` over Q. -/
theorem S2580_certificate_iff_irreducible :
    S2579P12Certificate ↔ Irreducible (S2579P12.map (algebraMap ℤ ℚ)) := by
  constructor
  · intro h
    have h1 : minpoly ℤ S2579Theta = S2579P12 := h
    have h2 : minpoly ℚ (S2579Theta : S1720Field) = S2579P12.map (algebraMap ℤ ℚ) := by
      rw [S2580_minpoly_rat, h1]
    rw [← h2]
    exact minpoly.irreducible S2580_isIntegral_rat
  · intro hirr
    have h1 : S2579P12.map (algebraMap ℤ ℚ) = minpoly ℚ (S2579Theta : S1720Field) :=
      minpoly.eq_of_irreducible_of_monic hirr S2580_aeval_Theta_rat S2579P12_rat_monic
    have h2 : (minpoly ℚ (S2579Theta : S1720Field)).natDegree = 12 := by
      rw [← h1, S2579P12_rat_natDegree]
    have h3 : (minpoly ℤ S2579Theta).natDegree = 12 := by
      rw [← S2580_minpoly_rat_natDegree, h2]
    exact S2580_certificate_iff.mpr h3

/-! ## 7. Axiom footprint -/

#print axioms S2580Hmonic_eq
#print axioms S2580G_eq
#print axioms S2579P12_eq_comp
#print axioms S2579P12_monic
#print axioms S2580_taylor
#print axioms S2580_val_aT
#print axioms S2580_val_bT
#print axioms S2580_key
#print axioms S2580_aeval_candidate
#print axioms S2580_aeval_Theta
#print axioms S2580_minpoly_dvd
#print axioms S2580_minpoly_natDegree_le
#print axioms S2580_minpoly_rat
#print axioms S2580_certificate_iff
#print axioms S2580G613_eq
#print axioms S2579P12_mod613_eq
#print axioms S2580LinearFactor613
#print axioms S2580_certificate_iff_irreducible
#print axioms S2580_minpoly_rat_natDegree

end LeanFormal.IUT.XiFPaper.S2580P12CertificateActual
