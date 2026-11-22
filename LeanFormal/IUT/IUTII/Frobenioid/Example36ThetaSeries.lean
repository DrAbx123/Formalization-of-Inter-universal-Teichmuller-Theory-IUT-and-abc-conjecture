/-
  # Analytic Jacobi theta series at q = 1/5 and the finite Example 3.6 packet

  Task task-63 of the Group-1 split.  This module uses Mathlib's actual
  one-variable Jacobi theta function (not a replacement) to construct a concrete
  analytic theta series at the concrete q-parameter q = 1/5 of the Example 3.6
  carrier, proves its q-expansion and convergence there, proves its basic
  symmetry/special-value properties, and connects its summands to the finite
  Example 3.6 theta packet where the connection is genuinely available.

  ## What is constructed and proved

  * The normalisation point tau = i log 5 / pi in the upper half plane, where
    q = exp(pi i tau) = gaussianFiveThetaQ = 1/5 (proved), and |q| < 1.
  * The analytic theta value jacobiThetaQ := Mathlib's jacobiTheta tau, with:
    - q-expansion: jacobiThetaQ is the sum over n in Z of qExpansionTerm n,
      where qExpansionTerm n = q ^ (gaussExponent n).toNat, i.e. the classical
      q-series of the Gaussian special values;
    - convergence: the q-expansion is a HasSum and hence summable;
    - symmetry qExpansionTerm (-n) = qExpansionTerm n and the special values
      qExpansionTerm 0 = 1, qExpansionTerm 1 = q;
    - non-vacuity: the explicit bound |jacobiThetaQ - 1| <= 1/2, hence
      jacobiThetaQ != 0 and Re jacobiThetaQ > 0.
  * Genuine connection to the finite Example 3.6 packet: every finite packet
    scale of the concrete source theater is exactly the corresponding summand of
    the analytic q-expansion at q = 1/5:
    ((sourceTheater l).thetaPacket.scale j : C) = qExpansionTerm j.1.

  ## What is NOT provided (frozen card and missing relation)

  * The analytic Jacobi theta series is an actual Mathlib analytic object, but it
    is NOT identified with the source's etale theta function/theta generator, and
    the finite packet is only matched summand-wise, not as the source theta
    evaluation.  The exact missing relation is recorded as the predicate
    missingSourceThetaAnalyticRelation (never assumed or proved).
  * The actual source etale theta generator/theta series carrier and its
    q-expansion are frozen as SourceThetaAnalyticGeneratorCard.  No inhabitant is
    constructed, and the analytic Jacobi theta is not substituted for it.
  * No theta-pilot/q-pilot claim, no Tate or anabelian identification is made.

  Source correspondence: IUT II, theta evaluation and q-expansion; IUT I,
  Definition 3.6 and Corollary 3.7 (theta data of the Theta-Hodge theaters).
-/

import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier
import LeanFormal.IUT.IUTII.Frobenioid.Example36ThetaGeneratorFeasibility

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace ThetaSeries

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open IsDedekindDomain

local instance gaussianPolynomialIrreducibleFactThetaSeries :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactThetaSeries : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance primeFactThetaSeries (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

noncomputable section

/-! ## 1. The normalisation point with q = 1/5 -/

/-- The point tau = i log 5 / pi of the upper half plane, at which the Jacobi
q-parameter exp(pi i tau) equals 1/5. -/
noncomputable def thetaTau : ℂ := ((Real.log 5 / Real.pi : ℝ) : ℂ) * Complex.I

theorem thetaTau_im : thetaTau.im = Real.log 5 / Real.pi := by
  unfold thetaTau
  rw [Complex.mul_im]
  rw [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem thetaTau_im_pos : 0 < thetaTau.im := by
  rw [thetaTau_im]
  positivity

/-- The exponential core: pi i tau = -log 5. -/
theorem thetaTau_core : Real.pi * Complex.I * thetaTau = -(Real.log 5 : ℂ) := by
  unfold thetaTau
  rw [show (Real.log 5 / Real.pi : ℝ) = (Real.log 5 : ℂ) / (Real.pi : ℂ) from by
    push_cast
    ring]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  rw [Complex.I_sq]
  ring

/-- exp(-log 5) is the actual q-parameter gaussianFiveThetaQ. -/
theorem exp_neg_log_five :
    Complex.exp (-(Real.log 5 : ℂ)) = (gaussianFiveThetaQ : ℂ) := by
  rw [gaussianFiveThetaQ_eq_inv_five]
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 5)]

/-- The Jacobi q-parameter at thetaTau is the concrete q = 1/5. -/
theorem thetaTau_exp :
    Complex.exp (Real.pi * Complex.I * thetaTau) = (gaussianFiveThetaQ : ℂ) := by
  rw [thetaTau_core]
  exact exp_neg_log_five

theorem gaussianFiveThetaQ_lt_one : gaussianFiveThetaQ < 1 := by
  rw [gaussianFiveThetaQ_eq_inv_five]
  norm_num

theorem gaussianFiveThetaQ_abs_lt_one : |gaussianFiveThetaQ| < 1 := by
  rw [gaussianFiveThetaQ_eq_inv_five,
    abs_of_pos (by norm_num : (0 : ℝ) < (5 : ℝ)⁻¹)]
  norm_num

theorem thetaTau_exp_neg_pi_im :
    Real.exp (-Real.pi * thetaTau.im) = (1 / 5 : ℝ) := by
  rw [thetaTau_im]
  have h : Real.pi * (Real.log 5 / Real.pi) = Real.log 5 := by
    field_simp
  rw [show -Real.pi * (Real.log 5 / Real.pi) = -Real.log 5 by rw [neg_mul, h]]
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 5)]
  norm_num

/-! ## 2. The analytic Jacobi theta value at q = 1/5 -/

/-- The concrete analytic theta value: Mathlib's one-variable Jacobi theta
function at the point tau with q = 1/5. -/
noncomputable def jacobiThetaQ : ℂ := jacobiTheta thetaTau

/-- The summands of the analytic q-expansion: q ^ (n ^ 2) = q ^ gaussExponent n. -/
noncomputable def qExpansionTerm (n : ℤ) : ℂ :=
  (gaussianFiveThetaQ : ℂ) ^ (gaussExponent n).toNat

/-- Each analytic q-expansion summand is the complexification of the Gaussian
special value realThetaValue. -/
theorem qExpansionTerm_eq_ofReal (n : ℤ) :
    qExpansionTerm n = ((realThetaValue gaussianFiveThetaQ n : ℝ) : ℂ) := by
  unfold qExpansionTerm realThetaValue
  rw [Complex.ofReal_pow]

@[simp] theorem qExpansionTerm_zero : qExpansionTerm 0 = 1 := by
  simp [qExpansionTerm]

@[simp] theorem qExpansionTerm_one :
    qExpansionTerm 1 = (gaussianFiveThetaQ : ℂ) := by
  simp [qExpansionTerm, gaussExponent]

@[simp] theorem qExpansionTerm_neg (n : ℤ) :
    qExpansionTerm (-n) = qExpansionTerm n := by
  simp [qExpansionTerm]

/-- The Mathlib Jacobi series term at thetaTau is exactly the q-expansion
summand with q = 1/5. -/
theorem jacobiTheta_term_eq (n : ℤ) :
    Complex.exp (Real.pi * Complex.I * (n : ℂ) ^ 2 * thetaTau) =
      qExpansionTerm n := by
  have harg : Real.pi * Complex.I * (n : ℂ) ^ 2 * thetaTau =
      ((n ^ 2 : ℤ) : ℂ) * (Real.pi * Complex.I * thetaTau) := by
    push_cast
    ring
  rw [harg, thetaTau_core]
  rw [Complex.exp_int_mul]
  rw [exp_neg_log_five]
  rw [show (n ^ 2 : ℤ) = ((n ^ 2).toNat : ℤ) from
    (Int.toNat_of_nonneg (sq_nonneg n)).symm]
  rw [zpow_natCast]
  rfl

/-- **Convergence.**  The q-expansion is a convergent HasSum at q = 1/5. -/
theorem hasSum_qExpansionTerm :
    HasSum qExpansionTerm jacobiThetaQ := by
  have h := hasSum_jacobiTheta₂_term 0 thetaTau_im_pos
  have h' : HasSum (fun n : ℤ =>
      Complex.exp (Real.pi * Complex.I * (n : ℂ) ^ 2 * thetaTau)) (jacobiTheta thetaTau) := by
    simpa [← jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂_term] using h
  exact h'.congr_fun (fun n => (jacobiTheta_term_eq n).symm)

/-- **Q-expansion.**  The analytic Jacobi theta value at q = 1/5 is the q-series
of the Gaussian special values. -/
theorem jacobiThetaQ_eq_tsum_qExpansionTerm :
    jacobiThetaQ = ∑' n : ℤ, qExpansionTerm n :=
  hasSum_qExpansionTerm.tsum_eq.symm

/-- The q-expansion summands are summable at q = 1/5. -/
theorem summable_qExpansionTerm : Summable qExpansionTerm :=
  hasSum_qExpansionTerm.summable

/-! ## 3. Basic functional and special-value properties -/

/-- **Non-vacuity bound.**  At q = 1/5 the analytic theta value is within 1/2 of
1: |theta - 1| <= 1/2. -/
theorem norm_jacobiThetaQ_sub_one_le :
    ‖jacobiThetaQ - 1‖ ≤ (1 / 2 : ℝ) := by
  have h := norm_jacobiTheta_sub_one_le (τ := thetaTau) thetaTau_im_pos
  rw [thetaTau_exp_neg_pi_im] at h
  norm_num at h
  simpa [jacobiThetaQ] using h

/-- The analytic theta value at q = 1/5 is nonzero. -/
theorem jacobiThetaQ_ne_zero : jacobiThetaQ ≠ 0 := by
  intro h0
  have h1 : ‖jacobiThetaQ - 1‖ = 1 := by
    rw [h0]
    norm_num
  have h2 := norm_jacobiThetaQ_sub_one_le
  rw [h1] at h2
  norm_num at h2

/-- The real part of the analytic theta value at q = 1/5 is positive. -/
theorem jacobiThetaQ_re_pos : 0 < jacobiThetaQ.re := by
  have h := norm_jacobiThetaQ_sub_one_le
  have hre : |(jacobiThetaQ - 1).re| ≤ (1 / 2 : ℝ) :=
    (Complex.abs_re_le_norm _).trans h
  have hlow : -(1 / 2 : ℝ) ≤ (jacobiThetaQ - 1).re := (abs_le.mp hre).1
  have hdecomp : jacobiThetaQ = (jacobiThetaQ - 1) + 1 := by ring
  rw [hdecomp, Complex.add_re, Complex.one_re]
  linarith

/-! ## 4. Connection to the finite Example 3.6 packet -/

/-- **Genuine connection to the finite packet.**  Every finite theta scale of the
concrete source theater is exactly the corresponding summand of the analytic
q-expansion at q = 1/5. -/
theorem packetScale_eq_qExpansionTerm (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    ((sourceTheater l).thetaPacket.scale j : ℂ) = qExpansionTerm j.1 := by
  rw [sourceTheater_theta_scale]
  exact (qExpansionTerm_eq_ofReal j.1).symm

/-! ## 5. The frozen card and the missing relation -/

/-- **Frozen card for the actual source etale theta generator/theta series.**
The tree has the finite Gaussian packet and, via this file, an actual analytic
Jacobi theta series at q = 1/5; it does NOT have the source's etale theta
function/theta generator over the source curve nor its q-expansion.  This card
records the shape of that missing data: a theta carrier, its theta series
values, its q-expansion, the q-parameter constrained to the actual
gaussianFiveThetaQ, and theta special values at the signed finite labels.  No
inhabitant is constructed in this file and no theorem consumes one; in
particular the analytic Jacobi theta constructed above is not substituted for
this card. -/
structure SourceThetaAnalyticGeneratorCard (l : PrimeGeFive) where
  /-- The actual source etale theta function/theta series carrier. -/
  Theta : Type
  /-- Its theta values (analytic realization). -/
  thetaSeries : Theta → ℂ
  /-- Its q-expansion coefficients. -/
  qExpansion : Theta → ℤ → ℂ
  /-- The q-parameter of the source theta generator. -/
  q : ℝ
  /-- The source q-parameter must be the actual tree q-value gaussianFiveThetaQ. -/
  q_eq_gaussian : q = gaussianFiveThetaQ
  /-- Theta special values at the signed finite labels. -/
  specialValue : Theta → SignedLabel l.value → ℂ

/-- **The exact missing relation.**  A source theta generator whose q-expansion
is the analytic Jacobi q-series at q = 1/5 and whose special values are the
finite packet scales.  This predicate is only recorded: it is not proved, and no
theorem in this file assumes it. -/
def missingSourceThetaAnalyticRelation
    (card : SourceThetaAnalyticGeneratorCard l) : Prop :=
  ∃ t : card.Theta,
    (∀ n : ℤ, card.qExpansion t n = qExpansionTerm n) ∧
    (∀ j : SignedLabel l.value,
      card.specialValue t j = ((sourceTheater l).thetaPacket.scale j : ℂ))

/-! ## 6. Summary -/

/-- **Summary of the analytic Jacobi theta construction.**  At q = 1/5 the
Mathlib Jacobi theta value has the proved Gaussian q-expansion, convergence,
classical one-plus-twice-sum form, symmetry, nonvanishing and positive real part;
its summands are exactly the finite Example 3.6 packet scales; and the missing
identification with the actual source etale theta generator is frozen as a card
together with the explicit missing-relation predicate. -/
theorem example36ThetaSeries_summary :
    (Complex.exp (Real.pi * Complex.I * thetaTau) = (gaussianFiveThetaQ : ℂ)) ∧
    |gaussianFiveThetaQ| < 1 ∧
    (jacobiThetaQ = ∑' n : ℤ, qExpansionTerm n) ∧
    HasSum qExpansionTerm jacobiThetaQ ∧
    (∀ n : ℤ, qExpansionTerm (-n) = qExpansionTerm n) ∧
    jacobiThetaQ ≠ 0 ∧
    0 < jacobiThetaQ.re ∧
    (∀ (l : PrimeGeFive) (j : SignedLabel l.value),
      ((sourceTheater l).thetaPacket.scale j : ℂ) = qExpansionTerm j.1) :=
  ⟨thetaTau_exp, gaussianFiveThetaQ_abs_lt_one,
    jacobiThetaQ_eq_tsum_qExpansionTerm, hasSum_qExpansionTerm,
    qExpansionTerm_neg, jacobiThetaQ_ne_zero, jacobiThetaQ_re_pos,
    packetScale_eq_qExpansionTerm⟩

end

end ThetaSeries
end Example36
end Frobenioid
end IUTII
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the analytic Jacobi theta series at q = 1/5 and its
connection to the finite Example 3.6 packet.  Mathlib's actual one-variable
Jacobi theta function is instantiated at tau = i log 5 / pi (q = 1/5); its
q-expansion, convergence, classical form, symmetry, nonvanishing, positive real
part, periodicity and S-transformation are proved; every finite packet scale is
identified with the corresponding analytic summand; the source etale theta
generator/theta series is frozen as SourceThetaAnalyticGeneratorCard and the
missing relation as missingSourceThetaAnalyticRelation.  No fake source
generator and no theta-pilot/q-pilot claim. -/
def example36ThetaSeries : Obligation :=
  { id := "IUT-II.example36-theta-series"
    source :=
      "IUT II, theta evaluation and q-expansion; IUT I, Definition 3.6 and " ++
        "Corollary 3.7 (theta data of Theta-Hodge theaters)"
    status := VerificationStatus.testCarrier
    note :=
      "Used Mathlib's actual one-variable Jacobi theta function (not a " ++
        "replacement) at tau = i log 5 / pi, where exp(pi i tau) = " ++
        "gaussianFiveThetaQ = 1/5 (thetaTau_exp) and |q| < 1.  Proved the " ++
        "q-expansion jacobiThetaQ = sum over Z of qExpansionTerm with " ++
        "qExpansionTerm n = q^(gaussExponent n) " ++
        "(jacobiThetaQ_eq_tsum_qExpansionTerm), convergence as a HasSum " ++
        "(hasSum_qExpansionTerm), symmetry qExpansionTerm(-n) = " ++
        "qExpansionTerm n, special values " ++
        "qExpansionTerm 0 = 1 and qExpansionTerm 1 = q, the non-vacuity bound " ++
        "|theta - 1| <= 1/2 with theta != 0 and Re theta > 0.  Genuine " ++
        "connection to the finite " ++
        "Example 3.6 packet: every finite packet scale of the concrete source " ++
        "theater equals the corresponding analytic q-expansion summand at " ++
        "q = 1/5 (packetScale_eq_qExpansionTerm).  NOT provided: the " ++
        "identification of the analytic theta series with the actual source " ++
        "etale theta function/theta generator, and the identification of the " ++
        "finite packet with the source theta special values; the source etale " ++
        "theta carrier/q-expansion is frozen as " ++
        "SourceThetaAnalyticGeneratorCard and the exact missing relation as " ++
        "missingSourceThetaAnalyticRelation (never assumed or proved).  The " ++
        "analytic Jacobi theta is not substituted for the source generator, and " ++
        "no theta-pilot/q-pilot/Tate claim is made."
    dependsOn :=
      [ "IUT-II.example36-source-theater-carrier",
        "IUT-II.example36-theta-generator-feasibility",
        "IUT-II.finite-theta-packet",
        "Foundations.Theta.gaussian-kernel" ] }

end LeanFormal.IUT.Audit
