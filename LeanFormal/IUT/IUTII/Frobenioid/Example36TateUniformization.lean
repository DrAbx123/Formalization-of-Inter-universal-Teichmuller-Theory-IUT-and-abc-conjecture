/-
  # Task-120: the actual Tate uniformization / source etale theta boundary

  This module records the parts of the required actual source theory that can be
  constructed from the tree and the exact classical theorem that is missing.

  ## Actual constructions

  * concreteFiveTateCurve is the canonical q-series Tate Weierstrass curve
    TateCurve.weierstrassCurve Q_5 (q = 5); it is the actual curve attached to
    the explicit q-parameter q = 5 in Q_5, whose norm is
    gaussianFiveThetaQ = 1/5 (concreteFiveTateCurve_q_norm).
  * concreteFiveTateCurve_isElliptic: its discriminant is nonzero, by the
    actual q-series estimates of TateCurveDiscriminantEstimates
    (canonicalCurve_is_elliptic); the discriminant has norm exactly
    ‖q‖ = 1/5 (concreteFiveTateCurve_delta_norm) and c4 has norm one.
  * concreteFiveQCandidate is the actual finite-place q-candidate at the
    concrete place above 5, from the completed-DVR construction
    finitePlaceQCandidate_nonempty.
  * The concrete split curve concreteSplitPuncturedCurve has actual split
    multiplicative reduction at concreteFivePlace (imported actual theorem).

  ## Exact classical theorem missing

  The required CurveIndexedTateUniformization for concreteSplitPuncturedCurve at
  concreteFivePlace would require all of the following, none of which is
  constructed in Mathlib 4.32.2 or in the tree:

  1. (Tate uniformization, curve side) A variable change C over the completion
     such that
        C • TateCurve.weierstrassCurve (Completion place) parameter.q
          = (concreteSplitPuncturedCurve.baseChange (Completion place)).curve;
     equivalently, an actual identification of the split curve with the Tate
     q-series equation at its actual Tate parameter q.  The tree contains the
     explicit contract (Foundations/Geometry/TateUniformizationContract) but no
     constructor; its audit status is interface and its own note states that
     coordinate identification, quotient point uniformization and Galois
     equivariance are genuine missing C-layer theorems.
  2. (Tate uniformization, point side) A Galois-equivariant group isomorphism
        (AlgebraicClosure Completion)^x / q^Z
          ≃* Multiplicative (localCurve.AlgebraicClosurePoint).
     This is the analytic Tate uniformization theorem; it is absent.
  3. (Theta function / line bundle) An actual Tate theta function, theta
     characteristic / line-bundle section on the source curve or Tate model,
     with actual q-expansion and special values at the signed labels.  The tree
     has only the finite theta packet and the analytic Jacobi theta model; no
     theta function or line-bundle section is constructed.
  4. (Nontrivial Theta-link) A nontrivial q-transport source Theta-link; the
     only actual HodgeTheaterLink relation in the tree is q-preserving
     (link_target_theta_q), so it cannot express the source Theta-link.

  Consequently the strengthened SourceCurveEtaleThetaIdentificationCard is NOT
  inhabited by this file, and the tasks remain open.  No card, refl equivalence,
  finite-packet or scalar substitution is used as completion.

  Source correspondence: IUT I, Definition 3.1(c); IUT II, theta evaluation and
  q-expansion; classical Tate uniformization at split multiplicative places.
-/

import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceEtaleThetaTheory
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaGenerator
import LeanFormal.IUT.Foundations.Geometry.RigidTateSeries
import Mathlib.Analysis.SpecificLimits.Normed
import LeanFormal.IUT.Foundations.Geometry.TateCurveDiscriminantEstimates
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateParameter
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract
import LeanFormal.IUT.IUTII.Frobenioid.Example36ThetaSeries
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurvePadic
import LeanFormal.IUT.Foundations.Geometry.TateJInvariantNorm
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace TateUniformization

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceEtaleThetaTheory

local instance fivePrimeFactTate : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance fivePrimeLabelFactTate :
    Fact (Nat.Prime SourceEtaleThetaTheory.fivePrimeLabel.value) :=
  ⟨SourceEtaleThetaTheory.fivePrimeLabel.prime⟩

noncomputable section

/-! ## 1. The actual explicit Tate q-parameter and q-series curve -/

/-- The explicit q-parameter q = 5 in Q_5 (the p-adic element, whose norm is
1/5). -/
def concreteFiveTateParameter : ℚ_[SourceEtaleThetaTheory.fivePrimeLabel.value] :=
  (SourceEtaleThetaTheory.fivePrimeLabel.value :
    ℚ_[SourceEtaleThetaTheory.fivePrimeLabel.value])

@[simp] theorem concreteFiveTateParameter_eq :
    concreteFiveTateParameter = (SourceEtaleThetaTheory.fivePrimeLabel.value :
      ℚ_[SourceEtaleThetaTheory.fivePrimeLabel.value]) :=
  rfl

/-- The norm of the explicit q-parameter is the actual source value
gaussianFiveThetaQ = 1/5. -/
theorem concreteFiveTateParameter_norm :
    ‖concreteFiveTateParameter‖ = gaussianFiveThetaQ := by
  change ‖TateCurvePadic.q SourceEtaleThetaTheory.fivePrimeLabel‖ = gaussianFiveThetaQ
  rw [TateCurvePadic.q_norm_eq]
  rw [show (SourceEtaleThetaTheory.fivePrimeLabel.value : ℝ) = 5 by
    exact_mod_cast SourceEtaleThetaTheory.fivePrimeLabel_value,
    SourceTheaterCarrier.gaussianFiveThetaQ_eq_inv_five]

/-- The canonical q-series Tate curve at q = 5. -/
noncomputable def concreteFiveTateCurve :
    WeierstrassCurve ℚ_[SourceEtaleThetaTheory.fivePrimeLabel.value] :=
  TateCurve.weierstrassCurve _
    concreteFiveTateParameter

theorem concreteFiveTateCurve_eq :
    concreteFiveTateCurve =
      TateCurvePadic.canonicalCurve SourceEtaleThetaTheory.fivePrimeLabel := by
  rw [concreteFiveTateCurve, TateCurvePadic.canonicalCurve_eq]
  rfl

/-- The canonical q-series Tate curve at q = 5 is an actual elliptic curve
(the discriminant is nonzero by the q-series estimates). -/
theorem concreteFiveTateCurve_isElliptic : concreteFiveTateCurve.IsElliptic := by
  rw [concreteFiveTateCurve_eq]
  exact TateCurvePadic.canonicalCurve_is_elliptic
    SourceEtaleThetaTheory.fivePrimeLabel

/-- The discriminant of the q-series Tate curve at q = 5 is nonzero. -/
theorem concreteFiveTateCurve_delta_ne_zero : concreteFiveTateCurve.Δ ≠ 0 :=
  concreteFiveTateCurve_isElliptic.isUnit.ne_zero

/-- The discriminant norm is exactly the q-parameter norm 1/5. -/
theorem concreteFiveTateCurve_delta_norm :
    ‖concreteFiveTateCurve.Δ‖ = gaussianFiveThetaQ := by
  rw [concreteFiveTateCurve_eq]
  rw [TateCurvePadic.canonicalCurve_delta_norm_eq_q,
    TateCurvePadic.q_norm_eq]
  rw [show (SourceEtaleThetaTheory.fivePrimeLabel.value : ℝ) = 5 by
    exact_mod_cast SourceEtaleThetaTheory.fivePrimeLabel_value,
    SourceTheaterCarrier.gaussianFiveThetaQ_eq_inv_five]

/-- The c4 coefficient of the q-series Tate curve at q = 5 has norm one. -/
theorem concreteFiveTateCurve_c4_norm :
    ‖concreteFiveTateCurve.c₄‖ = 1 := by
  rw [concreteFiveTateCurve_eq]
  exact TateCurvePadic.c4_norm_eq_one SourceEtaleThetaTheory.fivePrimeLabel

/-- The q-parameter is contracting. -/
theorem concreteFiveTateParameter_norm_lt_one :
    ‖concreteFiveTateParameter‖ < 1 := by
  rw [concreteFiveTateParameter_norm,
    SourceTheaterCarrier.gaussianFiveThetaQ_eq_inv_five]
  norm_num

/-! ## 2. The actual finite-place q-candidate and split reduction -/

/-- Actual finite-place q-candidate at the concrete place above 5. -/
noncomputable def concreteFiveQCandidate : FinitePlaceQCandidate concreteFivePlace :=
  Classical.choice (finitePlaceQCandidate_nonempty concreteFivePlace)

theorem concreteFiveQCandidate_exists :
    Nonempty (FinitePlaceQCandidate concreteFivePlace) :=
  ⟨concreteFiveQCandidate⟩

/-- Actual split multiplicative reduction of the concrete split curve at the
concrete place above 5. -/
theorem concreteSplitCurve_hasSplitMultiplicativeReductionAt_five :
    concreteSplitPuncturedCurve.HasSplitMultiplicativeReductionAt
      concreteFivePlace :=
  concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_five

/-- Actual multiplicative reduction of the concrete split curve at the concrete
place above 5. -/
theorem concreteSplitCurve_hasMultiplicativeReductionAt_five :
    concreteSplitPuncturedCurve.HasMultiplicativeReductionAt concreteFivePlace :=
  concreteSplitPuncturedCurve_hasMultiplicativeReductionAt_five

/-! ## 3. Summary of the actual constructions -/

/-- **Actual constructions available for the Tate/source-theta task.**  The
explicit q = 5 in Q_5 has norm gaussianFiveThetaQ = 1/5; the canonical q-series
Tate curve at q = 5 is actually elliptic with discriminant of norm 1/5 and c4
of norm one; an actual finite-place q-candidate exists at the concrete place
above 5; the concrete split curve actually has split multiplicative reduction
there.  The CurveIndexedTateUniformization, the source etale theta function /
line-bundle section / q-expansion / special values and the nontrivial Theta-link
are NOT constructed; they are the exact missing classical theorems recorded in
the module header and audit. -/
theorem example36TateUniformization_actual_summary :
    (‖concreteFiveTateParameter‖ = gaussianFiveThetaQ) ∧
    (concreteFiveTateCurve.IsElliptic) ∧
    (concreteFiveTateCurve.Δ ≠ 0) ∧
    (‖concreteFiveTateCurve.Δ‖ = gaussianFiveThetaQ) ∧
    (‖concreteFiveTateCurve.c₄‖ = 1) ∧
    (Nonempty (FinitePlaceQCandidate concreteFivePlace)) ∧
    (concreteSplitPuncturedCurve.HasSplitMultiplicativeReductionAt
      concreteFivePlace) :=
  ⟨concreteFiveTateParameter_norm,
    concreteFiveTateCurve_isElliptic,
    concreteFiveTateCurve_delta_ne_zero,
    concreteFiveTateCurve_delta_norm,
    concreteFiveTateCurve_c4_norm,
    concreteFiveQCandidate_exists,
    concreteSplitCurve_hasSplitMultiplicativeReductionAt_five⟩

/-! ## 4. The actual Tate theta q-series on the rigid Tate annulus -/

namespace TateRigidTheta

open LeanFormal.IUT.RigidTate
open LeanFormal.IUT.IUTII.Frobenioid.Example36.ThetaSeries
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (P : RigidTate.Parameter (K := K)) (u : RigidTate.FundamentalDomain P)

def positiveTerm (n : ℕ) : K := P.q ^ (n ^ 2) * u.1 ^ n
def negativeTerm (m : ℕ) : K := P.q ^ ((m + 1) ^ 2) * u.1 ^ (-(m + 1 : ℕ) : ℤ)

lemma square_ge_self (n : ℕ) (hn : 1 ≤ n) : n ≤ n ^ 2 := by
  nlinarith

lemma positiveTerm_norm_le (n : ℕ) (hn : 1 ≤ n) :
    ‖positiveTerm P u n‖ ≤ ‖P.q‖ ^ n := by
  rw [positiveTerm, norm_mul, norm_pow, norm_pow]
  have hqnonneg : 0 ≤ ‖P.q‖ := norm_nonneg _
  have hqle1 : ‖P.q‖ ≤ 1 := P.q_norm_lt_one.le
  have hpowle : ‖P.q‖ ^ (n ^ 2) ≤ ‖P.q‖ ^ n :=
    pow_le_pow_of_le_one hqnonneg hqle1 (square_ge_self n hn)
  have hu : ‖u.1‖ ^ n ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (RigidTate.FundamentalDomain.norm_lt_one P u).le
  calc
    ‖P.q‖ ^ (n ^ 2) * ‖u.1‖ ^ n ≤ ‖P.q‖ ^ n * 1 :=
      mul_le_mul hpowle hu (pow_nonneg (norm_nonneg _) n) (pow_nonneg hqnonneg n)
    _ = ‖P.q‖ ^ n := by ring

lemma positiveTerm_summable : Summable (positiveTerm P u) := by
  refine Summable.of_norm_bounded_eventually
    (summable_geometric_of_lt_one (norm_nonneg P.q) P.q_norm_lt_one) ?_
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  exact ⟨1, fun n hn => positiveTerm_norm_le P u n hn⟩

lemma square_succ_ge (m : ℕ) (hm : 1 ≤ m) : 2 * (m + 1) ≤ (m + 1) ^ 2 := by
  nlinarith

lemma negativeTerm_norm_le (m : ℕ) (hm : 1 ≤ m) :
    ‖negativeTerm P u m‖ ≤ ‖P.q‖ ^ (m + 1) := by
  rw [negativeTerm, norm_mul, norm_pow, norm_zpow]
  have hqpos : 0 < ‖P.q‖ := P.q_norm_pos
  have huq : ‖P.q‖ < ‖u.1‖ := RigidTate.FundamentalDomain.q_lt_norm P u
  have hpowlt : ‖P.q‖ ^ (m + 1) < ‖u.1‖ ^ (m + 1) :=
    pow_lt_pow_left₀ huq (le_of_lt hqpos) (by omega)
  have hinv : (‖u.1‖ ^ (m + 1))⁻¹ < (‖P.q‖ ^ (m + 1))⁻¹ :=
    inv_strictAnti₀ (pow_pos hqpos _) hpowlt
  have hsq : 2 * (m + 1) ≤ (m + 1) ^ 2 := square_succ_ge m hm
  have hqle1 : ‖P.q‖ ≤ 1 := P.q_norm_lt_one.le
  have hqnonneg : 0 ≤ ‖P.q‖ := hqpos.le
  have hpowle : ‖P.q‖ ^ ((m + 1) ^ 2) ≤ ‖P.q‖ ^ (2 * (m + 1)) :=
    pow_le_pow_of_le_one hqnonneg hqle1 hsq
  have hmain : ‖P.q‖ ^ ((m + 1) ^ 2) * (‖P.q‖ ^ (m + 1))⁻¹ ≤
      ‖P.q‖ ^ (m + 1) := by
    rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos hqpos (m + 1))]
    calc
      ‖P.q‖ ^ ((m + 1) ^ 2) ≤ ‖P.q‖ ^ (2 * (m + 1)) := hpowle
      _ = ‖P.q‖ ^ (m + 1) * ‖P.q‖ ^ (m + 1) := by
        rw [show 2 * (m + 1) = (m + 1) + (m + 1) by ring, pow_add]
  calc
    ‖P.q‖ ^ ((m + 1) ^ 2) * ‖u.1‖ ^ (-(m+1 : ℕ) : ℤ) =
        ‖P.q‖ ^ ((m + 1) ^ 2) * (‖u.1‖ ^ (m + 1))⁻¹ := by
          rw [zpow_neg, zpow_natCast]
    _ ≤ ‖P.q‖ ^ ((m + 1) ^ 2) * (‖P.q‖ ^ (m + 1))⁻¹ :=
          (mul_lt_mul_of_pos_left hinv (pow_pos hqpos _)).le
    _ ≤ ‖P.q‖ ^ (m + 1) := hmain

lemma negativeTerm_summable : Summable (negativeTerm P u) := by
  have hgeom : Summable (fun m : ℕ => ‖P.q‖ ^ (m + 1)) := by
    simpa [pow_succ, mul_comm, mul_left_comm] using
      (summable_geometric_of_lt_one (norm_nonneg P.q) P.q_norm_lt_one).mul_left ‖P.q‖
  refine Summable.of_norm_bounded_eventually hgeom ?_
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  exact ⟨1, fun m hm => negativeTerm_norm_le P u m hm⟩

noncomputable def positiveSeries : K := ∑' n : ℕ, positiveTerm P u n
noncomputable def negativeSeries : K := ∑' m : ℕ, negativeTerm P u m
noncomputable def thetaSeries : K := positiveSeries P u + negativeSeries P u

theorem hasSum_positiveSeries : HasSum (positiveTerm P u) (positiveSeries P u) :=
  (positiveTerm_summable P u).hasSum
theorem hasSum_negativeSeries : HasSum (negativeTerm P u) (negativeSeries P u) :=
  (negativeTerm_summable P u).hasSum
theorem thetaSeries_eq : thetaSeries P u = positiveSeries P u + negativeSeries P u := rfl
theorem hasSum_thetaSeries_split :
    HasSum (positiveTerm P u) (positiveSeries P u) ∧
      HasSum (negativeTerm P u) (negativeSeries P u) :=
  ⟨hasSum_positiveSeries P u, hasSum_negativeSeries P u⟩

/-- The actual q |-> q^2 transport of the Tate parameter. -/
noncomputable def transportParameter : RigidTate.Parameter (K := K) where
  q := P.q ^ 2
  q_ne_zero := pow_ne_zero 2 P.q_ne_zero
  q_norm_pos := by
    rw [norm_pow]
    exact pow_pos P.q_norm_pos 2
  q_norm_lt_one := by
    rw [norm_pow]
    nlinarith [norm_nonneg P.q, P.q_norm_lt_one]

/-- The identity map on the fundamental annulus is a genuine transport of the
q |-> q^2 parameter (the q^2-annulus contains the q-annulus). -/
def transportDomain : RigidTate.FundamentalDomain (transportParameter P) := by
  refine ⟨u.1, u.ne_zero, ?_, ?_⟩
  · have hq2 : ‖P.q‖ ^ 2 < ‖u.1‖ := by
      nlinarith [P.q_norm_pos, P.q_norm_lt_one,
        RigidTate.FundamentalDomain.q_lt_norm P u]
    simpa [transportParameter, norm_pow] using hq2
  · exact RigidTate.FundamentalDomain.norm_lt_one P u

/-- The actual transported theta value: evaluate the q^2-theta series at the
same annulus point. -/
noncomputable def thetaTransport : K :=
  thetaSeries (transportParameter P) (transportDomain P u)

theorem transportParameter_q_ne :
    (transportParameter P).q ≠ P.q := by
  intro h
  have hq : P.q ^ 2 = P.q := h
  have hfac : P.q * (P.q - 1) = 0 := by
    calc
      P.q * (P.q - 1) = P.q ^ 2 - P.q := by ring
      _ = 0 := by rw [hq]; ring
  rcases mul_eq_zero.mp hfac with h0 | h1
  · exact P.q_ne_zero h0
  · exact P.q_ne_one (sub_eq_zero.mp h1)

/-- The concrete complex Tate parameter with q = gaussianFiveThetaQ = 1/5. -/
noncomputable def concreteComplexTateParameter : RigidTate.Parameter (K := ℂ) where
  q := (gaussianFiveThetaQ : ℂ)
  q_ne_zero := Complex.ofReal_ne_zero.mpr (ne_of_gt gaussianFiveThetaQ_pos)
  q_norm_pos := by
    rw [Complex.norm_real, Real.norm_of_nonneg gaussianFiveThetaQ_pos.le]
    exact gaussianFiveThetaQ_pos
  q_norm_lt_one := by
    rw [Complex.norm_real, Real.norm_of_nonneg gaussianFiveThetaQ_pos.le]
    exact gaussianFiveThetaQ_lt_one

/-- The q-expansion coefficient of the actual Tate theta series. -/
noncomputable def thetaQExpansionCoefficient (n : ℤ) : ℂ :=
  (concreteComplexTateParameter.q) ^ (gaussExponent n).toNat

theorem thetaQExpansionCoefficient_eq_realThetaValue (n : ℤ) :
    thetaQExpansionCoefficient n =
      ((realThetaValue gaussianFiveThetaQ n : ℝ) : ℂ) := by
  unfold thetaQExpansionCoefficient concreteComplexTateParameter realThetaValue
  rw [Complex.ofReal_pow]

theorem thetaQExpansionCoefficient_eq_sourceTheaterScale
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    thetaQExpansionCoefficient j.1 =
      (((sourceTheater l).thetaPacket.scale j : ℝ) : ℂ) := by
  rw [thetaQExpansionCoefficient_eq_realThetaValue, sourceTheater_theta_scale]

/-- The actual theta q-expansion coefficient is the complexification of the
actual analytic Jacobi q-expansion term qExpansionTerm. -/
theorem thetaQExpansionCoefficient_eq_qExpansionTerm (n : ℤ) :
    thetaQExpansionCoefficient n = qExpansionTerm n := by
  rw [thetaQExpansionCoefficient_eq_realThetaValue, qExpansionTerm_eq_ofReal]

/-- The q |-> q^2 theta transport squares the theta q-expansion coefficients:
the q^2-transported coefficient is the square of the original coefficient. -/
theorem transportThetaQExpansionCoefficient_eq_square (n : ℤ) :
    (transportParameter concreteComplexTateParameter).q ^
        (gaussExponent n).toNat =
      (thetaQExpansionCoefficient n) ^ 2 := by
  change ((((gaussianFiveThetaQ : ℂ) ^ 2) ^ (gaussExponent n).toNat) =
    ((((gaussianFiveThetaQ : ℂ)) ^ (gaussExponent n).toNat) ^ 2))
  rw [← pow_mul, ← pow_mul]
  congr 1
  ring

/-- **Actual Tate theta q-series summary.**  On the actual rigid Tate
fundamental annulus the two one-sided Tate theta sums converge (bilateral
Laurent q-expansion), the q |-> q^2 transport parameter and annulus transport
are constructed, and the theta q-expansion coefficients at the concrete
complex parameter q = 1/5 are exactly the actual realThetaValue special values
and the actual source theater theta packet scales. -/
theorem tateThetaSeries_actual_summary
    (P : RigidTate.Parameter (K := K)) (u : RigidTate.FundamentalDomain P) :
    HasSum (positiveTerm P u) (positiveSeries P u) ∧
    HasSum (negativeTerm P u) (negativeSeries P u) ∧
    (transportParameter P).q = P.q ^ 2 ∧
    (transportParameter P).q ≠ P.q ∧
    (∀ n : ℤ, thetaQExpansionCoefficient n =
      ((realThetaValue gaussianFiveThetaQ n : ℝ) : ℂ)) :=
  ⟨hasSum_positiveSeries P u, hasSum_negativeSeries P u, rfl,
    transportParameter_q_ne P, thetaQExpansionCoefficient_eq_realThetaValue⟩

end TateRigidTheta

end

end TateUniformization
end Example36
end Frobenioid
end IUTII
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for task-120.  ACTUAL: explicit q = 5 in Q_5 with norm
gaussianFiveThetaQ = 1/5; canonical q-series Tate curve at q = 5 is actually
elliptic (q-series discriminant estimates), with ‖Δ‖ = 1/5 and ‖c₄‖ = 1; an
actual finite-place q-candidate at concreteFivePlace; actual split
multiplicative reduction of concreteSplitPuncturedCurve at concreteFivePlace.
MISSING EXACT THEOREMS (not cards): (1) CurveIndexedTateUniformization
concreteSplitPuncturedCurve concreteFivePlace parameter — no constructor; it
requires a coordinate variable change identifying the split curve completion
with the Tate q-series equation at its actual Tate parameter, plus the
Galois-equivariant quotient point uniformization
(AlgebraicClosure Completion)^x/q^Z ≃* Multiplicative localCurve.AlgebraicClosurePoint;
(2) the actual source etale theta function / theta characteristic / line-bundle
section and its normalization/identification with the constructed Tate theta
q-series; the actual Tate theta q-series itself is now constructed (positive and
negative convergent Laurent terms on the rigid Tate annulus, bilateral split
summability, q |-> q^2 transport, and q-expansion coefficients equal to
realThetaValue/source theater theta scales), but its line-bundle section
identification and the full source theta function are not; (3) the nontrivial
source Theta-link (the actual HodgeTheaterLink relation is q-preserving).
These are absent from Mathlib 4.32.2 and from the tree; the corrected
split-source-curve q-expansion/evaluation card is inhabited, but the full
source etale theta function/section and nontrivial Theta-link are NOT
constructed.  No card, refl equivalence, finite packet or scalar substitution
is used. -/
def example36TateUniformization : Obligation :=
  { id := "IUT-II.example36-tate-uniformization-source-theta"
    source :=
      "IUT I, Definition 3.1(c); IUT II, theta evaluation and q-expansion; " ++
        "classical Tate uniformization at split multiplicative places"
    status := VerificationStatus.interface
    note :=
      "Actual: concreteFiveTateParameter q = 5 in Q_5 with norm " ++
        "gaussianFiveThetaQ = 1/5; concreteFiveTateCurve = " ++
        "TateCurve.weierstrassCurve Q_5 5 is actually elliptic " ++
        "(concreteFiveTateCurve_isElliptic, from the q-series discriminant " ++
        "estimates), with concreteFiveTateCurve_delta_ne_zero, " ++
        "concreteFiveTateCurve_delta_norm = 1/5 and " ++
        "concreteFiveTateCurve_c4_norm = 1; concreteFiveQCandidate actual " ++
        "finite-place q-candidate; actual split multiplicative reduction of " ++
        "concreteSplitPuncturedCurve at concreteFivePlace.  MISSING exact " ++
        "classical theorems: (1) CurveIndexedTateUniformization " ++
        "concreteSplitPuncturedCurve concreteFivePlace parameter (no " ++
        "constructor) with coordinate variable change identifying the split " ++
        "curve completion with the Tate q-series equation at the actual Tate " ++
        "parameter and the Galois-equivariant point uniformization " ++
        "(AlgebraicClosure Completion)^x/q^Z ≃* Multiplicative " ++
        "localCurve.AlgebraicClosurePoint; (2) actual source etale theta " ++
        "function/theta characteristic/line-bundle section with q-expansion " ++
        "and special values; (3) nontrivial source Theta-link (the actual " ++
        "HodgeTheaterLink is q-preserving).  Not in Mathlib 4.32.2 or the tree; " ++
        "the corrected split-source-curve q-expansion/evaluation card is " ++
        "inhabited.  ACTUAL Tate theta q-series now constructed on the rigid " ++
        "Tate annulus: positiveTerm/negativeTerm, positiveTerm_summable, " ++
        "negativeTerm_summable, positiveSeries/negativeSeries/thetaSeries, " ++
        "hasSum_positiveSeries/hasSum_negativeSeries/thetaSeries_eq/" ++
        "hasSum_thetaSeries_split, transportParameter/transportDomain/" ++
        "thetaTransport/transportParameter_q_ne, concreteComplexTateParameter, " ++
        "thetaQExpansionCoefficient with " ++
        "thetaQExpansionCoefficient_eq_realThetaValue and " ++
        "thetaQExpansionCoefficient_eq_sourceTheaterScale, and " ++
        "tateThetaSeries_actual_summary.  Still missing: the source etale " ++
        "theta line-bundle section/normalization, its identification with the " ++
        "Tate theta q-series, and the nontrivial source Theta-link; task-120 " ++
        "remains open.  No card/refl/finite-packet substitution."
    dependsOn :=
      [ "Foundations.Geometry.tate-curve-discriminant-estimates",
        "Foundations.Geometry.concrete-split-curve-five-place",
        "Foundations.Geometry.concrete-tate-parameter",
        "Foundations.Geometry.curve-indexed-tate-uniformization",
        "IUT-II.example36-source-etale-theta-theory" ] }

end LeanFormal.IUT.Audit

set_option autoImplicit false

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36.TateInverseJ

noncomputable section

local instance fivePrimeFactScratch : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-- The prime label 5, used only in this scratch file. -/
abbrev fivePrimeLabelScratch : PrimeGeFive where
  value := 5
  prime := Nat.prime_five
  ge_five := by norm_num

@[simp] theorem fivePrimeLabelScratch_value :
    fivePrimeLabelScratch.value = 5 := rfl

local instance fivePrimeLabelFactScratch :
    Fact (Nat.Prime fivePrimeLabelScratch.value) :=
  ⟨fivePrimeLabelScratch.prime⟩

/-- The concrete split curve is elliptic; this instance lets the j-invariant
appear in theorem statements. -/
local instance concreteSplitCurveLocalIsEllipticScratch :
    concreteSplitCurveLocal.IsElliptic :=
  concreteSplitCurveLocal_isElliptic

/-- The global split curve is elliptic. -/
local instance concreteSplitPuncturedCurveIsEllipticScratch :
    concreteSplitPuncturedCurve.curve.IsElliptic :=
  concreteSplitPuncturedCurve.isElliptic

/-- The norm of the prime 5 in Q_5. -/
theorem five_norm_five :
    ‖(5 : concreteLocalField)‖ = (1 / 5 : ℝ) := by
  simpa using (Padic.norm_p (p := 5))

theorem five_norm_two :
    ‖(2 : concreteLocalField)‖ = 1 := by
  simpa using
    (Padic.norm_natCast_eq_one_iff (p := 5) (n := 2)).2 (by norm_num)

theorem five_norm_2161 :
    ‖(2161 : concreteLocalField)‖ = 1 := by
  simpa using
    (Padic.norm_natCast_eq_one_iff (p := 5) (n := 2161)).2 (by norm_num)

theorem five_norm_10805 :
    ‖(10805 : concreteLocalField)‖ = (1 / 5 : ℝ) := by
  have h : (10805 : concreteLocalField) = (5 : concreteLocalField) * 2161 := by
    norm_num
  rw [h, norm_mul, five_norm_2161, mul_one]
  exact five_norm_five

theorem five_norm_four :
    ‖(4 : concreteLocalField)‖ = 1 := by
  simpa using
    (Padic.norm_natCast_eq_one_iff (p := 5) (n := 4)).2 (by norm_num)

theorem five_norm_25_over_4 :
    ‖(25 / 4 : concreteLocalField)‖ = (1 / 25 : ℝ) := by
  have h : (25 / 4 : concreteLocalField) = (5 : concreteLocalField) ^ 2 / 4 := by
    norm_num
  rw [h, norm_div, norm_pow, five_norm_five, five_norm_four]
  norm_num

theorem five_norm_2160 :
    ‖(2160 : concreteLocalField)‖ = (1 / 5 : ℝ) := by
  have h : (2160 : concreteLocalField) = (5 : concreteLocalField) * 432 := by
    norm_num
  have h432 : ‖(432 : concreteLocalField)‖ = 1 := by
    simpa using
      (Padic.norm_natCast_eq_one_iff (p := 5) (n := 432)).2 (by norm_num)
  rw [h, norm_mul, h432, mul_one]
  exact five_norm_five

/-! ## The concrete split curve over Q_5 -/

/-- The exact j-invariant of the explicit curve y^2 + xy = x^3 + 5 over Q_5. -/
theorem concreteSplitCurveLocal_j_eq :
    concreteSplitCurveLocal.j = (-1 / 10805 : concreteLocalField) := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ', concreteSplitCurveLocal_c₄,
    concreteSplitCurveLocal_delta]
  norm_num

/-- The exact norm of the split-curve j-invariant at 5. -/
theorem concreteSplitCurveLocal_j_norm_scratch :
    ‖concreteSplitCurveLocal.j‖ = (5 : ℝ) := by
  rw [concreteSplitCurveLocal_j_eq, norm_div, norm_neg, norm_one,
    five_norm_10805]
  norm_num

/-- The split j-invariant is not p-adically integral. -/
theorem concreteSplitCurveLocal_j_norm_gt_one :
    1 < ‖concreteSplitCurveLocal.j‖ := by
  rw [concreteSplitCurveLocal_j_norm_scratch]
  norm_num

/-- The inverse of the split j-invariant is the actual integer -10805. -/
theorem concreteSplitCurveLocal_j_inv :
    (concreteSplitCurveLocal.j)⁻¹ = (-10805 : concreteLocalField) := by
  rw [concreteSplitCurveLocal_j_eq]
  norm_num

/-- The split j-invariant is congruent to -1/5 modulo Z_5, in the precise form
5 * j = -1 (mod 5). -/
theorem concreteSplitCurveLocal_five_mul_j_add_one_norm_lt_one :
    ‖(5 : concreteLocalField) * concreteSplitCurveLocal.j + 1‖ < 1 := by
  have hnum : (5 : concreteLocalField) * concreteSplitCurveLocal.j + 1 =
      (2160 : concreteLocalField) / 2161 := by
    rw [concreteSplitCurveLocal_j_eq]
    norm_num
  rw [hnum, norm_div, five_norm_2160, five_norm_2161]
  norm_num

/-- In particular 5 * j is a 5-adic unit. -/
theorem concreteSplitCurveLocal_j_unit_part :
    ‖(5 : concreteLocalField) * concreteSplitCurveLocal.j‖ = 1 := by
  have hnum : (5 : concreteLocalField) * concreteSplitCurveLocal.j =
      (-1 : concreteLocalField) / 2161 := by
    rw [concreteSplitCurveLocal_j_eq]
    norm_num
  rw [hnum, norm_div, norm_neg, norm_one, five_norm_2161]
  norm_num

/-! ## The global punctured split curve over Q -/

/-- The rational split curve has the same explicit j-invariant. -/
theorem concreteSplitPuncturedCurve_j_eq :
    concreteSplitPuncturedCurve.curve.j = (-1 / 10805 : ℚ) := by
  change concreteSplitCurve.j = (-1 / 10805 : ℚ)
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ', concreteSplitCurve_c₄,
    concreteSplitCurve_delta]
  norm_num

/-- The rational split j-invariant, viewed in Q_5, is the local split
j-invariant.  (Base change preserves j by WeierstrassCurve.map_j.) -/
theorem concreteSplitPuncturedCurve_j_map_eq_local :
    algebraMap ℚ concreteLocalField concreteSplitPuncturedCurve.curve.j =
      concreteSplitCurveLocal.j := by
  rw [concreteSplitPuncturedCurve_j_eq, concreteSplitCurveLocal_j_eq]
  norm_num

/-- The norm at 5 of the punctured split curve's j-invariant is 5. -/
theorem concreteSplitPuncturedCurve_j_norm_at_five :
    ‖algebraMap ℚ concreteLocalField concreteSplitPuncturedCurve.curve.j‖ =
      (5 : ℝ) := by
  rw [concreteSplitPuncturedCurve_j_map_eq_local,
    concreteSplitCurveLocal_j_norm_scratch]

/-! ## The canonical q-series curve at q = 5 -/

/-- The q-series j-invariant at the prime label 5 has norm 5. -/
theorem tateJInvariant_five_norm_scratch :
    ‖TateCurvePadic.tateJInvariant fivePrimeLabelScratch‖ = (5 : ℝ) := by
  rw [TateCurvePadic.tateJInvariant_norm_eq_prime fivePrimeLabelScratch,
    fivePrimeLabelScratch_value]
  norm_num

/-! ## Exact leading 5-adic unit of the canonical q-series j-invariant -/

/-- The concrete a4 coefficient of the canonical q-series curve at q = 5. -/
abbrev fiveA4 : concreteLocalField :=
  TateCurve.a4 concreteLocalField (TateCurvePadic.q fivePrimeLabelScratch)

/-- The concrete a6 coefficient of the canonical q-series curve at q = 5. -/
abbrev fiveA6 : concreteLocalField :=
  TateCurve.a6 concreteLocalField (TateCurvePadic.q fivePrimeLabelScratch)

theorem fiveA4_norm : ‖fiveA4‖ = (1 / 25 : ℝ) := by
  have h := TateCurvePadic.a4_norm_eq fivePrimeLabelScratch
  rw [TateCurvePadic.q_norm_eq, five_norm_five] at h
  norm_num at h
  simpa [fiveA4, TateCurvePadic.q_eq_prime] using h

theorem fiveA6_norm : ‖fiveA6‖ = (1 / 5 : ℝ) := by
  have h := TateCurvePadic.a6_norm_eq fivePrimeLabelScratch
  rw [TateCurvePadic.q_norm_eq] at h
  norm_num at h
  simpa [fiveA6, TateCurvePadic.q_eq_prime] using h

/-- The a6 coefficient at q = 5 is 5/4 up to an error of norm at most 1/20. -/
theorem fiveA6_sub_five_quarters_norm_le :
    ‖fiveA6 - (5 / 4 : concreteLocalField)‖ ≤ (1 / 20 : ℝ) := by
  unfold fiveA6
  rw [TateCurvePadic.a6_decomposition fivePrimeLabelScratch]
  have hprincipal :
      TateCurvePadic.a6Principal fivePrimeLabelScratch =
        (5 / 4 : concreteLocalField) := by
    rw [TateCurvePadic.a6Principal, TateCurvePadic.q_eq_prime]
    norm_num
  rw [hprincipal]
  have hsub :
      ((5 / 4 : concreteLocalField) +
          TateCurvePadic.a6Remainder fivePrimeLabelScratch) -
        (5 / 4 : concreteLocalField) =
      TateCurvePadic.a6Remainder fivePrimeLabelScratch := by
    ring
  rw [hsub]
  have hrem := TateCurvePadic.a6_remainder_norm_le fivePrimeLabelScratch
  rw [TateCurvePadic.q_norm_eq] at hrem
  calc
    ‖TateCurvePadic.a6Remainder fivePrimeLabelScratch‖ ≤
        (5 : ℝ)⁻¹ ^ 2 * (1 - (5 : ℝ)⁻¹)⁻¹ := hrem
    _ = (1 / 20 : ℝ) := by norm_num

/-- A five-term nonarchimedean sum bound, used below. -/
private theorem norm_add_five_lt {B : ℝ}
    {a b c d e : concreteLocalField}
    (ha : ‖a‖ < B) (hb : ‖b‖ < B) (hc : ‖c‖ < B)
    (hd : ‖d‖ < B) (he : ‖e‖ < B) :
    ‖a + b + c + d + e‖ < B := by
  have h₁ : ‖a + b‖ < B :=
    lt_of_le_of_lt (Padic.nonarchimedean a b) (max_lt ha hb)
  have h₂ : ‖a + b + c‖ < B :=
    lt_of_le_of_lt (Padic.nonarchimedean (a + b) c) (max_lt h₁ hc)
  have h₃ : ‖a + b + c + d‖ < B :=
    lt_of_le_of_lt (Padic.nonarchimedean (a + b + c) d) (max_lt h₂ hd)
  exact lt_of_le_of_lt (Padic.nonarchimedean (a + b + c + d) e)
    (max_lt h₃ he)

/-- The exact expansion of the canonical discriminant at q = 5. -/
theorem five_canonicalCurve_delta_eq :
    (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ =
      fiveA4 ^ 2 - fiveA6 - 64 * fiveA4 ^ 3 -
        432 * fiveA6 ^ 2 + 72 * fiveA4 * fiveA6 := by
  rw [TateCurvePadic.canonicalCurve_delta]

/-- The discriminant at q = 5 is 5 up to an error of norm at most 1/20. -/
theorem five_canonicalCurve_delta_sub_five_norm_lt :
    ‖(TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ - 5‖ <
      (1 / 5 : ℝ) := by
  rw [five_canonicalCurve_delta_eq]
  have hdecomp :
      fiveA4 ^ 2 - fiveA6 - 64 * fiveA4 ^ 3 -
          432 * fiveA6 ^ 2 + 72 * fiveA4 * fiveA6 - 5 =
        fiveA4 ^ 2 +
          (-(fiveA6 - (5 / 4 : concreteLocalField)) - (25 / 4 : concreteLocalField)) +
          (-(64 : concreteLocalField) * fiveA4 ^ 3) +
          (-(432 : concreteLocalField) * fiveA6 ^ 2) +
          ((72 : concreteLocalField) * fiveA4 * fiveA6) := by
    ring
  rw [hdecomp]
  apply norm_add_five_lt
  · rw [norm_pow, fiveA4_norm]
    norm_num
  · have hrem : ‖fiveA6 - (5 / 4 : concreteLocalField)‖ ≤ (1 / 20 : ℝ) :=
      fiveA6_sub_five_quarters_norm_le
    have h25 : ‖(25 / 4 : concreteLocalField)‖ < (1 / 5 : ℝ) := by
      rw [five_norm_25_over_4]
      norm_num
    have hsum :
        ‖-(fiveA6 - (5 / 4 : concreteLocalField)) -
            (25 / 4 : concreteLocalField)‖ ≤
          max ‖-(fiveA6 - (5 / 4 : concreteLocalField))‖
            ‖(25 / 4 : concreteLocalField)‖ := by
      simpa only [sub_eq_add_neg, norm_neg] using
        (Padic.nonarchimedean
          (-(fiveA6 - (5 / 4 : concreteLocalField)))
          (-(25 / 4 : concreteLocalField)))
    calc
      ‖-(fiveA6 - (5 / 4 : concreteLocalField)) -
          (25 / 4 : concreteLocalField)‖ ≤
          max ‖-(fiveA6 - (5 / 4 : concreteLocalField))‖
            ‖(25 / 4 : concreteLocalField)‖ := hsum
      _ < (1 / 5 : ℝ) := by
        apply max_lt
        · have hneg : ‖-(fiveA6 - (5 / 4 : concreteLocalField))‖ ≤ (1 / 20 : ℝ) := by
            rw [norm_neg]
            exact hrem
          exact lt_of_le_of_lt hneg (by norm_num)
        · exact h25
  · rw [norm_mul, norm_pow, fiveA4_norm]
    have h64 : ‖-(64 : concreteLocalField)‖ ≤ 1 := by
      rw [norm_neg]
      exact TateCurvePadic.nat_cast_norm_le_one fivePrimeLabelScratch 64
    calc
      ‖-(64 : concreteLocalField)‖ * (1 / 25 : ℝ) ^ 3 ≤
          1 * (1 / 25 : ℝ) ^ 3 := by
        exact mul_le_mul_of_nonneg_right h64 (by norm_num)
      _ < (1 / 5 : ℝ) := by norm_num
  · rw [norm_mul, norm_pow, fiveA6_norm]
    have h432 : ‖-(432 : concreteLocalField)‖ ≤ 1 := by
      rw [norm_neg]
      exact TateCurvePadic.nat_cast_norm_le_one fivePrimeLabelScratch 432
    calc
      ‖-(432 : concreteLocalField)‖ * (1 / 5 : ℝ) ^ 2 ≤
          1 * (1 / 5 : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_right h432 (by norm_num)
      _ < (1 / 5 : ℝ) := by norm_num
  · rw [norm_mul, norm_mul, fiveA4_norm, fiveA6_norm]
    have h72 : ‖(72 : concreteLocalField)‖ ≤ 1 :=
      TateCurvePadic.nat_cast_norm_le_one fivePrimeLabelScratch 72
    calc
      ‖(72 : concreteLocalField)‖ * (1 / 25 : ℝ) * (1 / 5 : ℝ) ≤
          1 * (1 / 25 : ℝ) * (1 / 5 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h72 (by norm_num)) (by norm_num)
      _ < (1 / 5 : ℝ) := by norm_num

/-- The canonical c4 coefficient at q = 5 is 1 up to an error of norm at most
1/25. -/
theorem five_canonicalCurve_c4_sub_one_norm_le :
    ‖(TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ - 1‖ ≤
      (1 / 25 : ℝ) := by
  have hc4 :
      (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ =
        1 - 48 * fiveA4 := by
    rw [TateCurvePadic.canonicalCurve_c4]
  have hc4sub :
      (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ - 1 =
        -(48 : concreteLocalField) * fiveA4 := by
    rw [hc4]
    ring
  rw [hc4sub, norm_mul, fiveA4_norm]
  have h48 : ‖-(48 : concreteLocalField)‖ ≤ 1 := by
    rw [norm_neg]
    exact TateCurvePadic.nat_cast_norm_le_one fivePrimeLabelScratch 48
  calc
    ‖-(48 : concreteLocalField)‖ * (1 / 25 : ℝ) ≤ 1 * (1 / 25 : ℝ) := by
      exact mul_le_mul_of_nonneg_right h48 (by norm_num)
    _ = (1 / 25 : ℝ) := by norm_num

/-- The c4 cube at q = 5 is 1 up to an error of norm at most 1/25. -/
theorem five_canonicalCurve_c4_cube_sub_one_norm_le :
    ‖(TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 3 - 1‖ ≤
      (1 / 25 : ℝ) := by
  have hfac :
      (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 3 - 1 =
        ((TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ - 1) *
          ((TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 2 +
            (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ + 1) := by
    ring
  rw [hfac, norm_mul]
  have h1 := five_canonicalCurve_c4_sub_one_norm_le
  have hc4norm :
      ‖(TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄‖ = 1 :=
    TateCurvePadic.canonicalCurve_c4_norm_for_j fivePrimeLabelScratch
  have h2 :
      ‖(TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 2 +
          (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ + 1‖ ≤ 1 := by
    have hsq :
        ‖(TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 2‖ = 1 := by
      rw [norm_pow, hc4norm]
      norm_num
    have hsum :
        ‖(TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 2 +
            (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄‖ ≤ 1 :=
      (Padic.nonarchimedean _ _).trans (max_le hsq.le hc4norm.le)
    exact (Padic.nonarchimedean _ _).trans
      (max_le hsum (by simp))
  calc
    ‖(TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ - 1‖ *
        ‖(TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 2 +
          (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ + 1‖ ≤
        (1 / 25 : ℝ) * 1 := by
      exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    _ = (1 / 25 : ℝ) := by norm_num

/-- The exact 5-adic unit part of the q-series j-invariant at q = 5:
5 * j = 1 (mod 5). -/
theorem tateJInvariant_five_five_mul_sub_one_norm_lt_one :
    ‖(5 : concreteLocalField) *
        TateCurvePadic.tateJInvariant fivePrimeLabelScratch - 1‖ < 1 := by
  have hΔne :
      (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ ≠ 0 :=
    TateCurvePadic.canonicalCurve_delta_ne_zero fivePrimeLabelScratch
  have hΔnorm :
      ‖(TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ‖ =
        (1 / 5 : ℝ) := by
    rw [TateCurvePadic.canonicalCurve_delta_norm_eq_q,
      TateCurvePadic.q_norm_eq]
    norm_num
  have hnum :
      ‖(5 : concreteLocalField) *
          (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 3 -
        (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ‖ <
        (1 / 5 : ℝ) := by
    have h1 :
        ‖(5 : concreteLocalField) *
            ((TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 3 - 1)‖ <
          (1 / 5 : ℝ) := by
      rw [norm_mul]
      rw [five_norm_five]
      calc
        (1 / 5 : ℝ) *
            ‖(TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 3 - 1‖ ≤
            (1 / 5 : ℝ) * (1 / 25 : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            five_canonicalCurve_c4_cube_sub_one_norm_le (by norm_num)
        _ < (1 / 5 : ℝ) := by norm_num
    have h2 := five_canonicalCurve_delta_sub_five_norm_lt
    have hdecomp :
        (5 : concreteLocalField) *
            (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 3 -
          (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ =
        (5 : concreteLocalField) *
            ((TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 3 - 1) -
          ((TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ - 5) := by
      ring
    rw [hdecomp]
    calc
      ‖(5 : concreteLocalField) *
            ((TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 3 - 1) -
          ((TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ - 5)‖ =
          ‖(5 : concreteLocalField) *
              ((TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 3 - 1) +
            (-((TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ - 5))‖ := by
        rw [sub_eq_add_neg]
      _ ≤ max ‖(5 : concreteLocalField) *
              ((TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 3 - 1)‖
            ‖-((TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ - 5)‖ :=
        Padic.nonarchimedean _ _
      _ = max ‖(5 : concreteLocalField) *
              ((TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 3 - 1)‖
            ‖(TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ - 5‖ := by
        rw [norm_neg]
      _ < (1 / 5 : ℝ) := max_lt h1 h2
  rw [TateCurvePadic.tateJInvariant_eq]
  have hsub :
      (5 : concreteLocalField) *
          ((TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 3 /
            (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ) - 1 =
        ((5 : concreteLocalField) *
            (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).c₄ ^ 3 -
          (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ) /
          (TateCurvePadic.canonicalCurve fivePrimeLabelScratch).Δ := by
    field_simp [hΔne]
  rw [hsub, norm_div, hΔnorm]
  rw [div_lt_one (by norm_num : (0 : ℝ) < (1 / 5))]
  exact hnum

/-- The q-series j-invariant at q = 5 is not equal to the split j-invariant:
their 5 * j residues are +1 and -1 respectively. -/
theorem tateJInvariant_five_ne_split_j :
    TateCurvePadic.tateJInvariant fivePrimeLabelScratch ≠
      concreteSplitCurveLocal.j := by
  intro h
  have hpos := tateJInvariant_five_five_mul_sub_one_norm_lt_one
  have hpos' :
      ‖(5 : concreteLocalField) * concreteSplitCurveLocal.j - 1‖ < 1 := by
    rw [← h]
    exact hpos
  have hneg := concreteSplitCurveLocal_five_mul_j_add_one_norm_lt_one
  have hdiff : ‖(2 : concreteLocalField)‖ < 1 := by
    have hrw :
        (2 : concreteLocalField) =
          ((5 : concreteLocalField) * concreteSplitCurveLocal.j + 1) -
            ((5 : concreteLocalField) * concreteSplitCurveLocal.j - 1) := by
      ring
    rw [hrw]
    calc
      ‖((5 : concreteLocalField) * concreteSplitCurveLocal.j + 1) -
          ((5 : concreteLocalField) * concreteSplitCurveLocal.j - 1)‖ =
          ‖((5 : concreteLocalField) * concreteSplitCurveLocal.j + 1) +
            (-((5 : concreteLocalField) * concreteSplitCurveLocal.j - 1))‖ := by
        rw [sub_eq_add_neg]
      _ ≤ max ‖(5 : concreteLocalField) * concreteSplitCurveLocal.j + 1‖
            ‖-((5 : concreteLocalField) * concreteSplitCurveLocal.j - 1)‖ :=
        Padic.nonarchimedean _ _
      _ = max ‖(5 : concreteLocalField) * concreteSplitCurveLocal.j + 1‖
            ‖(5 : concreteLocalField) * concreteSplitCurveLocal.j - 1‖ := by
        rw [norm_neg]
      _ < 1 := max_lt hneg hpos'
  have h2 : ‖(2 : concreteLocalField)‖ = 1 := five_norm_two
  rw [h2] at hdiff
  exact lt_irrefl (1 : ℝ) hdiff

/-! ## Candidate inverse-j q-series parameters -/

/-- The q-series j-invariant attached to an arbitrary candidate q in Q_5.
This is the Weierstrass invariant c4^3 / Delta, defined without assuming
ellipticity (it is the j-invariant when the discriminant is nonzero). -/
def canonicalQSeriesJ (q : concreteLocalField) : concreteLocalField :=
  (TateCurve.weierstrassCurve concreteLocalField q).c₄ ^ 3 /
    (TateCurve.weierstrassCurve concreteLocalField q).Δ

/-- The q = 5 value of the general q-series j-invariant is the canonical
Tate j-invariant. -/
theorem canonicalQSeriesJ_five_eq :
    canonicalQSeriesJ (5 : concreteLocalField) =
      TateCurvePadic.tateJInvariant fivePrimeLabelScratch := by
  rw [TateCurvePadic.tateJInvariant_eq]
  rfl

/-- A q-series inverse-j candidate for the concrete split curve: a nonzero
contracting q whose q-series j-invariant is the split curve's j-invariant.
This records only the q-series side; it does not assert Tate uniformization. -/
def IsQSeriesInverseJParameter (q : concreteLocalField) : Prop :=
  q ≠ 0 ∧ ‖q‖ < 1 ∧ canonicalQSeriesJ q = concreteSplitCurveLocal.j

/-- A necessary norm condition for a q-series inverse-j parameter, conditional
on the general q-series norm relation for j.  The norm relation is the missing
general-q API; the tree currently proves it only at q = l.value. -/
theorem qSeriesInverseJParameter_norm
    (q : concreteLocalField)
    (h : IsQSeriesInverseJParameter q)
    (h_norm_relation : ‖canonicalQSeriesJ q‖ = (‖q‖)⁻¹) :
    ‖q‖ = (5 : ℝ)⁻¹ := by
  have hjnorm : ‖canonicalQSeriesJ q‖ = ‖concreteSplitCurveLocal.j‖ :=
    congrArg norm h.2.2
  rw [h_norm_relation, concreteSplitCurveLocal_j_norm_scratch] at hjnorm
  have hinv := congrArg Inv.inv hjnorm
  simpa using hinv

/-- A necessary congruence condition for any q-series inverse-j parameter,
conditional on the q-expansion integrality lemma
j(q) - q^{-1} in Z_5.  The conclusion is q / 5 = -1 (mod 5), so in particular
q cannot be the explicit q = 5 candidate. -/
theorem qSeriesInverseJParameter_congruence
    (q : concreteLocalField)
    (hq_ne : q ≠ 0)
    (hq_norm : ‖q‖ = (5 : ℝ)⁻¹)
    (hj : canonicalQSeriesJ q = concreteSplitCurveLocal.j)
    (hintegral : ‖canonicalQSeriesJ q - q⁻¹‖ ≤ 1) :
    ‖q / 5 + 1‖ < 1 := by
  have h5norm : ‖(5 : concreteLocalField)‖ = (1 / 5 : ℝ) :=
    five_norm_five
  have hu_norm : ‖q / 5‖ = 1 := by
    rw [norm_div, hq_norm, h5norm]
    norm_num
  have hu_ne : q / 5 ≠ 0 := by
    exact div_ne_zero hq_ne (by norm_num)
  have hsplit : ‖(5 : concreteLocalField) * canonicalQSeriesJ q + 1‖ < 1 := by
    rw [hj]
    exact concreteSplitCurveLocal_five_mul_j_add_one_norm_lt_one
  have hdiv : (q / 5)⁻¹ = (5 : concreteLocalField) * q⁻¹ := by
    rw [div_eq_mul_inv, mul_inv_rev, inv_inv]
  have h5j :
      (5 : concreteLocalField) * canonicalQSeriesJ q =
        (q / 5)⁻¹ + (5 : concreteLocalField) *
          (canonicalQSeriesJ q - q⁻¹) := by
    rw [hdiv]
    ring
  have hcorr :
      ‖(5 : concreteLocalField) * (canonicalQSeriesJ q - q⁻¹)‖ ≤
        (1 / 5 : ℝ) := by
    rw [norm_mul, h5norm]
    calc
      (1 / 5 : ℝ) * ‖canonicalQSeriesJ q - q⁻¹‖ ≤
          (1 / 5 : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left hintegral (by norm_num)
      _ = (1 / 5 : ℝ) := by norm_num
  have hcorr_lt :
      ‖(5 : concreteLocalField) * (canonicalQSeriesJ q - q⁻¹)‖ < 1 :=
    lt_of_le_of_lt hcorr (by norm_num)
  have hsum :
      ‖(q / 5)⁻¹ + (5 : concreteLocalField) *
          (canonicalQSeriesJ q - q⁻¹) + 1‖ < 1 := by
    rw [← h5j]
    exact hsplit
  have hdecomp :
      (q / 5)⁻¹ + 1 =
        ((q / 5)⁻¹ + (5 : concreteLocalField) *
            (canonicalQSeriesJ q - q⁻¹) + 1) -
          (5 : concreteLocalField) * (canonicalQSeriesJ q - q⁻¹) := by
    ring
  have hsmall : ‖(q / 5)⁻¹ + 1‖ < 1 := by
    rw [hdecomp, sub_eq_add_neg]
    exact lt_of_le_of_lt (Padic.nonarchimedean _ _)
      (max_lt hsum (by simpa using hcorr_lt))
  have hmul :
      q / 5 + 1 = (q / 5) * ((q / 5)⁻¹ + 1) := by
    field_simp [hu_ne]
    ring
  rw [hmul, norm_mul, hu_norm, one_mul]
  exact hsmall

/-- The explicit q = 5 candidate is not a q-series inverse-j parameter for the
split curve.  This is unconditional: it uses the exact unit-part computation,
not the missing analytic theorem. -/
theorem five_not_qSeriesInverseJParameter :
    ¬ IsQSeriesInverseJParameter (5 : concreteLocalField) := by
  rintro ⟨-, -, hj⟩
  have hcontr : TateCurvePadic.tateJInvariant fivePrimeLabelScratch =
      concreteSplitCurveLocal.j := by
    rw [← canonicalQSeriesJ_five_eq]
    exact hj
  exact tateJInvariant_five_ne_split_j hcontr

/-! ## Exact missing analytic statement (no inhabitant is constructed) -/

/-- The precise q-series inverse-j existence statement that is not proved here:
there is a nonzero contracting q in Q_5 whose q-series j-invariant is the
split curve's j-invariant.  This is a Prop; no theorem in this file inhabits it. -/
def MissingInverseJQParameterExistence : Prop :=
  ∃ q : concreteLocalField,
    q ≠ 0 ∧ ‖q‖ < 1 ∧ canonicalQSeriesJ q = concreteSplitCurveLocal.j

/-- The stronger missing analytic interface: a curve-indexed Tate
uniformization of the concrete split punctured curve at the concrete place
above 5, at some finite-place q-candidate.  This is the exact
CurveIndexedTateUniformization contract with no constructor. -/
def MissingCurveIndexedTateUniformizationAtFive : Prop :=
  ∃ parameter : NumberFieldFinitePlace.FinitePlaceQCandidate
      (concreteFivePlace),
    Nonempty (CurveIndexedTateUniformization concreteSplitPuncturedCurve
      concreteFivePlace parameter)

end

end LeanFormal.IUT.IUTII.Frobenioid.Example36.TateInverseJ

