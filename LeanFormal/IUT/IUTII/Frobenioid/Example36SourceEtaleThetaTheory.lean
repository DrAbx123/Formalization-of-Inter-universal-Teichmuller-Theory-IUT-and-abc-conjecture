/-
  # Task-117: actual source etale theta theory — constructions and exact obstruction

  This module records the actual source-theater / Tate-parameter constructions
  that are available in the tree and the exact missing source etale theta
  theorem that prevents the independent fields of
  SourceCurveEtaleThetaIdentificationCard from being inhabited.

  ## Actual constructions

  * The source theater's arithmetic curve is the actual split curve
    concreteSplitPuncturedCurve.baseChange GaussianField (theorem
    sourceTheater_curve_eq_split), while the separate curve
    sourceOncePuncturedEllipticCurve is the Weierstrass curve
    y^2 = x^3 - x over Q (sourceCurve_eq).  These two curve models are proved
    DIFFERENT after base change to GaussianField by comparing the a1
    coefficient (0 versus 1): sourceTheaterCurve_ne_sourceCurve_baseChange.
  * The source curve y^2 = x^3 - x has discriminant 64
    (sourceCurve_delta), a 5-adic unit; its reduction at 5 is good and it
    cannot supply a split-multiplicative Tate q-parameter at 5.  The split
    curve, by contrast, actually has split multiplicative reduction at the
    concrete place above 5 (concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_five).
  * An actual finite-place q-candidate exists at the selected place above 5
    (concreteFiveQCandidate, from the actual completed-DVR construction
    finitePlaceQCandidate_nonempty), and the explicit actual Tate parameter
    q = 5 in Q_5 is constructed by ConcreteTateParameter.canonical; its norm is
    exactly gaussianFiveThetaQ = 1/5
    (concreteTateParameter_canonical_norm_eq_gaussianFiveThetaQ).
  * Actual source-theater theta data is tied to the analytic model: the
    source theater q is gaussianFiveThetaQ (sourceTheater_theta_q_eq_analytic),
    and every source theta scale is the actual Gaussian special value
    (sourceTheater_theta_scale_eq_analytic).
  * Actual theta-link obstruction: every HodgeTheaterLink from the source
    theater forces the target q to be gaussianFiveThetaQ
    (link_target_theta_q), so no actual HodgeTheaterLink in the tree can
    realize a nontrivial q-transport (no_link_to_different_theta_q).  The
    second-theater link is therefore necessarily q-preserving, not a source
    Theta-link.

  ## Exact missing theorem (reported, not frozen as a card)

  1. CurveIndexedTateUniformization concreteSplitPuncturedCurve
     concreteFivePlace parameter (Foundations/Geometry/TateUniformizationContract)
     has NO constructor in the tree.  It is precisely the missing Tate
     uniformization: canonical q-series ellipticity, an actual coordinate
     identification with the split curve's completion, quotient point
     uniformization and its absolute-Galois equivariance.
  2. There is no construction of an etale theta function / theta
     characteristic / line-bundle section on the source curve (or Tate
     carrier), no actual theta q-expansion and no theta special-value
     evaluation beyond the finite theta packet.  In particular no definition
     of the source etale theta carrier, Theta-link, or their compatibility
     with the analytic Jacobi theta model exists in the tree.
  3. The source curve model is ambiguous unless the source theater split curve
     is selected: sourceOncePuncturedEllipticCurve = y^2 = x^3 - x has good
     reduction at 5 and no split-multiplicative q-parameter.

  Consequently the independent fields of SourceCurveEtaleThetaIdentificationCard
  are NOT inhabited by this file.  The task remains OPEN; no card, no refl
  equivalence, no finite-packet or scalar substitution is used.

  Source correspondence: IUT I, Definition 3.1(c); IUT II, theta evaluation and
  q-expansion; Tate uniformization at split multiplicative places.
-/

import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaGenerator
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier
import LeanFormal.IUT.IUTII.Frobenioid.Example36ThetaGeneratorFeasibility
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract
import LeanFormal.IUT.Foundations.Geometry.ConcreteTateParameter
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace SourceEtaleThetaTheory

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.IUTII.Frobenioid.Example36.ThetaGeneratorFeasibility
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open LeanFormal.IUT.NumberFieldFinitePlace

local instance gaussianPolynomialIrreducibleFactTheory :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactTheory : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

noncomputable section

/-! ## 1. The two actual source curve models -/

/-- The prime label 5 as an actual PrimeGeFive. -/
def fivePrimeLabel : PrimeGeFive where
  value := 5
  prime := Nat.prime_five
  ge_five := by norm_num

local instance fivePrimeLabelFactTheory : Fact (Nat.Prime fivePrimeLabel.value) :=
  ⟨fivePrimeLabel.prime⟩

@[simp] theorem fivePrimeLabel_value : fivePrimeLabel.value = 5 :=
  rfl

/-- The source theater's arithmetic curve is the actual split curve base-changed
to the Gaussian field. -/
theorem sourceTheater_curve_eq_split (l : PrimeGeFive) :
    (sourceTheater l).arithmetic.curve.curve =
      (concreteSplitPuncturedCurve.baseChange GaussianField).curve := by
  rw [sourceTheater_arithmetic_curve l]

/-- The separate source curve is the actual Weierstrass curve y^2 = x^3 - x. -/
theorem sourceCurve_eq_sourceOnce :
    sourceOncePuncturedEllipticCurve.curve = curveY2EqX3SubX :=
  rfl

/-- The a1 coefficient of the source theater's split curve is 1. -/
theorem sourceTheater_curve_a₁ (l : PrimeGeFive) :
    (sourceTheater l).arithmetic.curve.curve.a₁ = (1 : GaussianField) := by
  rw [sourceTheater_curve_eq_split]
  simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    concreteSplitPuncturedCurve, concreteSplitCurve]

/-- The a1 coefficient of the base-changed source curve y^2 = x^3 - x is 0. -/
theorem sourceCurve_baseChange_a₁ :
    (sourceOncePuncturedEllipticCurve.curve.baseChange GaussianField).a₁ =
      (0 : GaussianField) := by
  rw [sourceCurve_eq_sourceOnce]
  simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    curveY2EqX3SubX]

/-- **The two candidate source curve models are genuinely different.**  The
source theater's split curve and the base change of sourceOncePuncturedEllipticCurve
have different a1 coefficients (1 versus 0). -/
theorem sourceTheaterCurve_ne_sourceCurve_baseChange (l : PrimeGeFive) :
    (sourceTheater l).arithmetic.curve.curve ≠
      sourceOncePuncturedEllipticCurve.curve.baseChange GaussianField := by
  intro h
  have h1 := congrArg (fun C : WeierstrassCurve GaussianField => C.a₁) h
  rw [sourceTheater_curve_a₁ l, sourceCurve_baseChange_a₁] at h1
  norm_num at h1

/-- The discriminant of the actual source curve y^2 = x^3 - x is 64. -/
theorem sourceCurve_delta :
    curveY2EqX3SubX.Δ = (64 : ℚ) := by
  norm_num [curveY2EqX3SubX, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The source curve discriminant 64 is not divisible by the selected prime 5:
the curve has good reduction at 5 and supplies no split-multiplicative Tate
q-parameter there. -/
theorem sourceCurve_delta_not_divisible_by_five :
    (64 : ℕ) % 5 ≠ 0 := by
  norm_num

/-! ## 2. The actual finite-place q-candidate and the explicit Tate q = 5 -/

/-- An actual q-candidate at the selected place above 5, from the completed-DVR
construction (not from an arbitrary field element). -/
noncomputable def concreteFiveQCandidate :
    NumberFieldFinitePlace.FinitePlaceQCandidate concreteFivePlace :=
  Classical.choice
    (NumberFieldFinitePlace.finitePlaceQCandidate_nonempty concreteFivePlace)

theorem concreteFiveQCandidate_exists :
    Nonempty (NumberFieldFinitePlace.FinitePlaceQCandidate concreteFivePlace) :=
  ⟨concreteFiveQCandidate⟩

theorem concreteFiveQCandidate_q_ne_zero :
    concreteFiveQCandidate.q ≠ 0 :=
  concreteFiveQCandidate.q_ne_zero

theorem concreteFiveQCandidate_valuation_lt_one :
    (Valued.v concreteFiveQCandidate.q : WithZero (Multiplicative ℤ)) < 1 :=
  concreteFiveQCandidate.valuation_lt_one

/-- The explicit actual Tate parameter q = 5 in Q_5 (from
ConcreteTateParameter.canonical). -/
theorem concreteTateParameter_canonical_q :
    (ConcreteTateParameter.canonical fivePrimeLabel).q =
      (fivePrimeLabel.value : ℚ_[fivePrimeLabel.value]) :=
  ConcreteTateParameter.canonical_q fivePrimeLabel

/-- The explicit actual Tate parameter has norm exactly
gaussianFiveThetaQ = 1/5. -/
theorem concreteTateParameter_canonical_norm_eq_gaussianFiveThetaQ :
    ‖(ConcreteTateParameter.canonical fivePrimeLabel).q‖ =
      gaussianFiveThetaQ := by
  rw [concreteTateParameter_canonical_q, Padic.norm_p (p := fivePrimeLabel.value)]
  rw [show (fivePrimeLabel.value : ℝ) = 5 by exact_mod_cast fivePrimeLabel_value,
    gaussianFiveThetaQ_eq_inv_five]

/-- The split curve actually has split multiplicative reduction at the concrete
place above 5 (actual theorem of the tree). -/
theorem splitCurve_hasSplitMultiplicativeReductionAt_five :
    concreteSplitPuncturedCurve.HasSplitMultiplicativeReductionAt
      concreteFivePlace :=
  concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_five

/-- The split curve actually has multiplicative reduction at the concrete place
above 5. -/
theorem splitCurve_hasMultiplicativeReductionAt_five :
    concreteSplitPuncturedCurve.HasMultiplicativeReductionAt concreteFivePlace :=
  concreteSplitPuncturedCurve_hasMultiplicativeReductionAt_five

/-! ## 3. Actual source-theater / analytic theta compatibility -/

/-- The source theater's theta q is the actual gaussianFiveThetaQ. -/
theorem sourceTheater_theta_q_eq_analytic (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.q = gaussianFiveThetaQ :=
  sourceTheater_theta_q l

/-- The source theater's theta scales are the actual Gaussian special values. -/
theorem sourceTheater_theta_scale_eq_analytic (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    (sourceTheater l).thetaPacket.scale j =
      realThetaValue gaussianFiveThetaQ j.1 :=
  sourceTheater_theta_scale l j

/-- The concrete analytic theta carrier has q equal to the source theater's
actual theta q. -/
theorem analyticThetaCarrierConcrete_q_eq_sourceTheater (l : PrimeGeFive) :
    analyticThetaCarrierConcrete.q = (sourceTheater l).thetaPacket.q := by
  rw [analyticThetaCarrierConcrete_q, sourceTheater_theta_q_eq_analytic]

/-- The source theater's theta scales are the analytic integer q-expansion
coefficients at the concrete q. -/
theorem sourceTheater_theta_scale_eq_analyticThetaQExpansion
    (l : PrimeGeFive) (j : SignedLabel l.value) :
    (sourceTheater l).thetaPacket.scale j =
      realThetaValue analyticThetaCarrierConcrete.q j.1 := by
  rw [sourceTheater_theta_scale_eq_analytic, analyticThetaCarrierConcrete_q]

/-! ## 4. Actual Theta-link obstruction -/

/-- Every actual HodgeTheaterLink from the source theater forces the target q to
be gaussianFiveThetaQ. -/
theorem sourceLink_target_theta_q {l : PrimeGeFive}
    {T : HodgeTheater l (FinitePrimePlace 2 7)}
    (link : HodgeTheaterLink (sourceTheater l) T) :
    T.thetaPacket.q = gaussianFiveThetaQ :=
  SourceTheaterCarrier.link_target_theta_q link

/-- A theater with a different theta q admits no actual HodgeTheaterLink from
the source theater: the actual link relation is q-preserving. -/
theorem no_link_to_different_theta_q (l : PrimeGeFive)
    {T : HodgeTheater l (FinitePrimePlace 2 7)}
    (h : T.thetaPacket.q ≠ gaussianFiveThetaQ) :
    ¬ Nonempty (HodgeTheaterLink (sourceTheater l) T) :=
  ThetaGeneratorFeasibility.no_link_to_different_theta_q h

/-- **The actual link relation cannot realize a nontrivial Theta-link.**  A
target with any q different from the source q is not actual-linkable.  In
particular the q |-> (n+1) q Theta-link of the source theory is not realized by
HodgeTheaterLink. -/
theorem actual_link_cannot_shift_theta_q (l : PrimeGeFive) (q' : ℝ)
    (hq' : q' ≠ gaussianFiveThetaQ) :
    ¬ ∃ T : HodgeTheater l (FinitePrimePlace 2 7),
        T.thetaPacket.q = q' ∧ Nonempty (HodgeTheaterLink (sourceTheater l) T) := by
  rintro ⟨T, hT, hlink⟩
  exact no_link_to_different_theta_q l (by rw [hT]; exact hq') hlink

/-! ## 5. Summary of actual constructions and the missing theorem -/

/-- **Actual constructions and exact obstruction.**  The source theater's actual
curve is the split curve (sourceTheater_curve_eq_split), different from
sourceOncePuncturedEllipticCurve (sourceTheaterCurve_ne_sourceCurve_baseChange);
the source curve has discriminant 64 (sourceCurve_delta) and no
split-multiplicative q at 5; the split curve actually has split multiplicative
reduction at the concrete place above 5; an actual finite-place q-candidate
exists, and the explicit actual Tate parameter q = 5 in Q_5 has norm
gaussianFiveThetaQ = 1/5; source-theater theta q/scales agree with the actual
analytic values; and the actual link relation is q-preserving.  The missing
source etale theta theorem (CurveIndexedTateUniformization, theta function /
line-bundle section / q-expansion / special values, and nontrivial Theta-link)
is NOT constructed. -/
theorem sourceEtaleThetaTheory_summary (l : PrimeGeFive) :
    ((sourceTheater l).arithmetic.curve.curve =
      (concreteSplitPuncturedCurve.baseChange GaussianField).curve) ∧
    ((sourceTheater l).arithmetic.curve.curve ≠
      sourceOncePuncturedEllipticCurve.curve.baseChange GaussianField) ∧
    (curveY2EqX3SubX.Δ = (64 : ℚ)) ∧
    (concreteSplitPuncturedCurve.HasSplitMultiplicativeReductionAt
      concreteFivePlace) ∧
    (Nonempty (NumberFieldFinitePlace.FinitePlaceQCandidate concreteFivePlace)) ∧
    (‖(ConcreteTateParameter.canonical fivePrimeLabel).q‖ =
      gaussianFiveThetaQ) ∧
    ((sourceTheater l).thetaPacket.q = gaussianFiveThetaQ) ∧
    (∀ j : SignedLabel l.value,
      (sourceTheater l).thetaPacket.scale j =
        realThetaValue gaussianFiveThetaQ j.1) ∧
    (∀ {T : HodgeTheater l (FinitePrimePlace 2 7)},
      HodgeTheaterLink (sourceTheater l) T → T.thetaPacket.q = gaussianFiveThetaQ) := by
  refine ⟨sourceTheater_curve_eq_split l,
    sourceTheaterCurve_ne_sourceCurve_baseChange l,
    sourceCurve_delta,
    splitCurve_hasSplitMultiplicativeReductionAt_five,
    concreteFiveQCandidate_exists,
    concreteTateParameter_canonical_norm_eq_gaussianFiveThetaQ,
    sourceTheater_theta_q_eq_analytic l,
    sourceTheater_theta_scale_eq_analytic l,
    fun link => sourceLink_target_theta_q link⟩

end

end SourceEtaleThetaTheory
end Example36
end Frobenioid
end IUTII
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for task-117 (blocking source etale theta theory).  The actual
constructions are the split-curve source model, its split multiplicative
reduction at the concrete place above 5, the actual finite-place q-candidate and
explicit q = 5 with norm gaussianFiveThetaQ, the source-theater/analytic theta
q and scale compatibility, the source curve discriminant 64, and the proof that
the actual HodgeTheaterLink relation is q-preserving.  The EXACT MISSING THEOREM
is the curve-indexed Tate uniformization
(CurveIndexedTateUniformization concreteSplitPuncturedCurve concreteFivePlace
parameter) and, on top of it, a construction of the etale theta function /
theta characteristic / line-bundle section / actual q-expansion / special values
and nontrivial source Theta-link.  No such construction exists in the tree: no
constructor of CurveIndexedTateUniformization, no theta-function or line-bundle
section API, and HodgeTheaterLink forces equal q, so it cannot express the
source Theta-link.  The independent fields of
SourceCurveEtaleThetaIdentificationCard therefore remain uninhabited and
task-117/task-107 remain open.  No card, refl equivalence, finite-packet or
scalar substitution is used. -/
def example36SourceEtaleThetaTheory : Obligation :=
  { id := "IUT-II.example36-source-etale-theta-theory"
    source :=
      "IUT I, Definition 3.1(c); IUT II, theta evaluation and q-expansion; " ++
        "Tate uniformization at split multiplicative places"
    status := VerificationStatus.interface
    note :=
      "Actual: sourceTheater_curve_eq_split (source theater curve is " ++
        "concreteSplitPuncturedCurve.baseChange GaussianField); " ++
        "sourceCurve_eq_sourceOnce; sourceTheater_curve_a₁ = 1 vs " ++
        "sourceCurve_baseChange_a₁ = 0, hence " ++
        "sourceTheaterCurve_ne_sourceCurve_baseChange (the two source models " ++
        "are genuinely different); sourceCurve_delta = 64 and " ++
        "sourceCurve_delta_not_divisible_by_five (good reduction at 5, no " ++
        "split-multiplicative q there); " ++
        "splitCurve_hasSplitMultiplicativeReductionAt_five (actual split " ++
        "multiplicative reduction at concreteFivePlace); " ++
        "concreteFiveQCandidate (actual finite-place q-candidate from " ++
        "finitePlaceQCandidate_nonempty); " ++
        "concreteTateParameter_canonical_q = 5 in Q_5 and " ++
        "concreteTateParameter_canonical_norm_eq_gaussianFiveThetaQ; " ++
        "sourceTheater_theta_q_eq_analytic and " ++
        "sourceTheater_theta_scale_eq_analytic (actual source theta q/scales " ++
        "equal gaussianFiveThetaQ and realThetaValue); sourceLink_target_theta_q " ++
        "and no_link_to_different_theta_q (actual HodgeTheaterLink forces equal " ++
        "theta q); actual_link_cannot_shift_theta_q (no nontrivial q-shifting " ++
        "Theta-link via the actual link relation).  MISSING (exact theorem): " ++
        "CurveIndexedTateUniformization concreteSplitPuncturedCurve " ++
        "concreteFivePlace parameter has no constructor in the tree; no " ++
        "etale theta function/theta characteristic/line-bundle section, no " ++
        "actual theta q-expansion/special values beyond the finite packet, and " ++
        "no nontrivial source Theta-link exist.  These are the genuine missing " ++
        "C-layer/source theorems.  The corrected task-107 card is bound to the " ++
        "actual split source curve and inhabited by actual q-expansion/evaluation " ++
        "data; only the full source etale theta function/section/Theta-link " ++
        "remains missing, and the tasks remain open.  No refl/definitional " ++
        "source:=target, no card, no finite-packet substitution."
    dependsOn :=
      [ "Foundations.NumberField.local-q-parameter-valuation",
        "Foundations.Geometry.concrete-split-curve-five-place",
        "Foundations.Geometry.concrete-tate-parameter",
        "Foundations.Geometry.curve-indexed-tate-uniformization",
        "IUT-II.example36-source-theta-generator",
        "IUT-II.example36-theta-generator-feasibility" ] }

end LeanFormal.IUT.Audit
