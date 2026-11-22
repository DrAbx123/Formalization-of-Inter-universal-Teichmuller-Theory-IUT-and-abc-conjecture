/-
U-R C2 hP5 J1 same-q bridge (J1 lane).

Goal (target):  -M_paper_v2 T <= ksThetaHullLogRoot_lam T.

SIGNS / DIRECTION (important).  The lambda-weighted lower bound proved in
Mzk1URThetaKHP5LamActual is

  -S <= ksThetaHullLogRoot_lam,   S := sum_b thetaLamWeight_b * urCeilC_b * log p_b.

Hence the target -M <= theta follows from the comparison

  S <= M_paper_v2      (theta-side ceiling sum at most the q-pilot magnitude),

NOT from M_paper_v2 <= S.  The context file Mzk1URThetaKHP5BridgeActual states
M_paper_v2 <= S; its proof term (neg_le_neg hbridge) yields -S <= -M, which
cannot be chained with -S <= theta, so that reduction is ill-typed as a proof
of -M <= theta (the watchdog is failing that file).  The direction below is the
one that matches the signs of ksThetaHullLog_lower.

WHAT IS PROVED HERE (unconditional):
* MpaperV2_eq_fiber_sum: M_paper_v2 is the (1/(2l))(1/[F:Q])-multiple of the
  full F-fibre sum of f_P c_P log p_P (definitional shape of
  qPilotMagnitudePaper_v2, paper Def 1.9 normalized degree);
* j1_ksRootCoeff_le_urCeilC and qVFamNormalizedCoefficient_le_twoL_mul_urCeilC:
  the unrounded normalized q coefficient c_norm_b is at most 2l*urCeilC_b;

WHAT IS REDUCED (conditional, and exactly the J1 same-q content):
* hbridge_of_fiberLe: S <= M_paper_v2 follows from the per-b F-fibre comparison

    [F:Q] * 2l * thetaLamWeight_b * (urCeilC_b * log p_b) <= fiberQTerm_b,

  i.e. the theta ceiling contribution at b is dominated by the q-fibre order
  contribution;
* neg_MpaperV2_le_thetaLam_of_fiberLe: the target follows from it together with
  the lambda-weighted hull lower bound hlower : -S <= ksThetaHullLogRoot_lam.
  That lower bound is the DONE theorem
  Mzk1URThetaKHP5LamActual.ksThetaHullLogRoot_lam_lower; it is kept as an
  explicit argument here because the KLower/KHP5Lam modules are being split
  (KLowerCore/KLowerBound) while this file was written.

WHY THE PER-FIBRE COMPARISON IS NOT DISCHARGED HERE (precise gap):
  (1) fiberQTerm sums the q-candidate order orderAtFPlace b P over ALL F-places
      P over b.1 (the full fibre of V(F)^bad over V^bad_mod, weight f_P/[F:Q]),
      while the theta side is indexed by Bad (F_mod places) and reads only the
      selected lift nativeBadToFPlace.  orderAtFPlace is Classical.choice of
      T.clauseB.q_comparison P _, and the only tree-level order relation is
      S1413SourceKPlaceQComparisonActual.parameter_order_congr, which needs the
      two places to be syntactically equal.  No lemma equates or bounds the
      orders of two distinct F-places over the same moduli place (grep:
      orderAtFPlace occurs only in Mzk1ULQPilotMagnitudeV2Actual).
  (2) the selected-lift coefficient c_norm_b is the normalized spectral
      coefficient of the same q; via the donor power formula it equals
      order_b / e_b with e_b the absolute ramification index of the selected
      F-place over Q_p (cf. BadPlacePaperNormalizedComparisonActual, where
      paperCoefficient = order*f and c_norm = paperCoefficient - log(ratio)/log p).
      The correct per-fibre comparison therefore needs the same-q identification
      of the q-orders on the fibre together with the Galois constancy of e,f
      (F/F_mod is Galois by SourceClauseA.fmod_galois_spec); neither is
      formalized (the same-q identification is route 5.3 J1).
  The per-fibre comparison is exposed as an explicit hypothesis of the
  reduction theorem; it is not an axiom and not a renamed goal.

THIS FILE ONLY uses maxHeartbeats 1000000 (paper-level budget); RC list.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5J1SameQActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullUpperActual
open NumberField
open MeasureTheory

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- The F-fibre summand of qPilotMagnitudePaper_v2 at one bad moduli place. -/
noncomputable def fiberQTerm (b : Bad (nativePlaceSelection T)) : ℝ :=
  ∑ x ∈ (IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
    ((x.1.inertiaDeg ℤ : ℝ) * (orderAtFPlace T b x.1 x.2 : ℝ) *
      Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : ℝ))

/-- The theta-side summand of the bridge (thetaLamWeight * urCeilC * log p). -/
noncomputable def thetaTerm (b : Bad (nativePlaceSelection T)) : ℝ :=
  thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
    ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))

/-- M_paper_v2 is the (1/(2l))(1/[F:Q])-multiple of the full F-fibre sum. -/
theorem MpaperV2_eq_fiber_sum :
    M_paper_v2 (l := l) T =
      ((∑ b : Bad (nativePlaceSelection T), fiberQTerm T b) /
          (Module.finrank ℚ T.arithmetic.F : ℝ)) / (2 * (l.value : ℝ)) := by
  unfold M_paper_v2 qPilotMagnitudePaper_v2 fiberQTerm
  rfl

/-- Local form of the half-root-ceiling comparison (same statement as
Mzk1URThetaKHP5Actual.ksRootCoeff_le_urCeilC, on the KLowerCore carrier). -/
theorem j1_ksRootCoeff_le_urCeilC (b : Bad (nativePlaceSelection T)) :
    actualRootCoeff (l := l) T b () ≤ urCeilC (l := l) T b := by
  rw [urCeilC_eq (l := l) T b]
  unfold ksCeilCoeff
  exact le_ceilExp (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
    (K := CommonPrimeCompletion (ksPlace T b)) (urRootCoeff_nonneg' (l := l) T b)

/-- The unrounded q coefficient is at most 2l * urCeilC. -/
theorem qVFamNormalizedCoefficient_le_twoL_mul_urCeilC
    (b : Bad (nativePlaceSelection T)) :
    qVFamNormalizedCoefficient T b ≤ (2 * (l.value : ℝ)) * urCeilC (l := l) T b := by
  have hceil := j1_ksRootCoeff_le_urCeilC (l := l) T b
  have h2l : (0 : ℝ) < 2 * (l.value : ℝ) := by
    have hl : (0 : ℝ) < (l.value : ℝ) := by exact_mod_cast l.prime.pos
    linarith
  have hc : actualRootCoeff (l := l) T b () =
      qVFamNormalizedCoefficient T b / (2 * (l.value : ℝ)) := by
    unfold actualRootCoeff
    ring
  rw [hc] at hceil
  have hmul : (2 * (l.value : ℝ)) * (qVFamNormalizedCoefficient T b / (2 * (l.value : ℝ))) =
      qVFamNormalizedCoefficient T b :=
    mul_div_cancel₀ _ h2l.ne'
  have h := mul_le_mul_of_nonneg_left hceil h2l.le
  rwa [hmul] at h

/-! ## Correct-direction bridge: S <= M -/

/-- J1 same-q per-fibre comparison (theta contribution <= q fibre contribution)
implies the bridge inequality S <= M_paper_v2. -/
theorem hbridge_of_fiberLe
    (hfc : ∀ b : Bad (nativePlaceSelection T),
      (Module.finrank ℚ T.arithmetic.F : ℝ) * (2 * (l.value : ℝ)) * thetaTerm T b ≤
        fiberQTerm T b) :
    (∑ b : Bad (nativePlaceSelection T), thetaTerm T b) ≤ M_paper_v2 (l := l) T := by
  have hfr_pos : (0 : ℝ) < (Module.finrank ℚ T.arithmetic.F : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := T.arithmetic.F)
  have h2l_pos : (0 : ℝ) < 2 * (l.value : ℝ) := by
    have hl : (0 : ℝ) < (l.value : ℝ) := by exact_mod_cast l.prime.pos
    linarith
  have hden : (0 : ℝ) < (Module.finrank ℚ T.arithmetic.F : ℝ) * (2 * (l.value : ℝ)) :=
    mul_pos hfr_pos h2l_pos
  have hsum : (Module.finrank ℚ T.arithmetic.F : ℝ) * (2 * (l.value : ℝ)) *
        (∑ b : Bad (nativePlaceSelection T), thetaTerm T b) ≤
      ∑ b : Bad (nativePlaceSelection T), fiberQTerm T b := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ => hfc b)
  rw [MpaperV2_eq_fiber_sum (l := l) T, div_div, le_div_iff₀ hden]
  calc (∑ b : Bad (nativePlaceSelection T), thetaTerm T b) *
        ((Module.finrank ℚ T.arithmetic.F : ℝ) * (2 * (l.value : ℝ)))
      = (Module.finrank ℚ T.arithmetic.F : ℝ) * (2 * (l.value : ℝ)) *
          (∑ b : Bad (nativePlaceSelection T), thetaTerm T b) := by ring
    _ ≤ ∑ b : Bad (nativePlaceSelection T), fiberQTerm T b := hsum

/-- The hP5 target from the J1 same-q per-fibre comparison (correct direction)
and the lambda-weighted hull lower bound. -/
theorem neg_MpaperV2_le_thetaLam_of_fiberLe
    (hfc : ∀ b : Bad (nativePlaceSelection T),
      (Module.finrank ℚ T.arithmetic.F : ℝ) * (2 * (l.value : ℝ)) * thetaTerm T b ≤
        fiberQTerm T b)
    (hlower : -(∑ b : Bad (nativePlaceSelection T), thetaTerm T b) ≤
      ksThetaHullLogRoot_lam (l := l) T) :
    -M_paper_v2 (l := l) T ≤ ksThetaHullLogRoot_lam (l := l) T := by
  have hS : (∑ b : Bad (nativePlaceSelection T), thetaTerm T b) ≤ M_paper_v2 (l := l) T :=
    hbridge_of_fiberLe (l := l) T hfc
  exact (neg_le_neg hS).trans hlower

#print axioms MpaperV2_eq_fiber_sum
#print axioms j1_ksRootCoeff_le_urCeilC
#print axioms qVFamNormalizedCoefficient_le_twoL_mul_urCeilC
#print axioms hbridge_of_fiberLe
#print axioms neg_MpaperV2_le_thetaLam_of_fiberLe

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5J1SameQActual
end
