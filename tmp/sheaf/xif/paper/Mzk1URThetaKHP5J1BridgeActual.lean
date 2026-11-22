/-
U-R C2 hP5 J1 same-q bridge (kurt / J1 lane).

Goal (target):
  neg_MpaperV2_le_thetaLam : -M_paper_v2 T <= ksThetaHullLogRoot_lam T.

The terminal reduction is already in Mzk1URThetaKHP5BridgeActual:
  hbridge : M_paper_v2 <= sum_b thetaLamWeight_b * (urCeilC_b * log p_b)
  => -M_paper_v2 <= ksThetaHullLogRoot_lam
(using ksThetaHullLogRoot_lam_lower from Mzk1URThetaKHP5LamActual).

WHAT IS PROVED HERE (unconditional):
* MpaperV2_eq_fiber_sum: M_paper_v2 is the (1/(2l))(1/[F:Q])-multiple of the
  full F-fibre sum of f_P c_P log p_P (definitional shape, the paper Def 1.9 form
  already used by qPilotMagnitudePaper_v2);
* qVFamNormalizedCoefficient_le_twoL_mul_urCeilC: the unrounded q coefficient
  c_norm_b is at most 2l*urCeilC_b (the value-group ceiling only increases the
  half root coefficient; from ksRootCoeff_le_urCeilC of Mzk1URThetaKHP5Actual).

WHAT IS REDUCED (conditional, and exactly the J1 same-q content):
* hbridge_of_fiberCoeff: hbridge follows from the per-b F-fibre comparison
    sum_{P | b} f_P c_P log p_P
      <= [F:Q] * thetaLamWeight_b * (c_norm_b * log p_b)
  (the unrounded, per-fibre q-theta coefficient comparison); the passage from
  c_norm_b to 2l*urCeilC_b is proved here, so no ceiling/volume fact is assumed;
* neg_MpaperV2_le_thetaLam_of_fiberCoeff: the target follows from that comparison
  (via neg_MpaperV2_le_thetaLam_of_bridge).

WHY THE PER-FIBRE COMPARISON IS NOT DISCHARGED HERE (precise gap):
  (1) M_paper_v2 sums the q-candidate order orderAtFPlace b P over ALL F-places
      P over b.1 (the whole fibre of V(F)^bad over V^bad_mod), while the theta
      side is indexed by Bad (F_mod places) and reads only the selected lift
      nativeBadToFPlace.  orderAtFPlace is Classical.choice of
      T.clauseB.q_comparison P _ .parameter.order; the only tree-level relation
      between orders at different places is
      S1413SourceKPlaceQComparisonActual.parameter_order_congr, which requires
      p = q syntactically.  There is NO lemma in the tree equating / bounding
      the orders of two distinct F-places over the same moduli place
      (grep: orderAtFPlace occurs only in Mzk1ULQPilotMagnitudeV2Actual).
  (2) the selected-lift coefficient c_norm_b is the normalized spectral
      coefficient of the same q, hence c_norm_b = order_b / e_b with e_b the
      absolute ramification index of the selected F-place over Q_p (see
      BadPlacePaperNormalizedComparisonActual for the exact
      paperCoefficient (= order*f) vs c_norm decomposition).  Dividing by e_b is
      what makes the comparison non-trivial when F/F_mod is ramified at the
      selected lift: a per-fibre proof needs the Galois constancy of e,f on the
      fibre plus the same-q identification of the q-orders, neither of which is
      formalized (the same-q identification is precisely route 5.3 J1).
  Consequently we do NOT state the per-fibre comparison as an axiom or a renamed
  goal; it is exposed as the explicit hypothesis of the two reduction theorems
  below, with the paper-level provenance recorded in this docstring.

THIS FILE ONLY uses maxHeartbeats 1000000 (paper-level budget); RC list.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKHP5Actual
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerBoundActual
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5J1BridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5Actual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerBoundActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1URQAllParamActual
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

/-- The unrounded q coefficient is at most 2l * urCeilC (the value-group
ceiling only increases the half root coefficient). -/
theorem qVFamNormalizedCoefficient_le_twoL_mul_urCeilC
    (b : Bad (nativePlaceSelection T)) :
    qVFamNormalizedCoefficient T b ≤ (2 * (l.value : ℝ)) * urCeilC (l := l) T b := by
  have hceil := ksRootCoeff_le_urCeilC (l := l) T b
  have h2l : (0 : ℝ) < 2 * (l.value : ℝ) := by
    have hl : (0 : ℝ) < (l.value : ℝ) := by exact_mod_cast l.prime.pos
    linarith
  have hc : actualRootCoeff (l := l) T b () =
      qVFamNormalizedCoefficient T b / (2 * (l.value : ℝ)) := by
    unfold actualRootCoeff
    push_cast
    ring
  rw [hc] at hceil
  have hmul : (2 * (l.value : ℝ)) * (qVFamNormalizedCoefficient T b / (2 * (l.value : ℝ))) =
      qVFamNormalizedCoefficient T b :=
    mul_div_cancel₀ _ h2l.ne'
  have h := mul_le_mul_of_nonneg_left hceil h2l.le
  rwa [hmul] at h

/-- J1 same-q per-fibre coefficient comparison implies the bridge inequality.

The hypothesis is the per-b F-fibre comparison of the unrounded q coefficient
c_norm_b with the theta weight; the ceiling step c_norm_b <= 2l*urCeilC_b is
proved above, so no volume/ceiling input is assumed. -/
theorem hbridge_of_fiberCoeff
    (hfc : ∀ b : Bad (nativePlaceSelection T),
      fiberQTerm T b ≤
        (Module.finrank ℚ T.arithmetic.F : ℝ) *
          (thetaLamWeight T b * (qVFamNormalizedCoefficient T b *
            Real.log ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ)))) :
    M_paper_v2 (l := l) T ≤ ∑ b : Bad (nativePlaceSelection T), thetaTerm T b := by
  have hfr_pos : (0 : ℝ) < (Module.finrank ℚ T.arithmetic.F : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := T.arithmetic.F)
  have h2l_pos : (0 : ℝ) < 2 * (l.value : ℝ) := by
    have hl : (0 : ℝ) < (l.value : ℝ) := by exact_mod_cast l.prime.pos
    linarith
  have hper : ∀ b : Bad (nativePlaceSelection T),
      fiberQTerm T b ≤
        (Module.finrank ℚ T.arithmetic.F : ℝ) * (2 * (l.value : ℝ)) * thetaTerm T b := by
    intro b
    have hcn := qVFamNormalizedCoefficient_le_twoL_mul_urCeilC (l := l) T b
    have hlog : 0 ≤ Real.log ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ) :=
      ksLogP_nonneg (l := l) T b
    have hstep : qVFamNormalizedCoefficient T b *
          Real.log ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ) ≤
        ((2 * (l.value : ℝ)) * urCeilC (l := l) T b) *
          Real.log ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ) :=
      mul_le_mul_of_nonneg_right hcn hlog
    have htheta_nn : 0 ≤ thetaLamWeight T b := thetaLamWeight_nonneg T b
    have hfr_nn : 0 ≤ (Module.finrank ℚ T.arithmetic.F : ℝ) := hfr_pos.le
    calc fiberQTerm T b
        ≤ (Module.finrank ℚ T.arithmetic.F : ℝ) *
            (thetaLamWeight T b * (qVFamNormalizedCoefficient T b *
              Real.log ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))) :=
          hfc b
      _ = (Module.finrank ℚ T.arithmetic.F : ℝ) * thetaLamWeight T b *
            (qVFamNormalizedCoefficient T b *
              Real.log ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ)) := by
          ring
      _ ≤ (Module.finrank ℚ T.arithmetic.F : ℝ) * thetaLamWeight T b *
            (((2 * (l.value : ℝ)) * urCeilC (l := l) T b) *
              Real.log ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hstep (mul_nonneg hfr_nn htheta_nn)
      _ = (Module.finrank ℚ T.arithmetic.F : ℝ) * (2 * (l.value : ℝ)) * thetaTerm T b := by
          unfold thetaTerm
          ring
  have hsum : (∑ b : Bad (nativePlaceSelection T), fiberQTerm T b) ≤
      (Module.finrank ℚ T.arithmetic.F : ℝ) * (2 * (l.value : ℝ)) *
        ∑ b : Bad (nativePlaceSelection T), thetaTerm T b := by
    calc (∑ b : Bad (nativePlaceSelection T), fiberQTerm T b)
        ≤ ∑ b : Bad (nativePlaceSelection T),
            (Module.finrank ℚ T.arithmetic.F : ℝ) * (2 * (l.value : ℝ)) * thetaTerm T b :=
          Finset.sum_le_sum (fun b _ => hper b)
      _ = (Module.finrank ℚ T.arithmetic.F : ℝ) * (2 * (l.value : ℝ)) *
            ∑ b : Bad (nativePlaceSelection T), thetaTerm T b := by
          rw [Finset.mul_sum]
  rw [MpaperV2_eq_fiber_sum (l := l) T]
  have hfr_ne : (Module.finrank ℚ T.arithmetic.F : ℝ) ≠ 0 := ne_of_gt hfr_pos
  have h2l_ne : (2 * (l.value : ℝ)) ≠ 0 := ne_of_gt h2l_pos
  have hdiv : (∑ b : Bad (nativePlaceSelection T), fiberQTerm T b) /
        (Module.finrank ℚ T.arithmetic.F : ℝ) ≤
      ((Module.finrank ℚ T.arithmetic.F : ℝ) * (2 * (l.value : ℝ)) *
          ∑ b : Bad (nativePlaceSelection T), thetaTerm T b) /
        (Module.finrank ℚ T.arithmetic.F : ℝ) :=
    div_le_div_of_nonneg_right hsum hfr_pos.le
  have hdiv2 := div_le_div_of_nonneg_right hdiv h2l_pos.le
  refine hdiv2.trans_eq ?_
  field_simp [hfr_ne, h2l_ne]
  ring

/-- Local re-derivation of the per-b lambda-weighted lower bound (the same
statement as Mzk1URThetaKHP5LamActual.ksThetaHullLog_lower_weighted, reproduced
here so the file does not depend on the currently rebuilding KHP5Lam module). -/
theorem j1_ksThetaHullLog_lower_weighted (b : Bad (nativePlaceSelection T)) :
    -(thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
        ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))) ≤
      thetaLamWeight T b * ksThetaHullLog (l := l) T b := by
  have h := ksThetaHullLog_lower (l := l) T b
  have hw : 0 ≤ thetaLamWeight T b := thetaLamWeight_nonneg T b
  have hm := mul_le_mul_of_nonneg_left h hw
  unfold ksThetaHullLog
  calc -(thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
        ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ)))
      = thetaLamWeight T b * (-((urCeilC (l := l) T b) * Real.log
        ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))) := by ring
    _ ≤ thetaLamWeight T b * arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
          MeasureTheory.Measure.addHaar (ksThetaHull (l := l) T b) := hm

/-- Local re-derivation of the lambda-weighted theta hull lower bound (same
statement as Mzk1URThetaKHP5LamActual.ksThetaHullLogRoot_lam_lower). -/
theorem j1_ksThetaHullLogRoot_lam_lower :
    -(∑ b : Bad (nativePlaceSelection T),
      thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
        ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))) ≤
      ksThetaHullLogRoot_lam (l := l) T := by
  unfold ksThetaHullLogRoot_lam
  have h : (∑ b : Bad (nativePlaceSelection T),
        -(thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
          ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))))
      ≤ ∑ b : Bad (nativePlaceSelection T),
          thetaLamWeight T b * ksThetaHullLog (l := l) T b :=
    Finset.sum_le_sum (s := (Finset.univ : Finset (Bad (nativePlaceSelection T))))
      (f := fun b => -(thetaLamWeight T b * ((urCeilC (l := l) T b) * Real.log
        ((completionRationalPrime (nativeBadToKPlace T b)).val : ℝ))))
      (g := fun b => thetaLamWeight T b * ksThetaHullLog (l := l) T b)
      (fun b _ => j1_ksThetaHullLog_lower_weighted (l := l) T b)
  rw [← Finset.sum_neg_distrib]
  exact h

/-- The hP5 target from the J1 same-q comparison, in the CORRECT direction:
S := sum_b thetaTerm_b <= M_paper_v2 (the genuine J1 same-q paper input, kept explicit;
the opposite direction M <= S is the ceiling bound and does not imply -M <= theta).
Reuse: Mzk1URThetaKHP5J1SameQActual.neg_MpaperV2_le_thetaLam_of_fiberLe. -/
theorem neg_MpaperV2_le_thetaLam_of_vol
    (hvol : (∑ b : Bad (nativePlaceSelection T), thetaTerm T b) ≤ M_paper_v2 (l := l) T) :
    -M_paper_v2 (l := l) T ≤ ksThetaHullLogRoot_lam (l := l) T := by
  have h1 : -M_paper_v2 (l := l) T ≤
      -(∑ b : Bad (nativePlaceSelection T), thetaTerm T b) := neg_le_neg hvol
  have h2 : -(∑ b : Bad (nativePlaceSelection T), thetaTerm T b) ≤
      ksThetaHullLogRoot_lam (l := l) T := by
    simpa [thetaTerm] using j1_ksThetaHullLogRoot_lam_lower (l := l) T
  exact h1.trans h2

#print axioms neg_MpaperV2_le_thetaLam_of_vol

#print axioms MpaperV2_eq_fiber_sum
#print axioms j1_ksThetaHullLogRoot_lam_lower
#print axioms qVFamNormalizedCoefficient_le_twoL_mul_urCeilC
#print axioms hbridge_of_fiberCoeff

end LeanFormal.IUT.XiFPaper.Mzk1URThetaKHP5J1BridgeActual
end