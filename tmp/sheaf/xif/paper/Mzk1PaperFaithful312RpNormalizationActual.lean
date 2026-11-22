import tmp.sheaf.xif.paper.Mzk1PaperFaithful312HqnegActual
import tmp.sheaf.xif.paper.Mzk1HaarProductStrictMainlineActual
import tmp.sheaf.xif.paper.Mzk1HaarScalingOneDimActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.Mzk1ProductStrictnessShaActual
import Mathlib.Tactic

/-!
# A726 paper-faithful hqneg: direct proof modulo ONE normalization proposition

The remaining gap is the concrete numeric inequality
`rpVolume T (rpRegion T) < 1` (`rpRegion` = product of `R/p_b` closed balls,
`rpVolume` = product Haar `.toReal`).  Mathlib's `Measure.addHaar` is
`haarMeasure (Classical.arbitrary PositiveCompacts _)`, so the unit-ball value is
not fixed by the abstract theory.  We therefore state the single normalization fact
as a **proposition** (not a structure):
`RpUnitBallHaarOne T := ∀ b, rootExtensionHaar T b (rootExtensionUnitBall T b) = 1`.

With it (and green `rootExtensionHaar_ball_strict`, `rootImageRadius ≤ 1`,
`rpRegion_toReal`, product strictness) we prove directly:
* `rpVolume_rpRegion_lt_one : rpVolume T (rpRegion T) < 1`;
* `hqneg_direct : requirementSignedQ (rpRequirement T) < 0`.

No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312RpNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.Mzk1ProductStrictnessShaActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312HqnegActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **The single normalization fact** (proposition, no structure): the local unit
ball has Haar measure one. -/
def RpUnitBallHaarOne : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    rootExtensionHaar T b (rootExtensionUnitBall T b) = 1

/-- Under the normalization, every `R/p` ball factor has real Haar volume `< 1`. -/
theorem rpFactor_toReal_lt_one (hN : RpUnitBallHaarOne T)
    (b : Bad (nativePlaceSelection T)) :
    (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
      (rpRadius T b))).toReal < 1 := by
  have hRpos : 0 < (rootImageRadius T b : Real) := s1915_rootImageRadius_pos T b
  have hRle1 : (rootImageRadius T b : Real) ≤ 1 := s1915_rootImageRadius_le_one T b
  have hstrict := rootExtensionHaar_ball_strict (T := T) (b := b)
    (rootImageRadius T b : Real) hRpos
  have hfinRp : rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
      (rpRadius T b)) < ⊤ :=
    rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _
  have hfinR : rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
      (rootImageRadius T b : Real)) < ⊤ :=
    rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _
  have hreal : (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
      (rpRadius T b))).toReal <
      (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
        (rootImageRadius T b : Real))).toReal :=
    (ENNReal.toReal_lt_toReal (ne_of_lt hfinRp) (ne_of_lt hfinR)).mpr (by
      simpa only [rpRadius] using hstrict)
  have hsub : Metric.closedBall (0 : rootNormedExtension T b)
        (rootImageRadius T b : Real) ⊆ rootExtensionUnitBall T b :=
    Metric.closedBall_subset_closedBall hRle1
  have hle : (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
      (rootImageRadius T b : Real))).toReal ≤
      (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal :=
    ENNReal.toReal_mono (ne_of_lt (rootExtensionUnitBall_measure_lt_top T b))
      (measure_mono hsub)
  have hunit : (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal = 1 := by
    rw [hN b]
    norm_num
  rw [hunit] at hle
  linarith

/-- **Main theorem**: under the single normalization proposition,
`rpVolume rpRegion < 1`. -/
theorem rpVolume_rpRegion_lt_one (hN : RpUnitBallHaarOne T) :
    rpVolume T (rpRegion T) < 1 := by
  unfold rpVolume
  rw [rpRegion_toReal]
  have hpos : ∀ b : Bad (nativePlaceSelection T),
      0 < (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
        (rpRadius T b))).toReal :=
    fun b => ENNReal.toReal_pos
      (ne_of_gt (rootExtensionClosedBall_measure_pos (T := T) (b := b) _ (rpRadius_pos T b)))
      (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _))
  have hlt : ∃ b : Bad (nativePlaceSelection T),
      (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
        (rpRadius T b))).toReal < 1 :=
    ⟨Classical.arbitrary _, rpFactor_toReal_lt_one T hN _⟩
  have h := prod_univ_lt_prod_univ_real
    (f := fun b : Bad (nativePlaceSelection T) =>
      (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
        (rpRadius T b))).toReal)
    (g := fun _ => (1 : Real)) hpos (fun b => le_of_lt (rpFactor_toReal_lt_one T hN b)) hlt
  simpa using h

/-- **Direct hqneg**: the paper-faithful strict sign, modulo the single normalization
proposition (no named evidence structure). -/
theorem hqneg_direct (hN : RpUnitBallHaarOne T) :
    requirementSignedQ (rpRequirement T) < 0 :=
  (hqneg_iff_rpVolume_lt_one T).mpr (rpVolume_rpRegion_lt_one T hN)

structure DirectRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def directRows : List DirectRow :=
  [ ⟨"normalization fact", "RpUnitBallHaarOne (Prop; unit-ball Haar = 1)", "SINGLE_GAP"⟩
  , ⟨"factor bound", "rpFactor_toReal_lt_one (strict p-scaling + rootImageRadius <= 1)", "GREEN"⟩
  , ⟨"volume inequality", "rpVolume_rpRegion_lt_one", "GREEN_CONDITIONAL"⟩
  , ⟨"hqneg direct", "hqneg_direct (no named structure)", "GREEN_CONDITIONAL"⟩
  , ⟨"scope", "no RETRACTED use", "INTEGRITY"⟩
  ]

theorem directRows_length : directRows.length = 5 := rfl

theorem directRows_statuses_ok :
    directRows.all (fun r =>
      r.status ∈ ["SINGLE_GAP", "GREEN", "GREEN_CONDITIONAL", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312RpNormalizationActual

/-! ### Axiom gates -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312RpNormalizationActual.rpVolume_rpRegion_lt_one
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312RpNormalizationActual.hqneg_direct
