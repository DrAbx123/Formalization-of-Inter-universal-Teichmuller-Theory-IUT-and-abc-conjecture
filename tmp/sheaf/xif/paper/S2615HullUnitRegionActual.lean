import tmp.sheaf.xif.paper.S2614CompactnessScalingActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeometryReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierHaarData

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2605SignedSourceVolumeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2615HullUnitRegionActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)

def S2615UnitData (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (himg : forall j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0)
    (hscal : forall s : I.ThetaPilotPoint v, s ∈ I.sourceScalingUnits v ->
      I.sourceLocalLogDegree v s <= 0) :
    I.SourceUnitRegionHaarData v R n where
  unitRegion := (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))
  scaling := 1
  degreeBound := 0
  hull_subset_scaledRegionImage := by
    intro x hx
    exact ⟨x, hx, by simp⟩
  unitRegion_logDegree_le := by
    intro y hy
    exact I.sourceLocalLogDegree_le_zero_of_mem_sourceHolomorphicHull
      v R n himg hscal y hy
  scaling_logDegree_nonpos := by
    rw [I.sourceLocalLogDegree_one v]

theorem S2615_scaledUnit_le_hull (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (himg : forall j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0)
    (hscal : forall s : I.ThetaPilotPoint v, s ∈ I.sourceScalingUnits v ->
      I.sourceLocalLogDegree v s <= 0) :
    ∀ a b c : Nat,
      sourceSetVolumeSigned I v
        (scaledRegionImage (S2615UnitData I v R n himg hscal).scaling
          (S2615UnitData I v R n himg hscal).unitRegion) <=
        sourceSetVolumeSigned I v (S2615UnitData I v R n himg hscal).unitRegion +
          ENNReal.ofReal 0 := by
  intro a b c
  have h : (S2615UnitData I v R n himg hscal).scaling = 1 := rfl
  have hu : (S2615UnitData I v R n himg hscal).unitRegion =
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := rfl
  rw [h, hu]
  have hset : scaledRegionImage (1 : I.ThetaPilotPoint v)
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) =
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
    ext x
    simp [scaledRegionImage]
  rw [hset, ENNReal.ofReal_zero, add_zero]

#check S2615UnitData
#check S2615_scaledUnit_le_hull

end LeanFormal.IUT.XiFPaper.S2615HullUnitRegionActual
end