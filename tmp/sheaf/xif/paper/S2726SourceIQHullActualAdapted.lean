import tmp.sheaf.xif.paper.S2725ThetaImageHullActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierHaarData
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullVertexConvexityAssembly
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2726SourceIQHullActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- The actual source IQ hull interface on `I.ThetaPilotPoint v`, conditional on
the actual unit-region/Haar data.  Its image set and hull are exactly the S2725
actual source image and holomorphic hull. -/
noncomputable def sourceIQHullInterface
    (D : I.SourceUnitRegionHaarData v R n) :
    IQHullLogVolumeInterface (I.ThetaPilotPoint v) :=
  I.sourceUnitRegionHaarInterface v R n D

theorem sourceIQHullInterface_imageSet
    (D : I.SourceUnitRegionHaarData v R n) :
    (sourceIQHullInterface (I := I) v R n D).imageSet =
      I.possibleThetaPilotImageSet v R n := rfl

theorem sourceIQHullInterface_hull
    (D : I.SourceUnitRegionHaarData v R n) :
    (sourceIQHullInterface (I := I) v R n D).hull =
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := rfl

theorem sourceIQHullInterface_logVolume
    (D : I.SourceUnitRegionHaarData v R n) :
    (sourceIQHullInterface (I := I) v R n D).logVolume =
      I.sourceSetVolume v := rfl

/-- Exact obstruction: under pointwise degree faithfulness there is no actual
unit-region/Haar datum realizing the source interface. -/
theorem no_sourceUnitRegionHaarData_of_degreeFaithful
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ Nonempty (I.SourceUnitRegionHaarData v R n) := by
  rintro ⟨D⟩
  refine (I.not_exists_iqHullLogVolumeInterface_hull_subset_of_degreeFaithful
    v R n hdeg) ⟨sourceIQHullInterface (I := I) v R n D, ?_, rfl⟩
  intro x hx
  exact hx

#check sourceIQHullInterface
#check sourceIQHullInterface_imageSet
#check sourceIQHullInterface_hull
#check no_sourceUnitRegionHaarData_of_degreeFaithful
#print axioms no_sourceUnitRegionHaarData_of_degreeFaithful

end LeanFormal.IUT.XiFPaper.S2726SourceIQHullActualAdapted
end
