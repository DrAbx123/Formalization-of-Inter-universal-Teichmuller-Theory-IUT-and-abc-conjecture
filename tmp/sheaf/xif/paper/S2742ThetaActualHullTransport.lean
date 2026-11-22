import tmp.sheaf.xif.paper.S2725ThetaImageHullActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2742ThetaActualHullTransport
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Actual theta hull log-volume from the S2725 source holomorphic hull. -/
noncomputable def S2742ThetaHullLogVolume
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) : Real :=
  I.sourceSignedHullLogVolume v R n

theorem S2742ThetaHullLogVolume_eq_neg_hullVolume
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    S2742ThetaHullLogVolume (I := I) v R n = -(I.sourceRealHullVolume v R n) :=
  I.sourceSignedHullLogVolume_eq_neg_hullSetVolume v R n

theorem S2742ThetaHullLogVolume_nonpos
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    S2742ThetaHullLogVolume (I := I) v R n <= 0 :=
  I.sourceSignedHullLogVolume_nonpos v R n

theorem S2742ThetaImage_subset_hull
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.possibleThetaPilotImageSet v R n ⊆ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
  I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n

theorem S2742ThetaHull_least
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    CandidateHull (I.sourceScalingUnits v) (I.sourceHolomorphicHull v R n) :=
  I.sourceHolomorphicHull_candidate v R n

end LeanFormal.IUT.XiFPaper.S2742ThetaActualHullTransport
end
