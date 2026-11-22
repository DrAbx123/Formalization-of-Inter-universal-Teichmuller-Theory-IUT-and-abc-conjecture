import tmp.sheaf.xif.paper.S2591PointLocalLogDegreeActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2591PointLocalLogDegreeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2592ValueMapCandidateActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {v : V}

/-- Candidate value map: send a tensor-block point to the constant theta-pilot
point whose value is the realized p-adic norm. -/
noncomputable def S2592TensorToThetaPilotPoint
    (R : I.SourceImageRealization v)
    {T : SourceNativeInitialThetaData.{0} l}
    {b : Bad (nativePlaceSelection T)}
    (x : qVFamTensorBlock T b) : I.ThetaPilotPoint v :=
  fun _ => R.posRealAction
    (Multiplicative.ofAdd (Real.log ‖x‖))

#check S2592TensorToThetaPilotPoint

end LeanFormal.IUT.XiFPaper.S2592ValueMapCandidateActual
end