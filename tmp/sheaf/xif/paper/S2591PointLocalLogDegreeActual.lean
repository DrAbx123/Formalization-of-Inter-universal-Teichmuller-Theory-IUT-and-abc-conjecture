import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import tmp.sheaf.xif.paper.S2587Cor312PointMapSkeletonActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2587Cor312PointMapSkeletonActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2591PointLocalLogDegreeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Candidate local log-degree on the one-factor tensor block: the log of the
p-adic tensor norm.  This is the tensor analogue of the per-index
`sourceLocalLogDegree` summand `log |deg_v|`. -/
noncomputable def S2591PointLocalLogDegree
    (x : qVFamTensorBlock T b) : Real :=
  Real.log ‖x‖

/-- The pointwise local log-degree of the rational point map. -/
noncomputable def S2591PointLocalLogDegreeMap :
    Nat -> Nat -> Nat -> Real :=
  fun a n c => S2591PointLocalLogDegree T b (S2588PointMap T b a n c)

#check S2591PointLocalLogDegree
#check S2591PointLocalLogDegreeMap

end LeanFormal.IUT.XiFPaper.S2591PointLocalLogDegreeActual
end