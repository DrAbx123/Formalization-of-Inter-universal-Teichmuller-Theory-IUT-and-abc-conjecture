import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.S902RootStackDVRInstancesActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S912RootStackNormedAlgebraActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S902RootStackDVRInstancesActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The intermediate field E is a normed algebra over L, with the norm inherited
from the ambient field.  This is the missing instance for the E-side DVR. -/
noncomputable instance rootStackNormedAlgebraL :
    NormedAlgebra (rootNormedExtension T b) (rootStackExtension T b) where
  norm_smul_le r x := by
    change ‖(algebraMap (rootNormedExtension T b) (rootStackExtension T b) r) *
        (x : rootStackExtension T b)‖ ≤
      ‖r‖ * ‖(x : rootStackExtension T b)‖
    rw [norm_mul]

/-- The Qp-normed-algebra structure on E, restricted from L. -/
noncomputable instance rootStackNormedAlgebraQp :
    NormedAlgebra ℚ_[qVFamTensorP T b] (rootStackExtension T b) :=
  NormedAlgebra.restrictScalars ℚ_[qVFamTensorP T b]
    (rootNormedExtension T b) (rootStackExtension T b)

end LeanFormal.IUT.XiFPaper.S912RootStackNormedAlgebraActualAdapted
