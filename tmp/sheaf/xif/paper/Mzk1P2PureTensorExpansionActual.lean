import tmp.sheaf.xif.paper.Mzk1P2LabelBlockSumActual
import Mathlib.Tactic

/-! # P2: pure-tensor finite-sum expansion

The pure tensor is represented as a function on the product carrier.  The
label-block q generator is expanded as the finite sum of its terms; this is the
finite-sum form consumed by the existing labelBlockSum file.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P2PureTensorExpansionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockSumActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Pure tensor family, pointwise finite sum of coefficient-theta terms. -/
noncomputable def pureTensorSumFamily
    {ι : Type} [Fintype ι]
    (coeff theta : ι -> RootExtensionProductCarrier T) :
    RootExtensionProductCarrier T :=
  fun b => ∑ i, coeff i b * theta i b

/-- Finite-sum expansion of the pure tensor family. -/
theorem pureTensor_finite_sum_expansion
    {ι : Type} [Fintype ι]
    (coeff theta : ι -> RootExtensionProductCarrier T) :
    pureTensorSumFamily T coeff theta =
      ∑ i, (fun b => coeff i b * theta i b) := by
  ext b
  unfold pureTensorSumFamily
  simp only [Finset.sum_apply]

/-- The existing label-block q generator has exactly the finite-sum expansion. -/
theorem labelBlockSum_expansion
    {ι : Type} [Fintype ι] (D : P2LabelBlockSumData T ι) :
    (fun b => ∑ i, D.coeff i b * D.thetaGen i b) =
      ∑ i, (fun b => D.coeff i b * D.thetaGen i b) := by
  ext b
  simp only [Finset.sum_apply]

/-- The finite-sum q generator is in the product unit ball (re-export). -/
theorem labelBlockSum_qGen_mem
    {ι : Type} [Fintype ι] (D : P2LabelBlockSumData T ι) :
    pureTensorSumFamily T D.coeff D.thetaGen ∈
      rootExtensionProductUnitBall T := by
  change (fun b => ∑ i, D.coeff i b * D.thetaGen i b) ∈
      rootExtensionProductUnitBall T
  exact p2_labelBlockSum_qGen_mem T D

#check pureTensorSumFamily
#check pureTensor_finite_sum_expansion
#check labelBlockSum_expansion
#check labelBlockSum_qGen_mem
end LeanFormal.IUT.XiFPaper.Mzk1P2PureTensorExpansionActual
end
