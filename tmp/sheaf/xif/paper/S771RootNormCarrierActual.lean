import tmp.sheaf.xif.paper.S757QVFamBlockIsometryActual
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Group.TransferInstance

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S771RootNormCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S312QPilotRootTensorBaseChangeActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S757QVFamBlockIsometryActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Carrier decision: the tensor block with the norm pulled back from
rootBase along the one-factor equivalence. -/
structure RootNormQVBlock where
  toBlock : qVFamTensorBlock T b

noncomputable def rootNormEquiv :
    RootNormQVBlock (T := T) b ≃ qVFamTensorBlock T b where
  toFun x := x.toBlock
  invFun x := ⟨x⟩
  left_inv x := by cases x; rfl
  right_inv x := rfl

noncomputable instance rootNormAddCommGroup :
    AddCommGroup (RootNormQVBlock (T := T) b) :=
  (rootNormEquiv (T := T) b).addCommGroup

noncomputable instance rootNormModule :
    Module ℚ_[qVFamTensorP T b] (RootNormQVBlock (T := T) b) :=
  letI := rootNormAddCommGroup (T := T) b
  (rootNormEquiv (T := T) b).module ℚ_[qVFamTensorP T b]

noncomputable def rootNormLinearEquiv :
    RootNormQVBlock (T := T) b ≃ₗ[ℚ_[qVFamTensorP T b]] rootBase T b :=
  (rootNormEquiv (T := T) b).linearEquiv ℚ_[qVFamTensorP T b] |>.trans
    (qVFamBlockLinearEquiv (l := l) T b)

noncomputable instance rootNormSeminormedAddCommGroup :
    SeminormedAddCommGroup (RootNormQVBlock (T := T) b) :=
  SeminormedAddCommGroup.induced (RootNormQVBlock (T := T) b)
    (rootBase T b) (rootNormLinearEquiv (l := l) T b).toLinearMap

noncomputable instance rootNormNormedSpace :
    NormedSpace ℚ_[qVFamTensorP T b] (RootNormQVBlock (T := T) b) :=
  NormedSpace.induced ℚ_[qVFamTensorP T b] (RootNormQVBlock (T := T) b)
    (rootBase T b) (rootNormLinearEquiv (l := l) T b).toLinearMap

/-- The pulled-back carrier is isometric to rootBase by rfl. -/
noncomputable def rootNormBlockIsometryEquiv :
    RootNormQVBlock (T := T) b ≃ₗᵢ[ℚ_[qVFamTensorP T b]] rootBase T b where
  toLinearEquiv := rootNormLinearEquiv (l := l) T b
  norm_map' := fun _ => rfl

/-- The underlying block of each x is qVFamBlockLinearEquiv applied to the
root-norm coordinate. -/
theorem rootNormBlockIsometryEquiv_apply
    (x : RootNormQVBlock (T := T) b) :
    rootNormBlockIsometryEquiv (l := l) T b x =
      qVFamBlockLinearEquiv (l := l) T b x.toBlock :=
  rfl

end LeanFormal.IUT.XiFPaper.S771RootNormCarrierActual

end
