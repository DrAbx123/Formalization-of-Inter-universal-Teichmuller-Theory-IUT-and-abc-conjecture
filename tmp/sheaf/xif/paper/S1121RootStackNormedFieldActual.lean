import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import Mathlib.Analysis.Normed.Algebra.Basic

/-! # S1121: NormedAlgebra L -> ambient and NontriviallyNormedField E

E = rootStackExtension is an IntermediateField of L = rootNormedExtension inside
the ambient normed field.  Mathlib gives a NontriviallyNormedField instance for
any IntermediateField once the base field is nontrivially normed and the
extension is a normed algebra.  Here we construct the missing
NormedAlgebra L ambient instance (the algebra map is the subtype inclusion, so
the norm inequality is the multiplicative norm identity), and then infer the
NontriviallyNormedField E instance. -/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1121RootStackNormedFieldActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- L = rootNormedExtension is a normed algebra over the ambient normed field,
with the algebra map the subtype inclusion. -/
noncomputable instance rootNormedAlgebraLAmbient :
    NormedAlgebra (rootNormedExtension T b) (rootNormedAmbient T b) where
  norm_smul_le r x := by
    change ‖((r : rootNormedExtension T b) : rootNormedAmbient T b) * x‖ ≤
      ‖r‖ * ‖x‖
    rw [norm_mul]
    have h : ‖((r : rootNormedExtension T b) : rootNormedAmbient T b)‖ = ‖r‖ := rfl
    rw [h]

/-- Actual NormedField instance on E via the ambient IntermediateField norm. -/
noncomputable instance rootStackNormedField : NormedField (rootStackExtension T b) :=
  inferInstance

/-- Actual NontriviallyNormedField instance on E. -/
noncomputable instance rootStackNontriviallyNormedField :
    NontriviallyNormedField (rootStackExtension T b) :=
  inferInstance

end LeanFormal.IUT.XiFPaper.S1121RootStackNormedFieldActual
end