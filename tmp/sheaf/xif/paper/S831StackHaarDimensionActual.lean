import tmp.sheaf.xif.paper.S823StackHaarNormalizedActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual

/-! # S831: d factorisation for rootStackExtension and S823 scaling bridge

The direct Qp-module structure on rootStackExtension is not synthesised from
the IntermediateField tower, so we record the exact tower factors:
  dK = [rootBase : Qp], dLK = [L : rootBase], dStack = [rootStack : L].
over rootBase, d = [rootStack : rootBase] = dLK * dStack (actual);
the Qp degree is the exact product dK * dLK * dStack.
The S823 scaling formula with this factor is an exact condition.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S823StackHaarNormalizedActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable instance rootStackFiniteDimensionalL :
    FiniteDimensional (rootNormedExtension T b) (rootStackExtension T b) := by
  letI : Module.Finite (rootNormedExtension T b) (rootStackExtension T b) :=
    rootStackExtension_finiteDimensional (l := l) T b
  infer_instance

/-- d over rootBase (K): [rootStackExtension : K]. -/
noncomputable def d : Nat :=
  Module.finrank (rootBase T b) (rootStackExtension T b)

/-- [K : Qp]. -/
noncomputable def dK : Nat :=
  Module.finrank ℚ_[(qVFamTensorP T b)] (rootBase T b)

/-- [L : K]. -/
noncomputable def dLK : Nat :=
  Module.finrank (rootBase T b) (rootNormedExtension T b)

/-- [rootStack : L]. -/
noncomputable def dStack : Nat :=
  Module.finrank (rootNormedExtension T b) (rootStackExtension T b)

/-- Exact d factorisation over rootBase. -/
theorem d_eq_dLK_mul_dStack :
    d (l := l) T b = dLK (l := l) T b * dStack (l := l) T b := by
  unfold d dLK dStack
  have h := Module.finrank_mul_finrank (rootBase T b)
    (rootNormedExtension T b) (rootStackExtension T b)
  exact h.symm

/-- The exact Qp degree factor: dK * dLK * dStack. -/
noncomputable def dQpFactor : Nat :=
  dK (l := l) T b * dLK (l := l) T b * dStack (l := l) T b

theorem dQpFactor_eq :
    dQpFactor (l := l) T b = dK (l := l) T b * dLK (l := l) T b *
      dStack (l := l) T b := rfl

/-- S823 root-ball scaling formula with the exact Qp factor. -/
def StackHaarScalingFormulaDQp : Prop :=
  StackHaarRootBallScalingFormula (l := l) T b (dQpFactor (l := l) T b)

/-- Exact S823 d-factor condition with dQpFactor. -/
def StackHaarDFactorConditionDQp : Prop :=
  ((dQpFactor (l := l) T b : Real) *
      paperQPilotLogLeast (l := l) T b) =
    paperQPilotLogLeast (l := l) T b

/-- If paper log is nonzero, S823's d-factor condition is dQpFactor = 1. -/
theorem stackHaarDFactorConditionDQp_iff
    (hlog : paperQPilotLogLeast (l := l) T b ≠ 0) :
    StackHaarDFactorConditionDQp (l := l) T b ↔
      dQpFactor (l := l) T b = 1 := by
  unfold StackHaarDFactorConditionDQp
  constructor
  · intro h
    have h' : ((dQpFactor (l := l) T b : Nat) : Real) = 1 :=
      mul_right_cancel₀ hlog (by simpa using h)
    exact_mod_cast h'
  · intro h
    rw [h]
    norm_num

end LeanFormal.IUT.XiFPaper.S831StackHaarDimensionActual
end
