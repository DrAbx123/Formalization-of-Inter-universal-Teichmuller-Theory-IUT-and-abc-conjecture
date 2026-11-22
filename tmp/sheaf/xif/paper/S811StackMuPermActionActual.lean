import tmp.sheaf.xif.paper.S789StackMuActionActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
/-! # S811: full mu_{2l} permutation action on the finite root-stack carrier
Left multiplication by zeta is an actual permutation action, but not a MulAut
action unless zeta=1 (S789).  This file records the actual permutation hom and
the exact MulAut gap. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S811StackMuPermActionActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S789StackMuActionActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
abbrev StackMuGroup : Type := rootsOfUnity (2 * l.value) (rootStackExtension T b)
noncomputable def stackMuPerm (ζ : StackMuGroup T b) :
    Equiv.Perm (StackSectionCarrier T b) :=
  Equiv.prodCongr (Equiv.mulLeft (ζ : (rootStackExtension T b)ˣ))
    (Equiv.refl (Multiplicative Real))
@[simp] theorem stackMuPerm_apply (ζ : StackMuGroup T b)
    (u : StackSectionCarrier T b) :
    stackMuPerm T b ζ u = ((ζ : (rootStackExtension T b)ˣ) * u.1, u.2) := rfl
/-- Full mu_{2l} permutation action. -/
noncomputable def stackMuPermActionOf :
    StackMuGroup T b →* Equiv.Perm (StackSectionCarrier T b) where
  toFun := stackMuPerm T b
  map_one' := by
    apply Equiv.ext
    intro u
    simp [stackMuPerm]
  map_mul' ζ η := by
    apply Equiv.ext
    intro u
    apply Prod.ext
    · simp [stackMuPerm, mul_assoc]
    · rfl
theorem stackMuPermActionOf_apply (ζ : StackMuGroup T b)
    (u : StackSectionCarrier T b) :
    stackMuPermActionOf T b ζ u =
      ((ζ : (rootStackExtension T b)ˣ) * u.1, u.2) := rfl
/-- Exact MulAut version: a hom whose action is left multiplication. -/
structure StackMuMulAutData where
  action : StackMuGroup T b →* MulAut (StackSectionCarrier T b)
  action_apply : ∀ (ζ : StackMuGroup T b) (u : StackSectionCarrier T b),
    action ζ u = ((ζ : (rootStackExtension T b)ˣ) * u.1, u.2)
end LeanFormal.IUT.XiFPaper.S811StackMuPermActionActual
