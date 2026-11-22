import tmp.sheaf.xif.paper.S824RootStackyHaarVolumeActual
import tmp.sheaf.xif.paper.W3RootStackTraceIndexActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.W11Scratch2

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S824RootStackyHaarVolumeActual
open LeanFormal.IUT.XiFPaper.W3RootStackTraceIndexActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem stackMuRoot_isPrimitiveRoot :
    IsPrimitiveRoot
      (((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
        rootNormedAmbient T b)) (2 * l.value) := by
  unfold stackMuRoot
  rw [Units.val_mk0]
  exact Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot (rootNormedAmbient T b) (2 * l.value))

theorem twoL_gt_one : 1 < 2 * l.value := by
  have h : 5 ≤ l.value := l.ge_five
  omega

theorem stackMuUnit_ne_one : stackMuUnit (l := l) T b ≠ 1 := by
  intro h
  have hval : ((stackMuUnit (l := l) T b : rootStackExtension T b)) = 1 := by
    rw [h]
    rfl
  have hroot : ((stackMuRoot (l := l) T b : (rootNormedAmbient T b)ˣ) :
      rootNormedAmbient T b) = 1 := by
    have h' := congrArg (fun x : rootStackExtension T b =>
      (x : rootNormedAmbient T b)) hval
    simpa [stackMuUnit] using h'
  exact (stackMuRoot_isPrimitiveRoot (l := l) T b).ne_one twoL_gt_one hroot

theorem stackMuElem_ne_one : stackMuElem (l := l) T b ≠ 1 := by
  intro h
  apply stackMuUnit_ne_one (l := l) T b
  apply Units.ext
  rw [Units.val_one]
  exact h

theorem stackMuElem_fixed_eq_zero {x : rootStackExtension T b}
    (h : stackMuElem (l := l) T b * x = x) : x = 0 := by
  have hsub : (stackMuElem (l := l) T b - 1) * x = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  have hne : (stackMuElem (l := l) T b - 1) ≠ 0 :=
    sub_ne_zero.mpr (stackMuElem_ne_one (l := l) T b)
  exact (mul_eq_zero.mp hsub).resolve_left hne

theorem stackMuElem_fixedPoints_eq_singleton :
    {x : rootStackExtension T b | stackMuElem (l := l) T b * x = x} = {0} := by
  ext x
  constructor
  · intro hx
    exact Set.mem_singleton_iff.mpr (stackMuElem_fixed_eq_zero (l := l) T b hx)
  · intro hx
    rw [Set.mem_singleton_iff.mp hx, mul_zero]
    rfl

end LeanFormal.IUT.XiFPaper.W11Scratch2

end
