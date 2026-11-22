/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.S201RootThetaNormLActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! 08_cross_norm_lemma (laichunwing IUT-Verification) as Lean numerics:
the cross norm is multiplicative on pure tensors, so its log-volume is additive.
We instantiate it at the actual root theta values (S201) where the cross norm
is the gaussExponent power of the q-root norm. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.CrossNormLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open scoped BigOperators

/-! ## 1. Cross-norm log-volume is additive -/

/-- The log-volume of a finite family of positive norms (the multiplicative
cross norm on pure tensors). -/
def crossNormLogVolume {iota : Type} [Fintype iota] (f : iota -> Real) : Real :=
  Real.log (∏ i, f i)

theorem crossNormLogVolume_constructed {iota : Type} [Fintype iota]
    (f : iota -> Real) (hf : forall i, 0 < f i) :
    crossNormLogVolume f = ∑ i, Real.log (f i) := by
  unfold crossNormLogVolume
  rw [Real.log_prod (s := Finset.univ) (f := f)]
  · simp
  · intro i _
    exact (hf i).ne'

/-- Three-factor form of the cross-norm lemma. -/
theorem crossNormLogVolume_three (a b c : Real) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) :
    Real.log (a * b * c) = Real.log a + Real.log b + Real.log c := by
  rw [Real.log_mul (by positivity) hc.ne']
  rw [Real.log_mul ha.ne' hb.ne']
  ring

/-! ## 2. Root theta values: cross norm = q-root norm ^ gaussExponent -/

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The root theta cross norm log-volume is gaussExponent j times the q-root
log-volume (the 08 cross-norm lemma at the actual theta values). -/
theorem rootTheta_crossNormLogVolume (j : SignedLabel l.value) :
    Real.log ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ =
      (gaussExponent j.1 : Real) * Real.log ‖rootNormedElement T b‖ := by
  rw [rootNormedThetaValueInL_norm, Real.log_zpow]

/-- The q-root log-volume in terms of the S201 actual norm. -/
theorem localQrootLogVolume_eq :
    Real.log ‖rootNormedElement T b‖ = Real.log (rootNormedElementNorm T b) := rfl

end LeanFormal.IUT.XiFPaper.CrossNormLogVolumeActual