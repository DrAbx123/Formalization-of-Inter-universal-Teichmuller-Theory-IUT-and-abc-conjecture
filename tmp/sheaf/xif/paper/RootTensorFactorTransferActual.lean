import tmp.sheaf.xif.paper.RootTensorHaarIsometryActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.RootTensorFactorTransferActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootTensorHaarActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarTransportActual
open LeanFormal.IUT.XiFPaper.RootTensorThetaHullActual
open LeanFormal.IUT.XiFPaper.RootTensorHaarIsometryActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Multiplicative scaling on L as a continuous additive equivalence. -/
noncomputable def rootScalingContinuousAddEquiv
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0) :
    rootNormedExtension T b ≃ₜ+ rootNormedExtension T b where
  toAddEquiv :=
    { toFun := fun y => lam * y
      invFun := fun y => lam⁻¹ * y
      left_inv := by
        intro y
        change lam⁻¹ * (lam * y) = y
        rw [← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
      right_inv := by
        intro y
        change lam * (lam⁻¹ * y) = y
        rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
      map_add' := by
        intro x y
        rw [mul_add] }
  continuous_toFun := by
    have h : Continuous (fun y : rootNormedExtension T b => lam • y) :=
      (Homeomorph.smulOfNeZero lam hlam).continuous
    simpa [smul_eq_mul] using h
  continuous_invFun := by
    have h : Continuous (fun y : rootNormedExtension T b => lam⁻¹ • y) :=
      (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam)).continuous
    simpa [smul_eq_mul] using h

/-- Conjugation: block lambda-scaling is transport of L lambda-scaling by the isometry. -/
theorem blockScaling_eq_conj
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0) :
    blockScalingContinuousAddEquiv (T := T) (b := b) lam hlam =
      (blockContinuousLinearEquiv T b).toContinuousAddEquiv.trans
        ((rootScalingContinuousAddEquiv (T := T) (b := b) lam hlam).trans
          (blockContinuousLinearEquiv T b).symm.toContinuousAddEquiv) := by
  ext x
  rfl

/-- Map of the block scaling under the isometry equals the L scaling map. -/
theorem blockScaling_map_eq_rootScaling_map
    (lam : rootNormedExtension T b) (hlam : lam ≠ 0) :
    ((blockHaar T b).map
        (blockScalingContinuousAddEquiv (T := T) (b := b) lam hlam)).map
      (blockContinuousLinearEquiv T b) =
      (rootNormedHaar T b).map
        (rootScalingContinuousAddEquiv (T := T) (b := b) lam hlam) := by
  let e := blockContinuousLinearEquiv T b
  let Tb := blockScalingContinuousAddEquiv (T := T) (b := b) lam hlam
  let Tr := rootScalingContinuousAddEquiv (T := T) (b := b) lam hlam
  have hcomp : (e : rootTensorBlock T b → rootNormedExtension T b) ∘ Tb =
      (Tr : rootNormedExtension T b → rootNormedExtension T b) ∘ e := by
    ext x
    simp only [Function.comp_apply]
    have hconj := blockScaling_eq_conj (T := T) (b := b) lam hlam
    have hx : Tb x = e.symm (Tr (e x)) := by
      simpa [Tb, Tr, e] using
        congrFun (congrArg (fun f : rootTensorBlock T b ≃ₜ+ rootTensorBlock T b =>
          (f : rootTensorBlock T b → rootTensorBlock T b)) hconj) x
    apply congrArg (fun y : rootNormedExtension T b =>
      (y : rootNormedAmbient T b))
    calc
      e (Tb x) = e (e.symm (Tr (e x))) := by rw [hx]
      _ = Tr (e x) := by simp
  calc
    ((blockHaar T b).map Tb).map e = (blockHaar T b).map (e ∘ Tb) := by
      rw [MeasureTheory.Measure.map_map]
      · exact e.continuous.measurable
      · exact Tb.continuous.measurable
    _ = (blockHaar T b).map (Tr ∘ e) := by rw [hcomp]
    _ = ((blockHaar T b).map e).map Tr := by
      rw [MeasureTheory.Measure.map_map]
      · exact Tr.continuous.measurable
      · exact e.continuous.measurable
    _ = (rootNormedHaar T b).map Tr := by
      rw [blockHaar_map_eq_rootNormedHaar]

end LeanFormal.IUT.XiFPaper.RootTensorFactorTransferActual
end
