import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Multilinear.Basic

/-!
# Continuous rational linearity extends to p-adic scalar linearity

Rationals are dense in Qp. Continuity therefore forces a Q-linear map
between compatible Qp modules to preserve every Qp scalar. No norm or
topology on Q is used in this argument.
-/

namespace LeanFormal.IUT.LocalFieldPadicScalars

noncomputable section

variable {p : ℕ} [Fact p.Prime]
section Linear

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
variable [AddCommGroup E] [AddCommGroup F] [T2Space F]
variable [Module ℚ_[p] E] [Module ℚ_[p] F]
variable [ContinuousSMul ℚ_[p] E] [ContinuousSMul ℚ_[p] F]
variable [Module ℚ E] [Module ℚ F]
variable [IsScalarTower ℚ ℚ_[p] E] [IsScalarTower ℚ ℚ_[p] F]

theorem continuous_ratLinearMap_padic_smul (f : E →ₗ[ℚ] F) (hf : Continuous f)
    (a : ℚ_[p]) (x : E) : f (a • x) = a • f x := by
  have hleft : Continuous (fun a : ℚ_[p] => f (a • x)) :=
    hf.comp (continuous_id.smul continuous_const)
  have hright : Continuous (fun a : ℚ_[p] => a • f x) :=
    continuous_id.smul continuous_const
  have heq := (Padic.denseRange_ratCast p).equalizer hleft hright (by
    funext q
    dsimp only [Function.comp_def]
    simpa only [Rat.cast_smul_eq_qsmul ℚ_[p]] using f.map_smul q x)
  exact congrFun heq a

def extendContinuousRatLinearMap (f : E →L[ℚ] F) : E →L[ℚ_[p]] F where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := continuous_ratLinearMap_padic_smul f.toLinearMap f.continuous a x
  cont := f.continuous

theorem extendContinuousRatLinearMap_apply (f : E →L[ℚ] F) (x : E) :
    extendContinuousRatLinearMap (p := p) f x = f x := rfl

end Linear

section Multilinear

variable {ι : Type*} {M : ι → Type*} {F : Type*}
variable [∀ i, TopologicalSpace (M i)] [∀ i, AddCommGroup (M i)]
variable [TopologicalSpace F] [AddCommGroup F] [T2Space F]
variable [∀ i, Module ℚ_[p] (M i)] [Module ℚ_[p] F]
variable [∀ i, ContinuousSMul ℚ_[p] (M i)] [ContinuousSMul ℚ_[p] F]
variable [∀ i, Module ℚ (M i)] [Module ℚ F]
variable [∀ i, IsScalarTower ℚ ℚ_[p] (M i)] [IsScalarTower ℚ ℚ_[p] F]

theorem continuous_ratMultilinearMap_padic_smul [DecidableEq ι]
    (f : ContinuousMultilinearMap ℚ M F) (m : (i : ι) → M i)
    (i : ι) (a : ℚ_[p]) (x : M i) :
    f (Function.update m i (a • x)) = a • f (Function.update m i x) := by
  have hleft : Continuous (fun a : ℚ_[p] => f (Function.update m i (a • x))) :=
    f.cont.comp (continuous_const.update i (continuous_id.smul continuous_const))
  have hright : Continuous (fun a : ℚ_[p] => a • f (Function.update m i x)) :=
    continuous_id.smul continuous_const
  have heq := (Padic.denseRange_ratCast p).equalizer hleft hright (by
    funext q
    dsimp only [Function.comp_def]
    simpa only [Rat.cast_smul_eq_qsmul ℚ_[p]] using f.map_update_smul m i q x)
  exact congrFun heq a

def extendContinuousRatMultilinearMap (f : ContinuousMultilinearMap ℚ M F) :
    ContinuousMultilinearMap ℚ_[p] M F where
  toFun := f
  map_update_add' m i x y := f.map_update_add m i x y
  map_update_smul' m i a x := continuous_ratMultilinearMap_padic_smul f m i a x
  cont := f.cont

theorem extendContinuousRatMultilinearMap_apply
    (f : ContinuousMultilinearMap ℚ M F) (m : (i : ι) → M i) :
    extendContinuousRatMultilinearMap (p := p) f m = f m := rfl

def continuousMultilinearScalarsEquiv :
    ContinuousMultilinearMap ℚ M F ≃ ContinuousMultilinearMap ℚ_[p] M F where
  toFun := extendContinuousRatMultilinearMap
  invFun := ContinuousMultilinearMap.restrictScalars ℚ
  left_inv f := by ext m; rfl
  right_inv f := by ext m; rfl

end Multilinear

end

end LeanFormal.IUT.LocalFieldPadicScalars
