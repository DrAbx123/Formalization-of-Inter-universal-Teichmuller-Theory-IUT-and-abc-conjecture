import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import LeanFormal.IUT.Foundations.LocalFields.ContinuousRationalPadicScalars

/-!
# The finite tensor is the topological rational tensor

Every continuous rational multilinear map of the finite-dimensional
Qp factors has a unique continuous rational linear lift through the
actual finite Qp tensor. Density of Q in Qp supplies the balancing
relations, rather than identifying the algebraic rational tensor with
the algebraic Qp tensor without a topological argument.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

open LeanFormal.IUT.LocalFieldPadicScalars

noncomputable section

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)] [∀ i, FiniteDimensional ℚ_[p] (M i)]

instance finitePadicTensorRatModule : Module ℚ (FinitePadicTensor (p := p) M) :=
  Module.compHom (FinitePadicTensor (p := p) M) (algebraMap ℚ ℚ_[p])

instance finitePadicTensorRatScalarTower :
    IsScalarTower ℚ ℚ_[p] (FinitePadicTensor (p := p) M) where
  smul_assoc q a x := by
    change (q • a) • x = (algebraMap ℚ ℚ_[p] q) • (a • x)
    rw [Algebra.smul_def, mul_smul]

variable [∀ i, Module ℚ (M i)] [∀ i, IsScalarTower ℚ ℚ_[p] (M i)]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [T2Space E] [Module ℚ_[p] E] [ContinuousSMul ℚ_[p] E]
variable [Module ℚ E] [IsScalarTower ℚ ℚ_[p] E]

def finitePadicTensorRationalTprod :
    ContinuousMultilinearMap ℚ M (FinitePadicTensor (p := p) M) :=
  (finitePadicTensorContinuousTprod (p := p) M).restrictScalars ℚ

def finitePadicTensorLift (f : ContinuousMultilinearMap ℚ M E) :
    FinitePadicTensor (p := p) M →L[ℚ_[p]] E := by
  let h : FinitePadicTensor (p := p) M →ₗ[ℚ_[p]] E :=
    PiTensorProduct.lift (extendContinuousRatMultilinearMap (p := p) f).toMultilinearMap
  exact ⟨h, h.continuous_of_finiteDimensional⟩

theorem finitePadicTensorLift_tprod (f : ContinuousMultilinearMap ℚ M E)
    (x : (i : ι) → M i) :
    finitePadicTensorLift (p := p) M f (finitePadicTensorTprod (p := p) M x) = f x :=
  PiTensorProduct.lift.tprod x

theorem finitePadicTensorLift_unique (f : ContinuousMultilinearMap ℚ M E)
    (g : FinitePadicTensor (p := p) M →L[ℚ_[p]] E)
    (hg : ∀ x, g (finitePadicTensorTprod (p := p) M x) = f x) :
    g = finitePadicTensorLift (p := p) M f := by
  have hlinear : g.toLinearMap = (finitePadicTensorLift (p := p) M f).toLinearMap := by
    apply PiTensorProduct.ext
    ext x
    exact (hg x).trans (finitePadicTensorLift_tprod M f x).symm
  ext x
  exact congrArg (fun h : FinitePadicTensor (p := p) M →ₗ[ℚ_[p]] E => h x) hlinear

def finitePadicTensorRationalLift (f : ContinuousMultilinearMap ℚ M E) :
    FinitePadicTensor (p := p) M →L[ℚ] E where
  toFun := finitePadicTensorLift (p := p) M f
  map_add' := (finitePadicTensorLift (p := p) M f).map_add
  map_smul' q x := by
    change finitePadicTensorLift (p := p) M f ((algebraMap ℚ ℚ_[p] q) • x) = _
    rw [map_smul, algebraMap_smul ℚ_[p]]
    rfl
  cont := (finitePadicTensorLift (p := p) M f).continuous

theorem finitePadicTensorRationalLift_tprod (f : ContinuousMultilinearMap ℚ M E)
    (x : (i : ι) → M i) :
    finitePadicTensorRationalLift (p := p) M f (finitePadicTensorTprod (p := p) M x) = f x :=
  finitePadicTensorLift_tprod M f x

theorem finitePadicTensorRationalLift_unique (f : ContinuousMultilinearMap ℚ M E)
    (g : FinitePadicTensor (p := p) M →L[ℚ] E)
    (hg : ∀ x, g (finitePadicTensorTprod (p := p) M x) = f x) :
    g = finitePadicTensorRationalLift (p := p) M f := by
  have hpadic := finitePadicTensorLift_unique (p := p) M f
    (extendContinuousRatLinearMap (p := p) g) hg
  ext x
  exact congrArg (fun h : FinitePadicTensor (p := p) M →L[ℚ_[p]] E => h x) hpadic

theorem existsUnique_continuous_rational_tensor_lift
    (f : ContinuousMultilinearMap ℚ M E) :
    ∃! g : FinitePadicTensor (p := p) M →L[ℚ] E,
      ∀ x, g (finitePadicTensorTprod (p := p) M x) = f x :=
  ⟨finitePadicTensorRationalLift M f, finitePadicTensorRationalLift_tprod M f,
    fun g hg => finitePadicTensorRationalLift_unique M f g hg⟩

end

end LeanFormal.IUT.LocalFieldPadicTensor
