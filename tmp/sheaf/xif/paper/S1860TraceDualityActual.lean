
/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1860
-/

import tmp.sheaf.xif.paper.S1859ProjectiveTraceActual
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.RingTheory.Trace.Quotient

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open scoped TensorProduct
open scoped Matrix
open LinearMap

namespace LeanFormal.IUT.XiFPaper.S1860TraceDualityActual

universe u v

/-! ## 1. The matrix criterion: unit determinant gives a bijective dual map -/

section MatrixCriterion

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_smul_single_one (y : ι → R) : (∑ j, y j • (Pi.single j (1 : R))) = y := by
  have h : ∀ j, y j • (Pi.single j (1 : R)) = Pi.single j (y j) := by
    intro j; funext i; simp [Pi.smul_apply, Pi.single_apply]
  simp only [h]
  exact Finset.univ_sum_single y

omit [DecidableEq ι] in
lemma dotProduct_mulVec_assoc (x y : ι → R) (N : Matrix ι ι R) :
    x ⬝ᵥ (N *ᵥ y) = (Nᵀ *ᵥ x) ⬝ᵥ y := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- The bilinear form x dot N y of an invertible matrix gives a bijection M -> M^*. -/
theorem toBilin'_bijective_of_isUnit_det (N : Matrix ι ι R) (h : IsUnit N.det) :
    Function.Bijective (Matrix.toBilin' N) := by
  have hT : IsUnit Nᵀ.det := by rwa [Matrix.det_transpose]
  have hzero : ∀ x : ι → R, Matrix.toBilin' N x = 0 → x = 0 := by
    intro x hx
    have h1 : ∀ j, x ⬝ᵥ N.col j = 0 := by
      intro j
      have h := congrArg (fun f : (ι → R) →ₗ[R] R => f (Pi.single j 1)) hx
      simp only [Matrix.toBilin'_apply', Matrix.mulVec_single_one, LinearMap.zero_apply] at h
      exact h
    have h2 : Nᵀ *ᵥ x = 0 := by
      funext j
      have h := h1 j
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply,
        Matrix.col_apply] at h ⊢
      rw [← h]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    calc x = (1 : Matrix ι ι R) *ᵥ x := by simp
      _ = ((N⁻¹)ᵀ * Nᵀ) *ᵥ x := by
            rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv N h, Matrix.transpose_one]
      _ = (N⁻¹)ᵀ *ᵥ (Nᵀ *ᵥ x) := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [h2, Matrix.mulVec_zero]
  refine ⟨fun x y hxy => ?_, fun φ => ?_⟩
  · have h := hzero (x - y) (by rw [map_sub, hxy, sub_self])
    rwa [sub_eq_zero] at h
  · refine ⟨(Nᵀ)⁻¹ *ᵥ (fun j => φ (Pi.single j 1)), ?_⟩
    have hx : Nᵀ *ᵥ ((Nᵀ)⁻¹ *ᵥ (fun j => φ (Pi.single j 1))) = (fun j => φ (Pi.single j 1)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Nᵀ hT, Matrix.one_mulVec]
    apply LinearMap.ext
    intro y
    rw [Matrix.toBilin'_apply', dotProduct_mulVec_assoc, hx, dotProduct]
    rw [show (∑ j, φ (Pi.single j 1) * y j) = ∑ j, y j * φ (Pi.single j 1) from
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
    have h2 : (∑ j, y j * φ (Pi.single j 1)) = ∑ j, φ (y j • (Pi.single j (1 : R))) :=
      Finset.sum_congr rfl (fun j _ => by rw [map_smul, smul_eq_mul])
    rw [h2, ← map_sum, sum_smul_single_one]

end MatrixCriterion

section GeneralBasis

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The matrix criterion.**  If the matrix of a bilinear form with respect to a basis has
unit determinant then the curried form M -> M^* is bijective. -/
theorem bilinForm_bijective_of_isUnit_det (b : Module.Basis κ R M)
    (B : LinearMap.BilinForm R M) (h : IsUnit ((LinearMap.BilinForm.toMatrix b) B).det) :
    Function.Bijective B := by
  set N := (LinearMap.BilinForm.toMatrix b) B with hN
  have hcongr : LinearMap.BilinForm.congr b.equivFun B = Matrix.toBilin' N := by
    apply LinearMap.BilinForm.ext
    intro x y
    rw [LinearMap.BilinForm.congr_apply, Matrix.toBilin'_apply']
    exact (LinearMap.BilinForm.dotProduct_toMatrix_mulVec (b := b) (B := B)
      (x := x) (y := y)).symm
  have hbij : Function.Bijective (Matrix.toBilin' N) := toBilin'_bijective_of_isUnit_det N h
  have key : ∀ (x : M) (z : κ → R), (Matrix.toBilin' N (b.equivFun x)) z =
      B x (b.equivFun.symm z) := by
    intro x z
    rw [← hcongr, LinearMap.BilinForm.congr_apply, LinearEquiv.symm_apply_apply]
  constructor
  · intro x y hxy
    have h' : b.equivFun x = b.equivFun y := by
      apply hbij.1
      apply LinearMap.ext
      intro z
      rw [key, key, hxy]
    exact b.equivFun.injective h'
  · intro φ
    obtain ⟨z, hz⟩ := hbij.2 (φ.comp (b.equivFun.symm : (κ → R) →ₗ[R] M))
    refine ⟨b.equivFun.symm z, ?_⟩
    apply LinearMap.ext
    intro m
    rw [show m = b.equivFun.symm (b.equivFun m) from (LinearEquiv.symm_apply_apply b.equivFun m).symm,
      ← key, LinearEquiv.apply_symm_apply]
    have := congrArg (fun f : (κ → R) →ₗ[R] R => f (b.equivFun m)) hz
    simpa [LinearMap.comp_apply] using this

end GeneralBasis

/-! ## 2. Localisation of duals: the evaluation map S (x) M^* -> (S (x) M)^* -/

section DualEval

variable {R : Type u} {S : Type u} {M : Type v}
  [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- Evaluation of the tensor s (x) g at m is s * algebraMap (g m). -/
def evalTmul (g : M →ₗ[R] R) : (S ⊗[R] M) →ₗ[S] S :=
  TensorProduct.AlgebraTensorModule.lift
    (((LinearMap.lsmul S (M →ₗ[R] S)).flip) ((Algebra.linearMap R S).comp g))

@[simp]
lemma evalTmul_tmul (g : M →ₗ[R] R) (s : S) (m : M) :
    evalTmul (S := S) g (s ⊗ₜ[R] m) = s * algebraMap R S (g m) := by
  rw [evalTmul, TensorProduct.AlgebraTensorModule.lift_tmul]
  simp

lemma evalTmul_add (g₁ g₂ : M →ₗ[R] R) :
    evalTmul (S := S) (g₁ + g₂) = evalTmul (S := S) g₁ + evalTmul g₂ := by
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s m => simp only [map_add, LinearMap.add_apply, evalTmul_tmul, mul_add]
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]

lemma evalTmul_smul (r : R) (g : M →ₗ[R] R) :
    evalTmul (S := S) (r • g) = r • evalTmul (S := S) g := by
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    simp only [LinearMap.smul_apply, evalTmul_tmul, smul_eq_mul, map_mul, Algebra.smul_def]
    ring
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- The evaluation map as a linear map in g. -/
def evalTmulLin : (M →ₗ[R] R) →ₗ[R] ((S ⊗[R] M) →ₗ[S] S) where
  toFun := evalTmul (S := S)
  map_add' := evalTmul_add
  map_smul' := evalTmul_smul

/-- The canonical evaluation map S (x) M^* -> (S (x) M)^*. -/
def dualEval : (S ⊗[R] (M →ₗ[R] R)) →ₗ[S] ((S ⊗[R] M) →ₗ[S] S) :=
  TensorProduct.AlgebraTensorModule.lift
    (((LinearMap.lsmul S ((M →ₗ[R] R) →ₗ[R] ((S ⊗[R] M) →ₗ[S] S))).flip) evalTmulLin)

lemma dualEval_tmul (s : S) (g : M →ₗ[R] R) :
    dualEval (S := S) (s ⊗ₜ[R] g) = s • evalTmul (S := S) g := by
  rw [dualEval, TensorProduct.AlgebraTensorModule.lift_tmul]
  simp [evalTmulLin]

@[simp]
lemma dualEval_tmul_tmul (s t : S) (g : M →ₗ[R] R) (m : M) :
    dualEval (S := S) (s ⊗ₜ[R] g) (t ⊗ₜ[R] m) = s * t * algebraMap R S (g m) := by
  rw [dualEval_tmul]
  simp [evalTmul_tmul, mul_assoc]

/-! ## 3. The free case and injectivity of the evaluation map -/

section Free

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The dual-basis expansion of a linear functional on ι → R. -/
lemma eq_sum_apply_single (g : (ι → R) →ₗ[R] R) :
    g = ∑ j, (g (Pi.single j (1 : R))) • LinearMap.proj j := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.sum_apply]
  have hv : v = ∑ j, v j • (Pi.single j (1 : R)) := (sum_smul_single_one v).symm
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [mul_comm]

/-- The evaluation map in the free case is determined by the values at the standard
basis vectors, and these coordinates determine the tensor. -/
lemma dualEval_free_eq_sum (y : S ⊗[R] ((ι → R) →ₗ[R] R)) :
    y = ∑ j, (dualEval (S := S) (M := ι → R) y (1 ⊗ₜ[R] (Pi.single j (1 : R)))) •
      (1 ⊗ₜ[R] (LinearMap.proj j)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul s g =>
      conv_lhs => rw [eq_sum_apply_single (R := R) g]
      rw [TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [dualEval_tmul_tmul]
      simp only [mul_one]
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
        TensorProduct.smul_tmul', Algebra.smul_def]
      simp [mul_comm]
  | add y₁ y₂ h₁ h₂ =>
      conv_lhs => rw [h₁, h₂]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_add, LinearMap.add_apply, add_smul]

/-- In the free case the evaluation map is injective. -/
lemma dualEval_free_injective (y : S ⊗[R] ((ι → R) →ₗ[R] R))
    (h : ∀ v : ι → R, dualEval (S := S) (M := ι → R) y (1 ⊗ₜ[R] v) = 0) : y = 0 := by
  rw [dualEval_free_eq_sum (S := S) y]
  apply Finset.sum_eq_zero
  intro j _
  rw [h (Pi.single j (1 : R)), zero_smul]

end Free

section Inject

variable {N : Type u} [AddCommGroup N] [Module R N]

/-- Naturality of the evaluation map in the module: precomposition of the dual. -/
lemma dualEval_lcomp (x : S ⊗[R] (M →ₗ[R] R)) (u : N →ₗ[R] M) (v : N) :
    dualEval (S := S) (TensorProduct.map (LinearMap.id : S →ₗ[R] S) (LinearMap.lcomp R R u) x)
        (1 ⊗ₜ[R] v) = dualEval (S := S) x (1 ⊗ₜ[R] u v) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s g => simp [LinearMap.lcomp_apply]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

end Inject

section InjectProjective

variable [Module.Finite R M] [Module.Projective R M]

/-- **The evaluation map is injective for a finite projective module.** -/
theorem dualEval_injective : Function.Injective (dualEval (R := R) (S := S) (M := M)) := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  set pDual : (M →ₗ[R] R) →ₗ[R] ((Fin n → R) →ₗ[R] R) := LinearMap.lcomp R R p with hpDual
  set iDual : ((Fin n → R) →ₗ[R] R) →ₗ[R] (M →ₗ[R] R) := LinearMap.lcomp R R i with hiDual
  have hcomp : iDual ∘ₗ pDual = LinearMap.id := by
    apply LinearMap.ext
    intro g
    apply LinearMap.ext
    intro m
    have h1 : (i : M →ₗ[R] Fin n → R) m = i m := rfl
    have := congrArg (fun (k : M →ₗ[R] M) => k m) hpi
    simpa [iDual, pDual, LinearMap.lcomp_apply] using congrArg g this
  have key : ∀ x : S ⊗[R] (M →ₗ[R] R), dualEval (S := S) x = 0 → x = 0 := by
    intro x hx
    have h' : ∀ v : Fin n → R,
        dualEval (S := S) (M := Fin n → R)
          (TensorProduct.map (LinearMap.id : S →ₗ[R] S) pDual x) (1 ⊗ₜ[R] v) = 0 := by
      intro v
      rw [dualEval_lcomp, hx]
      simp
    have hzero : TensorProduct.map (LinearMap.id : S →ₗ[R] S) pDual x = 0 :=
      dualEval_free_injective _ h'
    have h2 : TensorProduct.map (LinearMap.id : S →ₗ[R] S) iDual ∘ₗ
        TensorProduct.map (LinearMap.id : S →ₗ[R] S) pDual = LinearMap.id := by
      rw [← TensorProduct.map_comp, hcomp, LinearMap.id_comp, TensorProduct.map_id]
    calc x = (TensorProduct.map (LinearMap.id : S →ₗ[R] S) iDual ∘ₗ
          TensorProduct.map (LinearMap.id : S →ₗ[R] S) pDual) x := by rw [h2]; rfl
      _ = TensorProduct.map (LinearMap.id : S →ₗ[R] S) iDual
            (TensorProduct.map (LinearMap.id : S →ₗ[R] S) pDual x) := rfl
      _ = 0 := by rw [hzero, map_zero]
  intro x y hxy
  have h : dualEval (S := S) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key (x - y) h)

end InjectProjective

end DualEval


/-! ## 4. The local trace matrix has unit determinant (S1853, strengthened) -/

section LocalTraceMatrix

open LeanFormal.IUT.XiFPaper.S1853TraceFormActual

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsLocalRing R]
  [Module.Free R A] [Module.Finite R A] [Algebra.Etale R A]

/-- **The trace matrix of a finite etale algebra over a local ring has unit determinant.**
This is the missing strengthening of S1853's nondegeneracy result: the determinant is
actually a unit, so the trace-dual matrix is invertible. -/
theorem isUnit_det_traceMatrix_of_isLocalRing {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis κ R A) : IsUnit (Algebra.traceMatrix R b).det := by
  letI : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  letI : Algebra.Etale (R ⧸ IsLocalRing.maximalIdeal R)
      (A ⧸ Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R)) := etale_residueAlgebra
  have hfield := traceForm_residue_nondegenerate (R := R) (A := A)
  have hdet : (Algebra.traceMatrix (R ⧸ IsLocalRing.maximalIdeal R)
      (IsLocalRing.basisQuotient b)).det ≠ 0 := by
    have := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
      (IsLocalRing.basisQuotient b)).mp hfield
    simpa [Algebra.traceMatrix_of_basis] using this
  have hdet' : Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) ((Algebra.traceMatrix R b).det) ≠ 0 := by
    change (Algebra.traceMatrix (R ⧸ IsLocalRing.maximalIdeal R)
      (IsLocalRing.basisQuotient b)).det ≠ 0 at hdet
    rw [traceMatrix_quotient b] at hdet
    simpa [RingHom.map_det] using hdet
  rw [← IsLocalRing.notMem_maximalIdeal]
  exact fun hmem => hdet' (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)

end LocalTraceMatrix

/-! ## 5. Local-to-global: bijectivity at every maximal ideal -/

section LocalGlobal

variable {R : Type u} {M N : Type v} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- If the tensor one (x) q vanishes at every maximal localisation, then q = 0. -/
theorem tensor_one_eq_zero_of_forall_localization {Q : Type v} [AddCommGroup Q] [Module R Q]
    (q : Q) (h : ∀ (p : Ideal R) [p.IsMaximal], (1 : Localization.AtPrime p) ⊗ₜ[R] q = 0) :
    q = 0 := by
  refine Module.eq_zero_of_localization_maximal (R := R) (M := Q)
    (Mₚ := fun P _ => Localization.AtPrime P ⊗[R] Q)
    (f := fun P _ => TensorProduct.mk R (Localization.AtPrime P) Q 1) q ?_
  intro p hp
  exact h p

/-- **A linear map that is bijective after base change to every maximal localisation is
bijective.** -/
theorem bijective_of_localization_maximal (f : M →ₗ[R] N)
    (h : ∀ (p : Ideal R) [p.IsMaximal],
      Function.Bijective (LinearMap.baseChange (Localization.AtPrime p) f)) :
    Function.Bijective f := by
  constructor
  · intro x y hxy
    have h0 : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1 : ∀ (p : Ideal R) [p.IsMaximal], (1 : Localization.AtPrime p) ⊗ₜ[R] (x - y) = 0 := by
      intro p hp
      have hb : LinearMap.baseChange (Localization.AtPrime p) f
          ((1 : Localization.AtPrime p) ⊗ₜ[R] (x - y)) = 0 := by
        rw [LinearMap.baseChange_tmul, h0, TensorProduct.tmul_zero]
      have h0' : LinearMap.baseChange (Localization.AtPrime p) f
          (0 : Localization.AtPrime p ⊗[R] M) = 0 := map_zero _
      exact (h p).1 (hb.trans h0'.symm)
    have := tensor_one_eq_zero_of_forall_localization (x - y) h1
    rwa [sub_eq_zero] at this
  · intro y
    have hq : Submodule.mkQ (LinearMap.range f) y = 0 := by
      refine tensor_one_eq_zero_of_forall_localization (R := R) _ ?_
      intro p hp
      obtain ⟨z, hz⟩ := (h p).2 ((1 : Localization.AtPrime p) ⊗ₜ[R] y)
      have hmk : (Submodule.mkQ (LinearMap.range f)) ∘ₗ f = 0 := by
        apply LinearMap.ext
        intro m
        rw [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        exact ⟨m, rfl⟩
      have hbc : TensorProduct.map (LinearMap.id : Localization.AtPrime p →ₗ[R] Localization.AtPrime p)
          (Submodule.mkQ (LinearMap.range f)) =
          LinearMap.baseChange (Localization.AtPrime p) (Submodule.mkQ (LinearMap.range f)) := rfl
      have hcomp : LinearMap.baseChange (Localization.AtPrime p) (Submodule.mkQ (LinearMap.range f)) ∘ₗ
          LinearMap.baseChange (Localization.AtPrime p) f = 0 := by
        rw [← LinearMap.baseChange_comp, hmk, LinearMap.baseChange_zero]
      have hkill : TensorProduct.map (LinearMap.id : Localization.AtPrime p →ₗ[R] Localization.AtPrime p)
          (Submodule.mkQ (LinearMap.range f)) (LinearMap.baseChange (Localization.AtPrime p) f z) = 0 := by
        rw [hbc]
        exact congrArg (fun k => k z) hcomp
      have hmap : TensorProduct.map (LinearMap.id : Localization.AtPrime p →ₗ[R] Localization.AtPrime p)
          (Submodule.mkQ (LinearMap.range f)) ((1 : Localization.AtPrime p) ⊗ₜ[R] y)
          = (1 : Localization.AtPrime p) ⊗ₜ[R] (Submodule.mkQ (LinearMap.range f) y) :=
        TensorProduct.map_tmul _ _ _ _
      rw [← hmap, ← hz]
      exact hkill
    rw [Submodule.mkQ_apply] at hq
    have hy : y ∈ LinearMap.range f :=
      (Submodule.Quotient.mk_eq_zero (R := R) (M := N) (x := y) (LinearMap.range f)).mp hq
    exact LinearMap.mem_range.mp hy

end LocalGlobal

/-! ## 6. Compatibility of the evaluation map with the trace form -/

section TraceFormCompat

open LeanFormal.IUT.XiFPaper.S1859ProjectiveTraceActual

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Finite R A] [Module.Projective R A]
variable {S : Type u} [CommRing S] [Algebra R S]
  [Module.Finite S (S ⊗[R] A)] [Module.Projective S (S ⊗[R] A)]

/-- The evaluation map intertwines the base change of the trace form with the trace form of
the base-changed algebra. -/
theorem dualEval_baseChange_traceForm :
    (dualEval (R := R) (S := S) (M := A)).comp
        (LinearMap.baseChange S (projectiveTraceForm (R := R) (A := A)))
      = projectiveTraceForm (R := S) (A := S ⊗[R] A) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s a =>
      have hs : s ⊗ₜ[R] a = s • ((1 : S) ⊗ₜ[R] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul]
      congr 1
      rw [LinearMap.comp_apply, LinearMap.baseChange_tmul, dualEval_tmul]
      simp only [one_smul]
      apply LinearMap.ext
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul t b =>
          rw [projectiveTraceForm_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
          rw [show t ⊗ₜ[R] (a * b) = t • ((1 : S) ⊗ₜ[R] (a * b)) from by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
          rw [algebraTrace_smul, BaseChange.algebraTrace_baseChange]
          rw [evalTmul_tmul, projectiveTraceForm_apply]
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, h₁, h₂]

end TraceFormCompat

/-! ## 7. Trace duality over a local ring, and gluing to R' -/

section LocalStep

open LeanFormal.IUT.XiFPaper.S1859ProjectiveTraceActual

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Finite R A] [Module.Projective R A]
variable {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
  [Module.Finite S (S ⊗[R] A)] [Module.Flat S (S ⊗[R] A)] [Algebra.Etale S (S ⊗[R] A)]

/-- **Trace duality after localising at a local ring.**  If S is local and S (x) A is finite
etale over S, then the base change of the trace-dual map is bijective. -/
theorem baseChange_traceForm_bijective :
    Function.Bijective
      (LinearMap.baseChange S (projectiveTraceForm (R := R) (A := A))) := by
  haveI : Module.Free S (S ⊗[R] A) := Module.free_of_flat_of_isLocalRing
  have hdet := isUnit_det_traceMatrix_of_isLocalRing (R := S) (A := S ⊗[R] A)
    (Module.Free.chooseBasis S (S ⊗[R] A))
  have hθ : Function.Bijective (projectiveTraceForm (R := S) (A := S ⊗[R] A)) := by
    rw [projectiveTraceForm_eq_traceForm]
    refine bilinForm_bijective_of_isUnit_det (Module.Free.chooseBasis S (S ⊗[R] A))
      (Algebra.traceForm S (S ⊗[R] A)) ?_
    simpa [Algebra.traceMatrix_of_basis] using hdet
  have hcomp := dualEval_baseChange_traceForm (R := R) (A := A) (S := S)
  have hinj := dualEval_injective (R := R) (S := S) (M := A)
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply hθ.1
    rw [← hcomp, LinearMap.comp_apply, LinearMap.comp_apply, hxy]
  · intro z
    obtain ⟨y, hy⟩ := hθ.2 (dualEval (S := S) (M := A) z)
    refine ⟨y, ?_⟩
    apply hinj
    calc (dualEval (S := S) (M := A))
          (LinearMap.baseChange S (projectiveTraceForm (R := R) (A := A)) y)
        = ((dualEval (S := S) (M := A)).comp
            (LinearMap.baseChange S (projectiveTraceForm (R := R) (A := A)))) y := rfl
      _ = dualEval (S := S) (M := A) z := by rw [hcomp, hy]

end LocalStep

section MainTheorem

open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1859ProjectiveTraceActual

/-- **Trace duality for finite projective etale algebras over any commutative ring.** -/
theorem traceForm_bijective_of_etale (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] [Algebra.Etale R A] :
    Function.Bijective (projectiveTraceForm (R := R) (A := A)) := by
  refine bijective_of_localization_maximal _ ?_
  intro p hp
  haveI : p.IsMaximal := hp
  haveI hfin : Module.Finite (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] A) :=
    Module.Finite.base_change R (Localization.AtPrime p) A
  haveI hflat : Module.Flat (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] A) :=
    Module.Flat.baseChange R (Localization.AtPrime p) A
  haveI het : Algebra.Etale (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] A) :=
    Algebra.Etale.baseChange R A (Localization.AtPrime p)
  haveI hloc : IsLocalRing (Localization.AtPrime p) := inferInstance
  exact @baseChange_traceForm_bijective R A _ _ _ _ _
    (Localization.AtPrime p) _ _ hloc hfin hflat het

/-- **S1859ProjectiveTraceDuality is proved.**  For every finite etale R'-algebra A the
trace-dual map A -> A^*, a |-> (b |-> Tr (a*b)), is bijective. -/
theorem S1859ProjectiveTraceDuality_proof : S1859ProjectiveTraceDuality := by
  intro A hproj
  letI : Module.Projective S1779R (A : Type) := hproj
  intro φ
  have hbij : Function.Bijective (projectiveTraceForm (R := S1779R) (A := (A : Type))) :=
    traceForm_bijective_of_etale S1779R (A : Type)
  obtain ⟨a, ha⟩ := hbij.2 φ
  refine ⟨a, fun b => congrArg (fun f => f b) ha, ?_⟩
  intro y hy
  have h1 : projectiveTraceForm (R := S1779R) (A := (A : Type)) y = φ := by
    ext b
    exact hy b
  exact hbij.1 (h1.trans ha.symm)

end MainTheorem

/-! ## 8. Formal checks and axiom audit -/

#check S1859ProjectiveTraceDuality_proof
#check toBilin'_bijective_of_isUnit_det
#check bilinForm_bijective_of_isUnit_det
#check dualEval
#check dualEval_injective
#check isUnit_det_traceMatrix_of_isLocalRing
#check tensor_one_eq_zero_of_forall_localization
#check bijective_of_localization_maximal
#check dualEval_baseChange_traceForm
#check baseChange_traceForm_bijective

#print axioms toBilin'_bijective_of_isUnit_det
#print axioms bilinForm_bijective_of_isUnit_det
#print axioms dualEval_injective
#print axioms isUnit_det_traceMatrix_of_isLocalRing
#print axioms bijective_of_localization_maximal
#print axioms dualEval_baseChange_traceForm
#print axioms baseChange_traceForm_bijective
#print axioms S1859ProjectiveTraceDuality_proof

end LeanFormal.IUT.XiFPaper.S1860TraceDualityActual
