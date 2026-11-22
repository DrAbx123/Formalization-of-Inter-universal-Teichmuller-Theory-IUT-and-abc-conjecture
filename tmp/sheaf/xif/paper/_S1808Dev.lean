import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.Epi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.RingTheory.Finiteness.Basic
import tmp.sheaf.xif.paper.S1747FiniteEtaleMonoSplitActual

noncomputable section
open scoped TensorProduct
open CategoryTheory
open Finset

namespace S1808

/-! ## Auxiliary lemmas -/

/-- A K-algebra map between fields is injective. -/
lemma injective_of_field {K F L : Type} [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] (f : F →ₐ[K] L) : Function.Injective f := by
  intro x y hxy
  have h : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  by_contra hne
  have hx : x - y ≠ 0 := sub_ne_zero.mpr hne
  have h1 : f ((x - y)⁻¹ * (x - y)) = 1 := by rw [inv_mul_cancel₀ hx, map_one]
  rw [map_mul, h, mul_zero] at h1
  exact zero_ne_one h1

/-- A finite separable field extension is a finite etale algebra. -/
lemma etale_of_finite_separable (K L : Type) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.IsSeparable K L] : Algebra.Etale K L where
  formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
  finitePresentation := (Algebra.FinitePresentation.of_finiteType (R := K) (A := L)).mp inferInstance

/-! ## EpiSurjective: an epimorphism of finite etale algebras is surjective -/

set_option maxHeartbeats 1000000 in
/-- EpiSurjective, unconditionally.  The tensor product A ⊗[B] A is a finite etale
K-algebra; the two canonical maps a ↦ a ⊗ 1 and a ↦ 1 ⊗ a agree after precomposition
with the algebra map B → A, so the categorical epimorphism property forces them to be equal.
Mathlib's Algebra.IsEpi then gives surjectivity. -/
theorem epiSurjective (K : Type) [Field K] : S1747.EpiSurjective K := by
  intro A B hAring hAalg hAfin hAet hBring hBalg hBfin hBet φ hφ
  letI : Algebra B A := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K B A := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro k
    exact (φ.commutes k).symm
  haveI : Algebra.Etale B A := Algebra.Etale.of_restrictScalars K B A
  haveI : Module.Finite B A := Module.Finite.of_restrictScalars_finite K B A
  have hEpi : Algebra.IsEpi B A := by
    rw [Algebra.isEpi_iff_forall_one_tmul_eq]
    intro a
    haveI : Algebra.Etale A (A ⊗[B] A) := inferInstance
    haveI : Algebra.Etale K (A ⊗[B] A) := Algebra.Etale.comp K A (A ⊗[B] A)
    haveI : Module.Finite A (A ⊗[B] A) := Module.Finite.base_change B A A
    haveI : Module.Finite K (A ⊗[B] A) := Module.Finite.trans A (A ⊗[B] A)
    let g : A →ₐ[K] A ⊗[B] A := Algebra.TensorProduct.includeLeft
    let h : A →ₐ[K] A ⊗[B] A :=
      (Algebra.TensorProduct.includeRight (R := B) (A := A) (B := A)).restrictScalars K
    have hg_apply : ∀ x : A, g x = x ⊗ₜ[B] (1 : A) := fun x => rfl
    have hh_apply : ∀ x : A, h x = (1 : A) ⊗ₜ[B] x := fun x => rfl
    have hgh : g.comp φ = h.comp φ := by
      ext b
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hg_apply, hh_apply]
      have hsm : (b : B) • (1 : A) = φ b := by
        rw [Algebra.smul_def, mul_one]
        rfl
      rw [← hsm]
      exact TensorProduct.smul_tmul (R := B) (R' := B) b (1 : A) (1 : A)
    have hEq : g = h := hφ (A ⊗[B] A) g h hgh
    have h := congrArg (fun f => f a) hEq
    rw [hg_apply, hh_apply] at h
    exact h.symm
  have hsurj : Function.Surjective (algebraMap B A) :=
    (Algebra.isEpi_iff_surjective_algebraMap_of_finite (R := B) (A := A)).mp hEpi
  exact fun a => hsurj a

/-! ## SurjectiveSplit: a surjection of finite etale algebras is a projection -/

set_option maxHeartbeats 2000000 in
/-- SurjectiveSplit, unconditionally. -/
theorem surjectiveSplit (K : Type) [Field K] : S1747.SurjectiveSplit K := by
  intro A B hAR hAA hAF hAE hBR hBA hBF hBE φ hφ
  classical
  obtain ⟨I, hI, Ai, hAiField, hAiAlg, eA, hAiFinSep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := A)).mp hAE
  obtain ⟨J, hJ, Bj, hBjField, hBjAlg, eB, hBjFinSep⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := B)).mp hBE
  letI : Finite I := hI
  letI : Finite J := hJ
  letI : Fintype I := Fintype.ofFinite I
  letI : Fintype J := Fintype.ofFinite J
  letI : ∀ i, Field (Ai i) := hAiField
  letI : ∀ j, Field (Bj j) := hBjField
  letI : ∀ i, Algebra K (Ai i) := hAiAlg
  letI : ∀ j, Algebra K (Bj j) := hBjAlg
  haveI hAiFin : ∀ i, Module.Finite K (Ai i) := fun i => (hAiFinSep i).1
  haveI hBjFin : ∀ j, Module.Finite K (Bj j) := fun j => (hBjFinSep j).1
  haveI hAiSep : ∀ i, Algebra.IsSeparable K (Ai i) := fun i => (hAiFinSep i).2
  haveI hBjSep : ∀ j, Algebra.IsSeparable K (Bj j) := fun j => (hBjFinSep j).2
  haveI hAiEt : ∀ i, Algebra.Etale K (Ai i) := fun i => etale_of_finite_separable K (Ai i)
  haveI hBjEt : ∀ j, Algebra.Etale K (Bj j) := fun j => etale_of_finite_separable K (Bj j)
  let ψ : (∀ j, Bj j) →ₐ[K] (∀ i, Ai i) :=
    eA.toAlgHom.comp (φ.comp eB.symm.toAlgHom)
  have hψsurj : Function.Surjective ψ := by
    intro a
    obtain ⟨b, hb⟩ := hφ (eA.symm a)
    refine ⟨eB b, ?_⟩
    show eA (φ (eB.symm (eB b))) = a
    rw [AlgEquiv.symm_apply_apply, hb, AlgEquiv.apply_symm_apply]
  choose m σ hσ using fun i =>
    S1747.exists_factor (K := K) (J := J) Bj (L := Ai i) ((Pi.evalAlgHom K Ai i).comp ψ)
  have hψ_apply : ∀ (i : I) (x : ∀ j, Bj j), ψ x i = σ i (x (m i)) := by
    intro i x
    have h := congr_fun (congrArg
      (fun f : (∀ j, Bj j) →ₐ[K] Ai i => (f : (∀ j, Bj j) → Ai i)) (hσ i)) x
    simpa using h
  have hσ_inj : ∀ i, Function.Injective (σ i) := fun i => injective_of_field (σ i)
  have hσ_surj : ∀ i, Function.Surjective (σ i) := by
    intro i a
    obtain ⟨x, hx⟩ := hψsurj (Pi.single i a)
    refine ⟨x (m i), ?_⟩
    have h := congr_fun hx i
    rw [hψ_apply i x] at h
    simpa using h
  have hm_inj : Function.Injective m := by
    intro i1 i2 hi
    by_contra hne
    let a : ∀ i, Ai i := fun k => if k = i1 then 1 else 0
    obtain ⟨x, hx⟩ := hψsurj a
    have h1 : σ i1 (x (m i1)) = 1 := by
      have h := congr_fun hx i1
      rw [hψ_apply i1 x] at h
      simpa [a] using h
    have h2 : σ i2 (x (m i2)) = 0 := by
      have h := congr_fun hx i2
      rw [hψ_apply i2 x] at h
      have ha2 : a i2 = 0 := by
        simp [a, show i2 ≠ i1 from fun hEq => hne hEq.symm]
      rw [ha2] at h
      exact h
    have hx1 : x (m i1) = 1 := by
      apply hσ_inj i1
      rw [h1, map_one]
    have hx' : x (m i2) = 1 := by
      rw [show m i2 = m i1 from hi.symm, hx1]
    rw [hx', map_one] at h2
    exact one_ne_zero h2
  -- the complement algebra
  let p : Set J := Set.range m
  let CJ := {j : J // j ∉ p}
  let C := (j : CJ) → Bj j.1
  letI : CommRing C := inferInstance
  letI : Algebra K C := inferInstance
  letI : Module.Finite K C := inferInstance
  letI : Algebra.Etale K C := inferInstance
  let q : (∀ j, Bj j) →ₐ[K] C := AlgHom.pi (fun c => Pi.evalAlgHom K Bj c.1)
  let g : B →ₐ[K] C := q.comp eB.toAlgHom
  let f : B →ₐ[K] A × C := φ.prod g
  have hf_inj : Function.Injective f := by
    intro b1 b2 hb
    have hφb : φ b1 = φ b2 := congrArg Prod.fst hb
    have hq : q (eB b1) = q (eB b2) := congrArg Prod.snd hb
    have hψeq : ψ (eB b1) = ψ (eB b2) := by
      have h := congrArg eA hφb
      simpa [ψ] using h
    have hx : eB b1 = eB b2 := by
      funext j
      by_cases hj : j ∈ p
      · obtain ⟨i, hi⟩ := hj
        have hcomp : σ i ((eB b1) (m i)) = σ i ((eB b2) (m i)) := by
          have h := congr_fun hψeq i
          rw [hψ_apply i (eB b1), hψ_apply i (eB b2)] at h
          exact h
        rw [← hi]
        exact hσ_inj i hcomp
      · have hqj : (eB b1) j = (eB b2) j := congr_fun hq ⟨j, hj⟩
        exact hqj
    exact eB.injective hx
  have hf_surj : Function.Surjective f := by
    intro ac
    obtain ⟨a, c⟩ := ac
    obtain ⟨x, hx⟩ := hψsurj (eA a)
    let y : ∀ j, Bj j := fun j => if h : j ∈ p then x j else c ⟨j, h⟩
    refine ⟨eB.symm y, ?_⟩
    have hyψ : ψ y = ψ x := by
      ext i
      rw [hψ_apply i y, hψ_apply i x]
      congr 1
      dsimp only [y]
      rw [dif_pos (show m i ∈ p from ⟨i, rfl⟩)]
    have hyq : q y = c := by
      ext cc
      have hy : y cc.1 = c cc := by
        dsimp only [y]
        rw [dif_neg cc.2]
      exact hy
    have h1 : φ (eB.symm y) = a := by
      apply eA.injective
      have hψy : ψ y = eA a := by rw [hyψ, hx]
      simpa [ψ] using hψy
    have h2 : q (eB (eB.symm y)) = c := by
      rw [AlgEquiv.apply_symm_apply]
      exact hyq
    show (φ (eB.symm y), q (eB (eB.symm y))) = (a, c)
    rw [h1, h2]
  have hbij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance,
    AlgEquiv.ofBijective f hbij, ?_⟩
  have hcomp : (AlgHom.fst (R := K) (A := A) (B := C)).comp
      (AlgEquiv.ofBijective f hbij).toAlgHom = φ := by
    rw [AlgEquiv.toAlgHom_ofBijective]
    simpa [f] using AlgHom.fst_prod (R := K) φ g
  exact hcomp

end S1808
