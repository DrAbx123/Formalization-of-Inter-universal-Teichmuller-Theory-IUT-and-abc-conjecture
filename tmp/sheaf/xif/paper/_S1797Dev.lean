import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Algebra.Algebra.Epi
import Mathlib.Algebra.Category.Ring.Epi
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import tmp.sheaf.xif.paper.S1747FiniteEtaleMonoSplitActual

noncomputable section

open scoped TensorProduct
open Finset

namespace S1797

variable {K : Type} [Field K]

set_option maxHeartbeats 1000000

theorem eqRec_apply {κ : Type*} {Bj : κ → Type*} (x : (j : κ) → Bj j) {a b : κ} (h : a = b) :
    h ▸ x a = x b := by
  cases h
  rfl

theorem eqRec_zero {κ : Type*} {Bj : κ → Type*} [∀ j, Zero (Bj j)] {a b : κ} (h : a = b) :
    h ▸ (0 : Bj a) = (0 : Bj b) := by
  cases h
  rfl

/-- **SurjectiveSplit at the level of products of fields.** -/
theorem prod_surjective_split
    (ι : Type) [Fintype ι] (Ai : ι → Type) [∀ i, Field (Ai i)] [∀ i, Algebra K (Ai i)]
    [∀ i, Module.Finite K (Ai i)] [∀ i, Algebra.IsSeparable K (Ai i)]
    (κ : Type) [Fintype κ] (Bj : κ → Type) [∀ j, Field (Bj j)] [∀ j, Algebra K (Bj j)]
    [∀ j, Module.Finite K (Bj j)] [∀ j, Algebra.IsSeparable K (Bj j)]
    (ψ : (Π j, Bj j) →ₐ[K] (Π i, Ai i)) (hψsurj : Function.Surjective ψ) :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra K C) (_ : Module.Finite K C)
      (_ : Algebra.Etale K C) (e : (Π j, Bj j) ≃ₐ[K] (Π i, Ai i) × C),
      (AlgHom.fst (R := K) (A := Π i, Ai i) (B := C)).comp e.toAlgHom = ψ := by
  classical
  choose ji σ hσ using fun i =>
    S1747.exists_factor (K := K) (J := κ) Bj ((Pi.evalAlgHom K Ai i).comp ψ)
  have hproj_surj : ∀ i, Function.Surjective (Pi.evalAlgHom K Ai i) := by
    intro i y
    refine ⟨fun k => if h : k = i then h ▸ y else 0, ?_⟩
    show (if h : i = i then h ▸ y else 0) = y
    simp
  have hψisurj : ∀ i, Function.Surjective ((Pi.evalAlgHom K Ai i).comp ψ) := fun i =>
    (hproj_surj i).comp hψsurj
  have hσeval : ∀ (i : ι) (x : Π j, Bj j), σ i (x (ji i)) = (ψ x) i := by
    intro i x
    have h : ((Pi.evalAlgHom K Ai i).comp ψ) x = ((σ i).comp (Pi.evalAlgHom K Bj (ji i))) x := by
      rw [hσ i]
    simpa using h.symm
  have hσsurj : ∀ i, Function.Surjective (σ i) := by
    intro i y
    obtain ⟨x, hx⟩ := hψisurj i y
    refine ⟨(Pi.evalAlgHom K Bj (ji i)) x, ?_⟩
    change σ i (x (ji i)) = y
    rw [hσeval i x]
    simpa using hx
  have hσinj : ∀ i, Function.Injective (σ i) := fun i => RingHom.injective (σ i).toRingHom
  have hji_inj : Function.Injective ji := by
    intro i i' h
    by_contra hne
    have hne' : i' ≠ i := fun h' => hne h'.symm
    let y : Π k, Ai k := fun k => if k = i then 0 else if k = i' then 1 else 0
    have hyi : y i = 0 := by simp [y]
    have hyi' : y i' = 1 := by simp [y, hne']
    obtain ⟨x, hx⟩ := hψsurj y
    have h1 : σ i (x (ji i)) = 0 := by
      rw [hσeval i x, congrFun hx i, hyi]
    have h2 : σ i' (x (ji i')) = 1 := by
      rw [hσeval i' x, congrFun hx i', hyi']
    have hz1 : x (ji i) = 0 := by
      rw [← hσinj i (show σ i (x (ji i)) = σ i 0 by rw [h1, map_zero])]
    have htrans : h ▸ x (ji i) = x (ji i') := eqRec_apply x h
    have hz1' : x (ji i') = 0 := by
      rw [← htrans, hz1]
      exact eqRec_zero h
    rw [hz1', map_zero] at h2
    exact zero_ne_one h2
  -- ## The complement algebra
  let Comp := {j : κ // ¬ ∃ i, ji i = j}
  let C : Type := Π c : Comp, Bj c.val
  have hBjEtale : ∀ j, Algebra.Etale K (Bj j) := fun j =>
    Algebra.Etale.mk (Algebra.FormallyEtale.of_isSeparable K (Bj j))
      ((Algebra.FinitePresentation.of_finiteType).mp inferInstance)
  haveI : ∀ j, Algebra.Etale K (Bj j) := hBjEtale
  let β : (Π j, Bj j) →ₐ[K] C := AlgHom.pi (fun c : Comp => Pi.evalAlgHom K Bj c.val)
  have hβ_apply : ∀ (x : Π j, Bj j) (c : Comp), β x c = x c.val := fun x c => rfl
  let Phi : (Π j, Bj j) →ₐ[K] (Π i, Ai i) × C := ψ.prod β
  -- ## Injectivity
  have hPhi_inj : Function.Injective Phi := by
    intro b1 b2 hb
    have hψb : ψ b1 = ψ b2 := by
      have h := congrArg Prod.fst hb
      simpa [Phi] using h
    have hβb : β b1 = β b2 := by
      have h := congrArg Prod.snd hb
      simpa [Phi] using h
    have hcoord : ∀ j, b1 j = b2 j := by
      intro j
      by_cases hj : ∃ i, ji i = j
      · obtain ⟨i, rfl⟩ := hj
        have hh : σ i (b1 (ji i)) = σ i (b2 (ji i)) := by
          rw [hσeval i b1, hσeval i b2, hψb]
        exact hσinj i hh
      · have h := congrFun hβb ⟨j, hj⟩
        rw [hβ_apply b1 ⟨j, hj⟩, hβ_apply b2 ⟨j, hj⟩] at h
        exact h
    exact funext hcoord
  -- ## Surjectivity via an explicit right inverse
  let x0 : (Π i, Ai i) → (Π j, Bj j) := fun a => Classical.choose (hψsurj a)
  have hx0 : ∀ a, ψ (x0 a) = a := fun a => Classical.choose_spec (hψsurj a)
  let inv : (Π i, Ai i) × C → (Π j, Bj j) := fun p j =>
    if h : ∃ i, ji i = j then x0 p.1 j else p.2 ⟨j, h⟩
  have hinv_psi : ∀ p : (Π i, Ai i) × C, ψ (inv p) = p.1 := by
    intro p
    funext i
    have hmem : ∃ i' : ι, ji i' = ji i := ⟨i, rfl⟩
    have h1 : inv p (ji i) = x0 p.1 (ji i) := by
      show (if h : ∃ i', ji i' = ji i then x0 p.1 (ji i) else p.2 ⟨ji i, h⟩) = _
      rw [dif_pos hmem]
    have step1 : (ψ (inv p)) i = σ i (inv p (ji i)) := (hσeval i (inv p)).symm
    rw [step1, h1, hσeval i (x0 p.1), hx0 p.1]
  have hinv_comp : ∀ p : (Π i, Ai i) × C, β (inv p) = p.2 := by
    intro p
    funext c
    have h1 : inv p c.val = p.2 c := by
      show (if h : ∃ i, ji i = c.val then x0 p.1 c.val else p.2 ⟨c.val, h⟩) = p.2 c
      rw [dif_neg c.2]
    rw [hβ_apply (inv p) c, h1]
  have hPhi_surj : Function.Surjective Phi := by
    intro p
    exact ⟨inv p, by
      have h1 := hinv_psi p
      have h2 := hinv_comp p
      simp only [Phi, AlgHom.prod_apply, h1, h2]⟩
  have hPhi_bij : Function.Bijective Phi := ⟨hPhi_inj, hPhi_surj⟩
  let e : (Π j, Bj j) ≃ₐ[K] (Π i, Ai i) × C := AlgEquiv.ofBijective Phi hPhi_bij
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, e, ?_⟩
  have he : e.toAlgHom = Phi := rfl
  rw [he]
  exact AlgHom.fst_prod ψ β

/-- **SurjectiveSplit, unconditionally.** -/
theorem surjectiveSplit : S1747.SurjectiveSplit K := by
  intro A B hAring hAalg hAfin hAet hBring hBalg hBfin hBet φ hφsurj
  classical
  obtain ⟨ι, hιfin, Ai, hAiField, hAiAlg, eA, hAidata⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := A)).mp hAet
  obtain ⟨κ, hκfin, Bj, hBjField, hBjAlg, eB, hBjdata⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := B)).mp hBet
  haveI hιF : Fintype ι := Fintype.ofFinite ι
  haveI hκF : Fintype κ := Fintype.ofFinite κ
  let ψ : (Π j, Bj j) →ₐ[K] (Π i, Ai i) := eA.toAlgHom.comp (φ.comp eB.symm.toAlgHom)
  have hψsurj : Function.Surjective ψ := by
    have h1 : Function.Surjective (φ.comp eB.symm.toAlgHom) := hφsurj.comp eB.symm.surjective
    exact eA.surjective.comp h1
  have key := @prod_surjective_split K _ ι hιF Ai hAiField hAiAlg
    (fun i => (hAidata i).1) (fun i => (hAidata i).2)
    κ hκF Bj hBjField hBjAlg (fun j => (hBjdata j).1) (fun j => (hBjdata j).2)
    ψ hψsurj
  obtain ⟨C, hCring, hCalg, hCfin, hCetale, eψ, heψ⟩ := key
  letI : CommRing C := hCring
  letI : Algebra K C := hCalg
  letI : Module.Finite K C := hCfin
  letI : Algebra.Etale K C := hCetale
  let e' : B ≃ₐ[K] A × C :=
    eB.trans (eψ.trans (AlgEquiv.prodCongr eA.symm (AlgEquiv.refl : C ≃ₐ[K] C)))
  have he' : (AlgHom.fst (R := K) (A := A) (B := C)).comp e'.toAlgHom = φ := by
    ext b
    show (e' b).1 = φ b
    have hψb : (eψ (eB b)).1 = ψ (eB b) := by
      have h := DFunLike.congr_fun heψ (eB b)
      simpa [AlgHom.comp_apply] using h
    have hψdef : ψ (eB b) = eA (φ b) := by
      show eA (φ (eB.symm (eB b))) = eA (φ b)
      rw [eB.symm_apply_apply]
    have h1 : (e' b).1 = eA.symm ((eψ (eB b)).1) := by
      simp [e']
    rw [h1, hψb, hψdef, eA.symm_apply_apply]
  exact ⟨C, hCring, hCalg, hCfin, hCetale, e', he'⟩

end S1797
