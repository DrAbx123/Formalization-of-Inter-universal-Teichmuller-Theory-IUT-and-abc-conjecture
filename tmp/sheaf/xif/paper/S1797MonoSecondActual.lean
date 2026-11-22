import Mathlib.Algebra.Algebra.Epi
import Mathlib.Algebra.Category.Ring.Epi
import tmp.sheaf.xif.paper.S1747FiniteEtaleMonoSplitActual
import tmp.sheaf.xif.paper.S1786G3CategoricalTransferActual
import tmp.sheaf.xif.paper.S1793GaloisAssemblyWithQuotientsActual

/-!
# S1797 -- (G3) `monoInducesIsoOnDirectSummand` for finite etale K-algebras, unconditionally

S1747 reduced Lenstra's axiom (G3) for `(CommAlgCat.FiniteEtale K)^op` to two algebraic
statements about finite etale `K`-algebras:

* `S1747.EpiSurjective K`: every epimorphism of finite etale `K`-algebras is surjective;
* `S1747.SurjectiveSplit K`: every surjective map `B --> A` of finite etale `K`-algebras is,
  up to an algebra isomorphism `B ~= A x C`, the first projection.

This file proves **both**, unconditionally, with no `sorry`, no `admit` and no new axiom:

1. `S1797.epiSurjective`: an epimorphism `phi : B --> A` of finite etale `K`-algebras is
   surjective.  Proof: make `A` a `B`-algebra through `phi`; then `A` is etale and finite over
   `B` (`Algebra.Etale.of_restrictScalars`, `Module.Finite.of_restrictScalars_finite`), the
   tensor square `A (x)_B A` is a finite etale `K`-algebra (`Algebra.Etale.baseChange`,
   `Algebra.Etale.comp`, `Module.Finite.base_change`), and applying the epimorphism hypothesis
   to the two maps `a |-> a (x) 1`, `a |-> 1 (x) a` (`Algebra.TensorProduct.includeLeft`,
   `Algebra.TensorProduct.includeRight`) gives `1 (x) a = a (x) 1`, i.e. `Algebra.IsEpi B A`.
   Mathlib's `Algebra.isEpi_iff_surjective_algebraMap_of_finite` then yields surjectivity.

2. `S1797.surjectiveSplit`: a surjection `phi : B --> A` splits.  Proof: write
   `A ~= prod_i A_i` and `B ~= prod_j B_j` as products of finite separable field extensions
   (`Algebra.Etale.iff_exists_algEquiv_prod`), and factor the induced map on each component
   through a unique projection (`S1747.exists_factor`).  Surjectivity forces the index map
   `i |-> j i` to be injective and the component maps `B_{j i} --> A_i` to be bijections; the
   complement `C = prod_{j not in range} B_j` then satisfies `B ~= A x C` with first projection
   `phi`.  The bijection is proved by exhibiting an explicit right inverse of
   `B --> A x C`.

3. `S1797.finiteEtaleSplit` (= `S1786.FiniteEtaleSplit K`) combines them.

4. `S1797.monoInducesIsoOnDirectSummandField`: Lenstra (G3) for `(CommAlgCat.FiniteEtale K)^op`,
   via the categorical transfer of S1786.  It is displayed in the literal shapes used by
   S1767/S1793 and plugged into S1793's assembly, giving an unconditional
   `PreGaloisCategory (FiniteEtaleAlg K)`.

## References

* S1747: `tmp/sheaf/xif/paper/S1747FiniteEtaleMonoSplitActual.lean`
* S1786: `tmp/sheaf/xif/paper/S1786G3CategoricalTransferActual.lean`
* S1793: `tmp/sheaf/xif/paper/S1793GaloisAssemblyWithQuotientsActual.lean`
* Lenstra, *Galois theory for schemes*, Definition 3.1 (G3).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Finset

namespace S1797

variable {K : Type} [Field K]

set_option maxHeartbeats 1000000


/-- **EpiSurjective, unconditionally.**  An epimorphism of finite etale `K`-algebras, in the
category of finite etale `K`-algebras, is surjective. -/
theorem epiSurjective : S1747.EpiSurjective K := by
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
    have := congrArg (fun f => f a) hEq
    rw [hg_apply, hh_apply] at this
    exact this.symm
  have hsurj : Function.Surjective (algebraMap B A) :=
    (Algebra.isEpi_iff_surjective_algebraMap_of_finite (R := B) (A := A)).mp hEpi
  exact fun a => hsurj a

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


/-- `S1747.EpiSurjective` and `S1747.SurjectiveSplit` together give the algebraic form of (G3). -/
theorem finiteEtaleSplit : S1786.FiniteEtaleSplit K :=
  S1786.finiteEtaleSplit_of_epiSurjective_of_surjectiveSplit epiSurjective surjectiveSplit

/-- **Lenstra (G3), unconditional**, in the shape of S1786's field. -/
theorem monoInducesIsoOnDirectSummandField : S1786.MonoInducesIsoOnDirectSummandField K :=
  S1786.monoInducesIsoOnDirectSummand_of_epiSurjective_of_surjectiveSplit
    epiSurjective surjectiveSplit

/-- **Lenstra (G3), unconditional**, in the literal shape of S1767's field. -/
theorem monoInducesIsoOnDirectSummandField_S1767 :
    S1767FiniteEtaleGalois.MonoInducesIsoOnDirectSummandField K :=
  monoInducesIsoOnDirectSummandField

/-- **Lenstra (G3), unconditional**, in the shape consumed by S1793's assembly. -/
theorem monoInducesIsoOnDirectSummandField_S1793 :
    S1793GaloisAssembly.MonoInducesIsoOnDirectSummandField K :=
  monoInducesIsoOnDirectSummandField

/-- **S1793's pre-Galois category with all five fields actual** (no (G3) hypothesis). -/
theorem preGaloisCategory :
    PreGaloisCategory (S1793GaloisAssembly.FiniteEtaleAlg K) :=
  S1793GaloisAssembly.preGaloisCategory (K := K) monoInducesIsoOnDirectSummandField_S1793

/-- The same at the category written literally as `(CommAlgCat.FiniteEtale K)^op`. -/
theorem preGaloisCategory_op :
    PreGaloisCategory ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :=
  preGaloisCategory

/-- **Galois category**, now conditional only on the fibre-functor field. -/
theorem galoisCategory
    (hFiber : S1793GaloisAssembly.FiberFunctorField K
      (S1793GaloisAssembly.preGaloisCategory (K := K) monoInducesIsoOnDirectSummandField_S1793)) :
    GaloisCategory (S1793GaloisAssembly.FiniteEtaleAlg K) :=
  S1793GaloisAssembly.galoisCategory (K := K) monoInducesIsoOnDirectSummandField_S1793 hFiber

/-! ### Axiom audit -/

#print axioms S1797.epiSurjective
#print axioms S1797.prod_surjective_split
#print axioms S1797.surjectiveSplit
#print axioms S1797.finiteEtaleSplit
#print axioms S1797.monoInducesIsoOnDirectSummandField
#print axioms S1797.monoInducesIsoOnDirectSummandField_S1793
#print axioms S1797.preGaloisCategory
#print axioms S1797.galoisCategory

end S1797