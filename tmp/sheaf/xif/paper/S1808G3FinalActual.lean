/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors

# S1808 -- (G3) for finite etale K-algebras, unconditionally

This file closes the last open field of the pre-Galois category
`PreGaloisCategory ((CommAlgCat.FiniteEtale K)^op)`: the axiom

  `monoInducesIsoOnDirectSummand`

(Lenstra, *Galois theory for schemes*, Definition 3.1, (G3)).

## Reduction (S1747) and the two algebraic inputs

S1747 reduced (G3) for the opposite category of finite etale K-algebras to two
exact statements about finite etale K-algebras:

* `S1747.EpiSurjective K`: every epimorphism `phi : B -> A of finite etale
  K-algebras (epimorphism in the category of finite etale K-algebras: any two maps
  out of A into a finite etale K-algebra that agree after precomposition with phi
  are equal) is surjective;
* `S1747.SurjectiveSplit K`: every surjective `phi : B -> A` is, up to an
  algebra isomorphism `B ~= A x C`, the first projection.

This file proves both, unconditionally and without `sorry`, and then feeds them
into the verified categorical transfer of S1786.  The result is the (G3) field in
its literal form, and -- together with the four fields that are already actual
(S1745: pullbacks and finite coproducts; S1767: terminal object; S1770: quotients
by finite groups, integrated in S1793) -- an unconditional

  `PreGaloisCategory ((CommAlgCat.FiniteEtale.{0} K)^op)`.

## Proof of EpiSurjective

Let `phi : B -> A` be an epimorphism of finite etale K-algebras.  View A as a
B-algebra through phi.  The test algebra is the tensor product `A (x)_B A`, which
is a finite etale K-algebra: it is etale over A (base change) and A is etale over K.
The two canonical K-algebra maps

  `g : A -> A (x)_B A,  a |-> a (x) 1,      h : A -> A (x)_B A,  a |-> 1 (x) a`

agree after precomposition with phi, because for `b : B` both sides are the
scalar action of b on 1.  The categorical epimorphism property gives `g = h`, hence
`a (x) 1 = 1 (x) a` for all `a : A`, i.e. `Algebra.IsEpi B A`.  Since A is
finite over B, Mathlib's `Algebra.isEpi_iff_surjective_algebraMap_of_finite`
turns this into surjectivity of `algebraMap B A`, which is phi.

## Proof of SurjectiveSplit

Let `phi : B -> A` be surjective.  By the product decomposition of finite etale
algebras over a field (Mathlib, `Algebra.Etale.iff_exists_algEquiv_prod`, the
"product of separable fields" decomposition) write

  `A ~= prod_i A_i,    B ~= prod_j B_j`

with each `A_i, B_j` a finite separable field extension of K.  Let

  `psi : prod_j B_j -> prod_i A_i`

be phi transported across these isomorphisms; it is still surjective.  For each i,
S1747.exists_factor (the classification of maps from a finite product of fields into
a field) writes the i-th component of psi as `sigma_i o eval_{m i}` for a unique
`m i : J` and an injective field map `sigma_i : B_{m i} -> A_i`.  Since psi is
surjective, each component psi_i is surjective, hence each sigma_i is surjective,
hence bijective.

The index map m is injective.  Otherwise m i1 = m i2 = m with i1 != i2; the
surjectivity of psi would produce x with `sigma_{i1}(x_m) = 1` and
`sigma_{i2}(x_m) = 0`, impossible because sigma_{i2}(1) = 1.

Now let `C := prod_{j not in range(m)} B_j` (the empty product when m is
surjective).  The algebra map

  `f : B -> A x C,  f := phi.prod (projection of prod_j B_j onto C after eB)`

is bijective: injectivity follows because two preimages have the same image in A, so
the factors in range(m) agree (sigma_i is injective), and the same image in C, so the
remaining factors agree; surjectivity follows by overwriting an arbitrary preimage
of the A-component only outside of range(m) with the prescribed C-component.  Thus f
is an algebra isomorphism, and its first projection is phi by construction.

## Categorical transfer and assembly (reused, verified files)

* S1786G3CategoricalTransferActual proves that `S1747.EpiSurjective K` and
  `S1747.SurjectiveSplit K` imply the literal `monoInducesIsoOnDirectSummand`
  field for `(CommAlgCat.FiniteEtale K)^op` (turning the opposite of the split
  `B ~= A x C` into a binary coproduct of finite etale algebras);
* S1793GaloisAssemblyWithQuotientsActual supplies the other four fields as actual
  kernel-checked instances and assembles the pre-Galois category from the (G3) field.

## Verification

* Compile command (from D:\lean):
  `lake env lean -j1 -R 'D:\lean' -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1808G3FinalActual.olean tmp/sheaf/xif/paper/S1808G3FinalActual.lean`
  -> EXIT=0, no errors, no warnings.
* Axiom audit: every declaration below depends only on
  `[propext, Classical.choice, Quot.sound]`; in particular there is no `sorryAx`
  and no new axiom.
-/

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
import tmp.sheaf.xif.paper.S1786G3CategoricalTransferActual
import tmp.sheaf.xif.paper.S1793GaloisAssemblyWithQuotientsActual

noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
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
/-- **EpiSurjective, unconditionally.**  Every epimorphism of finite etale K-algebras
(in the category of finite etale K-algebras) is surjective.  The proof uses the tensor
test algebra `A (x)_B A` together with Mathlib's
`Algebra.isEpi_iff_surjective_algebraMap_of_finite`. -/
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
/-- **SurjectiveSplit, unconditionally.**  A surjective map of finite etale K-algebras
is, up to an algebra isomorphism `B ~= A x C`, the first projection.  The proof
uses the product-of-separable-fields decomposition and S1747.exists_factor. -/
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
  -- transport phi to the product-of-fields picture
  let ψ : (∀ j, Bj j) →ₐ[K] (∀ i, Ai i) :=
    eA.toAlgHom.comp (φ.comp eB.symm.toAlgHom)
  have hψsurj : Function.Surjective ψ := by
    intro a
    obtain ⟨b, hb⟩ := hφ (eA.symm a)
    refine ⟨eB b, ?_⟩
    show eA (φ (eB.symm (eB b))) = a
    rw [AlgEquiv.symm_apply_apply, hb, AlgEquiv.apply_symm_apply]
  -- each component factors through a unique projection
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
  -- the index map is injective
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
  -- the complement algebra and the splitting map
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
    simp [f]
  exact hcomp

/-! ## (G3) and the unconditional pre-Galois category -/

/-- **(G3), unconditional.**  Every monomorphism in `(CommAlgCat.FiniteEtale K)^op`
is a coproduct injection; this is the `monoInducesIsoOnDirectSummand` field of
`PreGaloisCategory`, obtained from EpiSurjective and SurjectiveSplit by the
verified categorical transfer of S1786. -/
theorem monoInducesIsoOnDirectSummand (K : Type) [Field K] :
    S1786.MonoInducesIsoOnDirectSummandField K :=
  S1786.monoInducesIsoOnDirectSummand_of_epiSurjective_of_surjectiveSplit
    (epiSurjective K) (surjectiveSplit K)

/-- The (G3) field in the exact shape used by S1793/S1767. -/
theorem monoInducesIsoOnDirectSummand' (K : Type) [Field K] :
    S1793GaloisAssembly.MonoInducesIsoOnDirectSummandField K :=
  monoInducesIsoOnDirectSummand K

/-- The category of S1793 is definitionally the opposite of the category of finite
etale K-algebras. -/
example (K : Type) [Field K] :
    S1793GaloisAssembly.FiniteEtaleAlg K = (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ := rfl

/-- **Unconditional pre-Galois category.**  All five fields of
`PreGaloisCategory (CommAlgCat.FiniteEtale K)^op` are now actual proofs:
terminal object (S1767), pullbacks and finite coproducts (S1745), quotients by finite
groups (S1770), and (G3) (this file). -/
theorem preGaloisCategory (K : Type) [Field K] :
    PreGaloisCategory (S1793GaloisAssembly.FiniteEtaleAlg K) :=
  S1793GaloisAssembly.preGaloisCategory (K := K) (monoInducesIsoOnDirectSummand K)

/-- The same statement at the category written literally as
`(CommAlgCat.FiniteEtale K)^op`. -/
theorem preGaloisCategory' (K : Type) [Field K] :
    PreGaloisCategory ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) :=
  preGaloisCategory K

/-- **Downstream check: Galois category.**  Adding a fibre-functor structure on the
geometric fibre functor (the remaining hypothesis of S1793/S1767, not addressed here)
produces Mathlib's `GaloisCategory` instance. -/
theorem galoisCategory (K : Type) [Field K]
    (hFiber : S1793GaloisAssembly.FiberFunctorField K
      (S1793GaloisAssembly.preGaloisCategory (K := K) (monoInducesIsoOnDirectSummand K))) :
    GaloisCategory (S1793GaloisAssembly.FiniteEtaleAlg K) :=
  S1793GaloisAssembly.galoisCategory (K := K) (monoInducesIsoOnDirectSummand K) hFiber

end S1808

/-! ### Axiom audit -/

#print axioms S1808.injective_of_field
#print axioms S1808.etale_of_finite_separable
#print axioms S1808.epiSurjective
#print axioms S1808.surjectiveSplit
#print axioms S1808.monoInducesIsoOnDirectSummand
#print axioms S1808.monoInducesIsoOnDirectSummand'
#print axioms S1808.preGaloisCategory
#print axioms S1808.preGaloisCategory'
#print axioms S1808.galoisCategory
