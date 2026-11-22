import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Prod
import tmp.sheaf.xif.paper.S1747FiniteEtaleMonoSplitActual

/-!
# S1811: S1747.SurjectiveSplit K --- splitting a surjection of finite etale algebras

S1747 reduced the (G3) axiom 'monoInducesIsoOnDirectSummand' of 'PreGaloisCategory'
for '(CommAlgCat.FiniteEtale K)^op' to two algebraic statements, of which

  S1747.SurjectiveSplit K:
  a surjective K-algebra map 'phi : B ->[K] A' between finite etale K-algebras is,
  up to an algebra isomorphism 'B =~[K] A x C', the first projection,

was left open (a 'precise missing' input).  This file proves it, with no 'sorry', no new
axiom and no change of statement.

## The argument

Mathlib's 'Algebra.Etale.iff_exists_algEquiv_prod' writes B as a finite product of finite
separable field extensions, 'eB : B =~[K] (forall j : J, Bj j)'.  (No decomposition of A
is needed.)

Let 'psi : (forall j, Bj j) ->[K] A' be 'phi' transported along 'eB' and let

  S := {j | psi (Pi.single j 1) = 0}

be the set of components of the product that 'psi' kills.  The kernel of 'psi' is exactly
the set of elements supported on S:

* if j is in S then 'psi (Pi.single j x) = psi (Pi.single j 1) * psi (Pi.single j x) = 0',
  so every element supported on S (a sum of such terms) is killed;
* conversely, if 'psi b = 0' and 'b j != 0', then
  'Pi.single j 1 = Pi.single j ((b j)^{-1}) * Pi.single j (b j)', hence
  'psi (Pi.single j 1) = psi (Pi.single j ((b j)^{-1})) * psi b = 0', i.e. j is in S.

Then 'C := forall j : S, Bj j' (a finite product of finite separable fields, hence finite
etale) and

  'e' : (forall j, Bj j) =~[K] A x C,  b |-> (psi b, b restricted to S)',

is an algebra isomorphism: injective because 'psi b = 0' forces b to vanish off S while
the second component forces b to vanish on S; surjective because for '(a, c)' we choose
'b0' with 'psi b0 = a' and replace its S-coordinates by c, which changes 'psi b' by an
element of the kernel.  Finally 'e := eB.trans e'' is an isomorphism 'B =~[K] A x C'
whose first projection is 'phi'.

## Contents

* 'S1811.pi_single_one_mul': 'Pi.single j 1 * b = Pi.single j (b j)'.
* 'S1811.split_prod': the splitting for a product of fields (the mathematical core).
* 'S1811.surjectiveSplit': 'S1747.SurjectiveSplit K'.

## References

* S1747: 'tmp/sheaf/xif/paper/S1747FiniteEtaleMonoSplitActual.lean'
* Lenstra, Galois theory for schemes, Definition 3.1 (G3).
-/

noncomputable section

open Finset

namespace S1811

/-- In a product of commutative rings, multiplying by 'Pi.single j 1' picks out the
j-th coordinate. -/
lemma pi_single_one_mul {J : Type} [DecidableEq J] (Bj : J → Type*) [∀ j, CommRing (Bj j)]
    (j : J) (b : ∀ k, Bj k) : Pi.single j (1 : Bj j) * b = Pi.single j (b j) := by
  ext k
  by_cases h : k = j
  · subst h; simp
  · rw [Pi.mul_apply, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, zero_mul]

/-- **The mathematical core.**  A surjective K-algebra map out of a finite product of
fields splits as the first projection, with complement the product over the set of
components killed by the map.

The hypotheses 'hfin', 'hsep' say that each factor is a finite separable field extension
of K, so that the complement is again a finite etale K-algebra. -/
theorem split_prod {K : Type} [Field K] {J : Type} [Fintype J]
    (Bj : J → Type) [F : ∀ j, Field (Bj j)] [Aalg : ∀ j, Algebra K (Bj j)]
    {A : Type} [CommRing A] [Algebra K A]
    (ψ : (∀ j, Bj j) →ₐ[K] A) (hψ : Function.Surjective ψ)
    (hfin : ∀ j, Module.Finite K (Bj j)) (hsep : ∀ j, Algebra.IsSeparable K (Bj j)) :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra K C) (_ : Module.Finite K C)
      (_ : Algebra.Etale K C) (e : (∀ j, Bj j) ≃ₐ[K] A × C),
      (AlgHom.fst (R := K) (A := A) (B := C)).comp e.toAlgHom = ψ := by
  classical
  -- the set of components killed by psi
  let S : Set J := {j | ψ (Pi.single j 1) = 0}
  -- (a) psi kills the j-th component for j in S
  have hsingle : ∀ (j : J), j ∈ S → ∀ x : Bj j, ψ (Pi.single j x) = 0 := by
    intro j hj x
    rw [show Pi.single j x = Pi.single j (1 : Bj j) * Pi.single j x by
      rw [← Pi.single_mul, one_mul]]
    rw [map_mul, hj, zero_mul]
  -- (b) anything supported on S is killed by psi
  have hsupp : ∀ b : ∀ j, Bj j, (∀ j, j ∉ S → b j = 0) → ψ b = 0 := by
    intro b hb
    rw [← Finset.univ_sum_single (M := Bj) b, map_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    by_cases hj : j ∈ S
    · exact hsingle j hj (b j)
    · rw [hb j hj, Pi.single_zero, map_zero]
  -- (c) anything killed by psi vanishes off S
  have hvan : ∀ b : ∀ j, Bj j, ψ b = 0 → ∀ j, j ∉ S → b j = 0 := by
    intro b hb j hj
    by_contra hne
    have h2 : ψ (Pi.single j (b j)) = 0 := by
      rw [← pi_single_one_mul Bj j b, map_mul, hb, mul_zero]
    have h1 : ψ (Pi.single j (1 : Bj j)) = 0 := by
      rw [show Pi.single j (1 : Bj j) = Pi.single j ((b j)⁻¹) * Pi.single j (b j) by
        rw [← Pi.single_mul, inv_mul_cancel₀ hne]]
      rw [map_mul, h2, mul_zero]
    exact hj h1
  -- each factor is a finite etale K-algebra
  have hEtale : ∀ j, Algebra.Etale K (Bj j) := by
    intro j
    exact (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := Bj j)).mpr
      ⟨PUnit, inferInstance, fun _ => Bj j, fun _ => F j, fun _ => Aalg j,
        (AlgEquiv.funUnique K PUnit (Bj j)).symm, fun _ => ⟨hfin j, hsep j⟩⟩
  letI : ∀ j, Algebra.Etale K (Bj j) := hEtale
  -- the complement
  let C : Type := ∀ j : {j // j ∈ S}, Bj j.1
  letI hCring : CommRing C := inferInstance
  letI hCalg : Algebra K C := inferInstance
  letI hCfin : Module.Finite K C := inferInstance
  letI hCet : Algebra.Etale K C := inferInstance
  -- the two components of the isomorphism
  let ρ : (∀ j, Bj j) →ₐ[K] C := AlgHom.pi fun j : {j // j ∈ S} => Pi.evalAlgHom K Bj j.1
  let e' : (∀ j, Bj j) →ₐ[K] A × C := ψ.prod ρ
  have hρ_apply : ∀ (b : ∀ j, Bj j) (j : {j // j ∈ S}), ρ b j = b j.1 := by
    intro b j
    rfl
  have hbij : Function.Bijective e' := by
    constructor
    · -- injectivity
      intro b1 b2 h
      have h1 : ψ b1 = ψ b2 := congrArg Prod.fst h
      have h2 : ρ b1 = ρ b2 := congrArg Prod.snd h
      have hsub : ψ (b1 - b2) = 0 := by rw [map_sub, h1, sub_self]
      have hv := hvan _ hsub
      funext j
      by_cases hj : j ∈ S
      · have h3 := congrFun h2 ⟨j, hj⟩
        rw [hρ_apply, hρ_apply] at h3
        exact h3
      · have h4 := hv j hj
        exact sub_eq_zero.mp (by simpa using h4)
    · -- surjectivity
      rintro ⟨a, c⟩
      obtain ⟨b0, hb0⟩ := hψ a
      refine ⟨fun j => if h : j ∈ S then c ⟨j, h⟩ else b0 j, ?_⟩
      have hpt : ∀ j, j ∉ S →
          ((fun j => if h : j ∈ S then c ⟨j, h⟩ else b0 j) - b0) j = 0 := by
        intro j hj
        simp [hj]
      have hzero : ψ ((fun j => if h : j ∈ S then c ⟨j, h⟩ else b0 j) - b0) = 0 :=
        hsupp _ hpt
      rw [map_sub] at hzero
      have hψb : ψ (fun j => if h : j ∈ S then c ⟨j, h⟩ else b0 j) = a := by
        rw [sub_eq_zero.mp hzero, hb0]
      have hρb : ρ (fun j => if h : j ∈ S then c ⟨j, h⟩ else b0 j) = c := by
        funext j
        rw [hρ_apply, dif_pos j.2]
      exact Prod.ext hψb hρb
  let e : (∀ j, Bj j) ≃ₐ[K] A × C := AlgEquiv.ofBijective e' hbij
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, e, ?_⟩
  have he : e.toAlgHom = e' := rfl
  rw [he]
  exact AlgHom.fst_prod ψ ρ

/-- **S1747.SurjectiveSplit.**  A surjective map of finite etale K-algebras is, up to an
algebra isomorphism 'B =~[K] A x C', the first projection. -/
theorem surjectiveSplit {K : Type} [Field K] : S1747.SurjectiveSplit K := by
  intro A B hAR hAA hAF hAE hBR hBA hBF hBE φ hφ
  classical
  -- decompose B as a product of finite separable fields
  obtain ⟨J, hJfin, Bj, hBjfield, hBjalg, eB, hBj⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := B)).mp hBE
  letI : Fintype J := Fintype.ofFinite J
  letI hF : ∀ j, Field (Bj j) := hBjfield
  letI hAalg : ∀ j, Algebra K (Bj j) := hBjalg
  have hfin : ∀ j, Module.Finite K (Bj j) := fun j => (hBj j).1
  have hsep : ∀ j, Algebra.IsSeparable K (Bj j) := fun j => (hBj j).2
  -- the coordinate map
  let ψ : (∀ j, Bj j) →ₐ[K] A := φ.comp eB.symm.toAlgHom
  have hψ : Function.Surjective ψ := hφ.comp eB.symm.surjective
  -- the splitting in coordinates
  obtain ⟨C, hCring, hCalg, hCfin, hCet, e', he'⟩ := split_prod Bj ψ hψ hfin hsep
  letI : CommRing C := hCring
  letI : Algebra K C := hCalg
  letI : Module.Finite K C := hCfin
  letI : Algebra.Etale K C := hCet
  refine ⟨C, hCring, hCalg, hCfin, hCet, eB.trans e', ?_⟩
  -- the first projection of the composite is phi
  have hfst : (AlgHom.fst (R := K) (A := A) (B := C)).comp e'.toAlgHom = ψ := he'
  ext x
  have h1 : (eB.trans e').toAlgHom x = e' (eB x) := rfl
  rw [AlgHom.comp_apply, h1]
  have h2 : (AlgHom.fst (R := K) (A := A) (B := C)) (e' (eB x)) = ψ (eB x) := by
    have hh := AlgHom.congr_fun hfst (eB x)
    simpa using hh
  rw [h2]
  have h3 : ψ (eB x) = φ (eB.symm (eB x)) := rfl
  rw [h3, AlgEquiv.symm_apply_apply]

end S1811

/-! ### Axiom audit -/

#print axioms S1811.pi_single_one_mul
#print axioms S1811.split_prod
#print axioms S1811.surjectiveSplit