import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# S1747: the G3 axiom (monoInducesIsoOnDirectSummand) for finite etale K-algebras

S1739 left the monoInducesIsoOnDirectSummand field of
PreGaloisCategory ((CommAlgCat.FiniteEtale K)^op) open.  In the opposite category a
monomorphism is an epimorphism phi : B --> A of finite etale K-algebras, and the
axiom asks that B be the product A x C with phi the first projection.

## What is proved here (no sorry, no axiom, no fake data)

* S1747.exists_factor: a map from a finite product of fields into a field factors
  through a unique projection.  This is the algebraic classification of maps out of a
  product that the standard proof of (G3) needs.
* S1747.finiteEtaleSplit_of_epiSurjective_of_surjectiveSplit: the algebraic splitting
  statement follows from the two precise missing lemmas EpiSurjective and
  SurjectiveSplit, which are stated below with their exact quantifiers.

## The precise missing input

Mathlib (v4.32.2, commit 905b9581) has Algebra.Etale.iff_exists_algEquiv_prod:
a finite etale K-algebra is a finite product of finite separable field extensions
of K.  On top of it, the following two statements about finite etale K-algebras are
needed.  Both are mathematically true; neither is in Mathlib.

EpiSurjective K :
  for finite etale K-algebras B, A, every map phi : B --> A that is an epimorphism
  in the category of finite etale K-algebras is surjective.

SurjectiveSplit K :
  for finite etale K-algebras B, A, every surjective map phi : B --> A is, up to an
  algebra isomorphism B ~= A x C, the first projection.

### Proof of EpiSurjective (mathematical sketch)

Write B ~= prod_j B_j and A ~= prod_i A_i as products of finite separable fields
(Algebra.Etale.iff_exists_algEquiv_prod).  For each i the component
prod_j B_j --> A_i factors through a unique j(i) with an injective field map
sigma_i : B_{j(i)} --> A_i (exists_factor).  If j is not injective, say
j(i1) = j(i2) = m with i1 != i2, then the finite etale test algebra
A_{i1} (x)_{B_m} A_{i2} carries two maps out of prod_i A_i that agree after
precomposition with phi but are not equal.  If some sigma_i is not surjective,
the finite etale test algebra A_i (x)_{B_m} A_i plays the same role: the two canonical
maps a |-> a (x) 1 and a |-> 1 (x) a agree on the image of phi; if they were
equal, the multiplication map would be an isomorphism and the rank computation
finrank_{B_m} (A_i (x)_{B_m} A_i) = [A_i : B_m]^2 would force [A_i : B_m] = 1,
contradicting non-surjectivity.

### Proof of SurjectiveSplit (mathematical sketch)

With the same product decompositions, surjectivity of phi forces j to be injective
and each sigma_i to be bijective.  Then A ~= prod_{j in range j} B_j and the
complement is C := prod_{j not in range j} B_j; the map
B ~= A x C, b |-> (phi b, (b_j)_{j not in range j}) is an algebra isomorphism whose
first projection is phi.

### Why this is not formalized here

Step 3 of the first proof needs the tensor-product test algebras
A_{i1} (x)_{B_m} A_{i2} and A_i (x)_{B_m} A_i together with the finrank
computation over B_m.  The algebraic instances for tensor products over an
intermediate algebra B_m (the Algebra K structure obtained from the left factor and
the scalar tower K --> B_m --> A_i) and the finrank bookkeeping are the missing
formalization work; the mathematical statements above are complete and correct.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Finset

namespace S1747

/-- In a field the only idempotents are 0 and 1. -/
lemma idem_eq_zero_or_one {L : Type} [Field L] {x : L} (hx : IsIdempotentElem x) :
    x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp (show x * (1 - x) = 0 by
    rw [mul_sub, mul_one, hx.eq, sub_self]) with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h).symm

/-- A map from a finite product of fields into a field factors through a unique
projection.  This is the algebraic core of the classification of maps out of a product:
the idempotents Pi.single j 1 map to 0 or 1, exactly one maps to 1, and the
map kills every factor whose idempotent maps to 0. -/
theorem exists_factor {K : Type} [Field K] {J : Type} [Finite J]
    (Bj : J → Type) [∀ j, Field (Bj j)] [∀ j, Algebra K (Bj j)]
    {L : Type} [Field L] [Algebra K L] (ψ : (∀ j, Bj j) →ₐ[K] L) :
    ∃ (j : J) (σ : Bj j →ₐ[K] L), ψ = σ.comp (Pi.evalAlgHom K Bj j) := by
  classical
  haveI : Fintype J := Fintype.ofFinite J
  have hidem : ∀ j, IsIdempotentElem (Pi.single (M := Bj) j 1) := by
    intro j
    ext k
    by_cases h : k = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne, h]
  have horth : ∀ j k, j ≠ k → Pi.single (M := Bj) j 1 * Pi.single (M := Bj) k 1 = 0 := by
    intro j k hjk
    ext l
    by_cases hl : l = j
    · subst hl
      simp [Pi.single_eq_of_ne, hjk]
    · simp [Pi.single_eq_of_ne, hl]
  have hsum : (∑ j, Pi.single (M := Bj) j (1 : Bj j)) = 1 := by
    ext k
    simp
  have hfidem : ∀ j, IsIdempotentElem (ψ (Pi.single (M := Bj) j 1)) := fun j => (hidem j).map ψ
  have hfsum : (∑ j, ψ (Pi.single (M := Bj) j 1)) = 1 := by
    rw [← map_sum, hsum, map_one]
  have hex : ∃ j, ψ (Pi.single (M := Bj) j 1) = 1 := by
    by_contra h
    push Not at h
    have hzero : ∀ j, ψ (Pi.single (M := Bj) j 1) = 0 := by
      intro j
      rcases idem_eq_zero_or_one (hfidem j) with h0 | h1
      · exact h0
      · exact absurd h1 (h j)
    rw [Finset.sum_congr rfl (fun j _ => hzero j), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_zero] at hfsum
    exact zero_ne_one hfsum
  obtain ⟨j0, hj0⟩ := hex
  have huniq : ∀ j, ψ (Pi.single (M := Bj) j 1) = 1 → j = j0 := by
    intro j hj
    by_contra hne
    have h0 : ψ (Pi.single (M := Bj) j 1) * ψ (Pi.single (M := Bj) j0 1) = 0 := by
      rw [← map_mul, horth j j0 hne, map_zero]
    rw [hj, hj0, one_mul] at h0
    exact one_ne_zero h0
  let σFun : Bj j0 → L := fun y => ψ (Pi.single (M := Bj) j0 y)
  have hσ_one : σFun 1 = 1 := hj0
  have hσ_mul : ∀ x y, σFun (x * y) = σFun x * σFun y := by
    intro x y
    simp only [σFun]
    rw [← map_mul, Pi.single_mul]
  have hσ_zero : σFun 0 = 0 := by simp [σFun]
  have hσ_add : ∀ x y, σFun (x + y) = σFun x + σFun y := by
    intro x y
    simp only [σFun]
    rw [← map_add, Pi.single_add]
  have hσ_smul : ∀ (k : K) (x : Bj j0), σFun (k • x) = k • σFun x := by
    intro k x
    simp only [σFun]
    rw [Pi.single_smul, map_smul]
  let σ : Bj j0 →ₐ[K] L :=
    { toFun := σFun
      map_one' := hσ_one
      map_mul' := hσ_mul
      map_zero' := hσ_zero
      map_add' := hσ_add
      commutes' := fun k => by
        rw [Algebra.algebraMap_eq_smul_one, hσ_smul, hσ_one,
          Algebra.algebraMap_eq_smul_one] }
  refine ⟨j0, σ, ?_⟩
  ext x
  show ψ x = ψ (Pi.single (M := Bj) j0 (x j0))
  conv_lhs => rw [← Finset.univ_sum_single (M := Bj) x]
  rw [map_sum, Finset.sum_eq_single_of_mem j0 (Finset.mem_univ _)]
  intro b _ hb
  have hker : Pi.single (M := Bj) b (x b) =
      Pi.single (M := Bj) b 1 * Pi.single (M := Bj) b (x b) := by
    ext k
    by_cases hk : k = b
    · subst hk; simp
    · simp [Pi.single_eq_of_ne, hk]
  rw [hker, map_mul]
  have hz : ψ (Pi.single (M := Bj) b 1) = 0 := by
    rcases idem_eq_zero_or_one (hfidem b) with h1 | h1
    · exact h1
    · exact absurd (huniq b h1) hb
  rw [hz, zero_mul]

/-! ### The two precise missing statements -/

/-- MISSING (Mathlib): every epimorphism of finite etale K-algebras, in the category
of finite etale K-algebras, is surjective.

The hypothesis hphi is epimorphy: any two maps out of A into a finite etale
K-algebra that agree after precomposition with phi are equal. -/
def EpiSurjective (K : Type) [Field K] : Prop :=
  ∀ (A B : Type) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A]
    [CommRing B] [Algebra K B] [Module.Finite K B] [Algebra.Etale K B]
    (φ : B →ₐ[K] A),
    (∀ (T : Type) [CommRing T] [Algebra K T] [Module.Finite K T] [Algebra.Etale K T]
      (g h : A →ₐ[K] T), g.comp φ = h.comp φ → g = h) →
    Function.Surjective φ

/-- MISSING (Mathlib): a surjective map B --> A of finite etale K-algebras is,
up to an algebra isomorphism B ~= A x C, the first projection. -/
def SurjectiveSplit (K : Type) [Field K] : Prop :=
  ∀ (A B : Type) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A]
    [CommRing B] [Algebra K B] [Module.Finite K B] [Algebra.Etale K B]
    (φ : B →ₐ[K] A), Function.Surjective φ →
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra K C) (_ : Module.Finite K C)
      (_ : Algebra.Etale K C) (e : B ≃ₐ[K] A × C),
      (AlgHom.fst (R := K) (A := A) (B := C)).comp e.toAlgHom = φ

/-- The algebraic form of (G3) for finite etale K-algebras, obtained by combining the
two missing statements. -/
theorem finiteEtaleSplit_of_epiSurjective_of_surjectiveSplit
    {K : Type} [Field K] (h1 : EpiSurjective K) (h2 : SurjectiveSplit K)
    (A B : Type) [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.Etale K A]
    [CommRing B] [Algebra K B] [Module.Finite K B] [Algebra.Etale K B]
    (φ : B →ₐ[K] A)
    (hφ : ∀ (T : Type) [CommRing T] [Algebra K T] [Module.Finite K T] [Algebra.Etale K T]
      (g h : A →ₐ[K] T), g.comp φ = h.comp φ → g = h) :
    ∃ (C : Type) (_ : CommRing C) (_ : Algebra K C) (_ : Module.Finite K C)
      (_ : Algebra.Etale K C) (e : B ≃ₐ[K] A × C),
      (AlgHom.fst (R := K) (A := A) (B := C)).comp e.toAlgHom = φ :=
  h2 A B φ (h1 A B φ hφ)

end S1747

/-! ### Axiom audit -/

#print axioms S1747.idem_eq_zero_or_one
#print axioms S1747.exists_factor
#print axioms S1747.finiteEtaleSplit_of_epiSurjective_of_surjectiveSplit
