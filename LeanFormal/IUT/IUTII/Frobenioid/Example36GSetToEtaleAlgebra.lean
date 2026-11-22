import LeanFormal.IUT.IUTII.Frobenioid.Example36GaloisCorrespondence
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.Algebra.Pi
import LeanFormal.IUT.IUTII.Frobenioid.Example36SpecEssentialSurjectivity

/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
# F1f: converse object map finite G_K-sets to finite etale K-algebras

This module attacks the converse direction of the field Galois correspondence:
from a finite continuous G_K-set to a finite etale K-algebra.

Proved (actual):
* the absolute Galois group G_K = Gal(Kbar/K) is Mathlib's profinite Galois
  group at the separable closure;
* for an open subgroup H of G_K, the fixed field L_H = Kbar^H is an
  intermediate field of the separable closure, and it is finite dimensional over
  K.  This is the finite-extension side of the infinite Galois correspondence,
  proved from Mathlib's InfiniteGalois.isOpen_iff_finite and
  InfiniteGalois.fixingSubgroup_fixedField (the same argument as the tree's
  LocalUnitKummerInjectivity FixedField / fixedField_finiteDimensional pattern).

Further proved (actual, unconditional):
* the fixed field of an open subgroup is separable over K (subextension of the
  separable closure; the ambient instance is separableClosure.isSeparable and
  transfers by Subalgebra.isSeparable_iff), hence finite etale, packaged as a
  CommAlgCat.FiniteEtale object;
* a finite product of finite etale K-algebras is finite etale (product closure);
* for a finite continuous G_K-set, the orbit quotient is finite, each orbit
  stabilizer is open, and the product of the orbit fixed fields gives the actual
  object map A_X into CommAlgCat.FiniteEtale K.

Frozen exact remaining cards (no inhabitant, no fake algebra):
* GSetToEtaleFiberCard: the fiber of A_X at the separable closure is isomorphic
  to X, and the object-level roundtrip with the task-74 object map
  finiteEtaleObjectToGSet (the product-to-disjoint-union Hom decomposition and
  the infinite Galois description Hom(L_H, Kbar) = G_K/H are not formalized);
* GSetToEtaleNaturalityCard: functoriality/naturality and unit/counit of the
  induced equivalence; the full equivalence remains the frozen
  FieldGaloisCorrespondence card.

Boundary: no fake finite etale algebra and no fake equivalence.  Fixed fields,
their finite etale packaging, product closure and the object map A_X are proved;
the fiber/roundtrip and naturality are isolated as named unproved structures.  No
curve Pi_1, theta/q-pilot or D6 geometric claim is made.
-/

noncomputable section

open CategoryTheory
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.IUTII.Frobenioid.Example36.GaloisCorrespondence

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36.GSetToEtaleAlgebra

universe u

variable (K : Type u) [Field K]

/-- The absolute Galois group of K as a topological group. -/
abbrev galoisGroup : Type u := ↥(Iut.AbsoluteGaloisProfinite K)

/-- The tree's absolute Galois group is Mathlib's profinite Galois group at the
separable closure. -/
theorem galoisGroup_eq :
    Iut.AbsoluteGaloisProfinite K =
      InfiniteGalois.profiniteGalGrp K (SeparableClosure K) :=
  rfl

/-! ## 1. Fixed fields of open subgroups: finite dimensional over K -/

/-- The fixed field of an open subgroup H of G_K inside the separable closure. -/
noncomputable def openSubgroupFixedField
    (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K)) :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.fixedField H.toSubgroup

/-- The finite-extension side of the infinite Galois correspondence: the fixed
field of an open subgroup is finite dimensional over K. -/
theorem openSubgroupFixedField_finiteDimensional
    (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K)) :
    FiniteDimensional K (openSubgroupFixedField K H) := by
  let closedSubgroup : ClosedSubgroup (Iut.AbsoluteGaloisProfinite K) :=
    { toSubgroup := H.toSubgroup
      isClosed' := H.isClosed }
  apply
    (InfiniteGalois.isOpen_iff_finite
      (IntermediateField.fixedField H.toSubgroup)).mp
  change IsOpen
    ((IntermediateField.fixedField
      closedSubgroup.toSubgroup).fixingSubgroup.carrier)
  rw [InfiniteGalois.fixingSubgroup_fixedField closedSubgroup]
  exact H.isOpen

/-- The fixed field of an open subgroup is a finite K-module (from finite
dimensionality). -/
noncomputable instance openSubgroupFixedField_moduleFinite
    (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K)) :
    Module.Finite K (openSubgroupFixedField K H) := by
  haveI := openSubgroupFixedField_finiteDimensional K H
  exact inferInstance

/-- A finite separable field extension is an etale algebra: formally etale by
separability, finitely presented because it is finite type over the Noetherian
field K. -/
noncomputable instance algebraEtale_of_finiteDimensional_isSeparable
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] : Algebra.Etale K L where
  formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
  finitePresentation := by
    haveI : IsNoetherianRing K := inferInstance
    exact (Algebra.FinitePresentation.of_finiteType (R := K) (A := L)).mp inferInstance

/-- **Separability of the fixed field**: the fixed field Kbar^H is separable
over K because it is a subextension of the separable closure.  SeparableClosure K
is definitionally the separable closure inside the algebraic closure, so the
ambient separability instance is separableClosure.isSeparable; it transfers to
the subalgebra Kbar^H by Subalgebra.isSeparable_iff. -/
noncomputable instance openSubgroupFixedField_isSeparable
    (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K)) :
    Algebra.IsSeparable K (openSubgroupFixedField K H) := by
  let S : Subalgebra K (SeparableClosure K) :=
    (IntermediateField.fixedField H.toSubgroup).toSubalgebra
  have hS : Algebra.IsSeparable K S := by
    rw [Subalgebra.isSeparable_iff]
    intro x hx
    haveI : Algebra.IsSeparable K (SeparableClosure K) :=
      separableClosure.isSeparable K (AlgebraicClosure K)
    exact Algebra.IsSeparable.isSeparable K (x : SeparableClosure K)
  exact hS

/-- The fixed field of an open subgroup, packaged as a finite etale K-algebra
(unconditional): finite dimensional by the infinite Galois correspondence,
separable as a subextension of the separable closure. -/
noncomputable def openSubgroupFixedFieldFiniteEtale
    (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K)) :
    CommAlgCat.FiniteEtale.{u} K := by
  haveI := openSubgroupFixedField_finiteDimensional K H
  haveI := openSubgroupFixedField_isSeparable K H
  exact CommAlgCat.FiniteEtale.of K ↥(openSubgroupFixedField K H)

/-! ## 2. Finite continuous G_K-sets -/

/-- A finite G_K-set with the continuity condition: every point stabilizer is
open in G_K. -/
structure FiniteContinuousGSet (K : Type u) [Field K] where
  /-- The underlying finite G_K-set. -/
  toGSet : FiniteGaloisSetCategory K
  /-- Every point stabilizer is open in G_K. -/
  stabilizer_isOpen : ∀ x : ↥toGSet.V,
    IsOpen
      (MulAction.stabilizer (Iut.AbsoluteGaloisProfinite K) x :
        Set (Iut.AbsoluteGaloisProfinite K))

/-- Product closure: a finite product of finite etale K-algebras is a finite
etale K-algebra (Mathlib's Module.Finite.pi and the Etale product instance). -/
noncomputable def productFiniteEtale {ι : Type u} [Fintype ι]
    (A : ι → CommAlgCat.FiniteEtale.{u} K) : CommAlgCat.FiniteEtale.{u} K :=
  CommAlgCat.FiniteEtale.of K (Π i, ↥(A i).obj)

/-! ## 2b. Orbit decomposition and the object map A_X -/

namespace FiniteContinuousGSet

variable {K} (X : FiniteContinuousGSet K)

/-- The orbit quotient of a finite continuous G_K-set. -/
abbrev orbitIndex : Type u :=
  MulAction.orbitRel.Quotient (Iut.AbsoluteGaloisProfinite K) X.toGSet.V

/-- The orbit quotient of a finite G_K-set is finite. -/
instance orbitIndex_finite : Finite X.orbitIndex := by
  haveI : Finite ↥X.toGSet.V := X.toGSet.V.property
  exact Finite.of_surjective (Quotient.mk'' : ↥X.toGSet.V → X.orbitIndex)
    Quotient.mk''_surjective

instance orbitIndex_fintype : Fintype X.orbitIndex :=
  Fintype.ofFinite X.orbitIndex

/-- The open stabilizer attached to an orbit (represented by Quotient.out). -/
noncomputable def orbitStabilizer (q : X.orbitIndex) :
    OpenSubgroup (Iut.AbsoluteGaloisProfinite K) where
  toSubgroup := MulAction.stabilizer (Iut.AbsoluteGaloisProfinite K) q.out
  isOpen' := X.stabilizer_isOpen q.out

/-- The fixed field of the stabilizer of an orbit. -/
noncomputable def orbitFixedField (q : X.orbitIndex) :
    IntermediateField K (SeparableClosure K) :=
  openSubgroupFixedField K (X.orbitStabilizer q)

/-- Each orbit fixed field is finite dimensional over K. -/
theorem orbitFixedField_finiteDimensional (q : X.orbitIndex) :
    FiniteDimensional K (X.orbitFixedField q) :=
  openSubgroupFixedField_finiteDimensional K (X.orbitStabilizer q)

/-- The product of the orbit fixed fields: the actual object map A_X from a
finite continuous G_K-set to a finite etale K-algebra. -/
noncomputable def gSetToFiniteEtaleObject : CommAlgCat.FiniteEtale.{u} K :=
  productFiniteEtale K
    (fun q : X.orbitIndex =>
      openSubgroupFixedFieldFiniteEtale K (X.orbitStabilizer q))

/-- Identity `AlgEquiv` from the forgetful carrier of the orbit-product object to
the explicit Pi type of fixed fields (the underlying types are definitionally
equal; this bridges the different `CommRing` instances without type rewriting). -/
noncomputable def gSetToFiniteEtaleObjectAlgEquiv (X : FiniteContinuousGSet K) :
    (↥(gSetToFiniteEtaleObject X) : Type u) ≃ₐ[K]
      (Π q : X.orbitIndex, ↥(openSubgroupFixedField K (X.orbitStabilizer q))) where
  toFun x := x
  invFun x := x
  left_inv x := rfl
  right_inv x := rfl
  map_mul' x y := rfl
  map_add' x y := rfl
  commutes' k := rfl

end FiniteContinuousGSet

/-! ## 2c. Step 4i ingredients: idempotent factorization of algebra maps out of a finite product -/

section PiFactorizationIngredients

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
variable {F : Type u} [Field F] [Algebra K F]

/-- The idempotents Pi.single i 1 form a complete orthogonal family in the
product algebra (Mathlib's CompleteOrthogonalIdempotents.single). -/
theorem piSingle_completeOrthogonal (φ : (Π i, A i) →ₐ[K] F) :
    CompleteOrthogonalIdempotents (fun i => φ (Pi.single i (1 : A i))) :=
  (CompleteOrthogonalIdempotents.single (fun i => A i)).map φ.toRingHom

/-- Each phi (Pi.single i 1) is an idempotent in the field F. -/
theorem piSingle_phi_idempotent (φ : (Π i, A i) →ₐ[K] F) (i : ι) :
    IsIdempotentElem (φ (Pi.single i (1 : A i))) := by
  rw [IsIdempotentElem, ← map_mul, ← Pi.single_mul]
  simp

/-- Each phi (Pi.single i 1) is 0 or 1 in the field F. -/
theorem piSingle_phi_eq_zero_or_one (φ : (Π i, A i) →ₐ[K] F) (i : ι) :
    φ (Pi.single i (1 : A i)) = 0 ∨ φ (Pi.single i (1 : A i)) = 1 :=
  IsIdempotentElem.iff_eq_zero_or_one.mp (piSingle_phi_idempotent K A φ i)

/-- The sum of the images of the idempotents is 1. -/
theorem piSingle_phi_sum (φ : (Π i, A i) →ₐ[K] F) :
    (∑ i, φ (Pi.single i (1 : A i))) = 1 := by
  have hsum : (∑ i, Pi.single i (1 : A i)) = (1 : Π i, A i) :=
    Finset.univ_sum_single 1
  rw [← map_sum, hsum, map_one]

/-- At least one idempotent maps to 1: this is the index through which phi
factors. -/
theorem exists_piSingle_phi_eq_one (φ : (Π i, A i) →ₐ[K] F) :
    ∃ i, φ (Pi.single i (1 : A i)) = 1 := by
  by_contra h
  push_neg at h
  have hzero : ∀ i, φ (Pi.single i (1 : A i)) = 0 := fun i =>
    (piSingle_phi_eq_zero_or_one K A φ i).resolve_right (h i)
  have hzero_sum : (∑ i, φ (Pi.single i (1 : A i))) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hzero i)]
    simp
  have hsum := piSingle_phi_sum K A φ
  rw [hzero_sum] at hsum
  exact zero_ne_one hsum

/-- The index with phi (Pi.single i 1) = 1 is unique, as the idempotents are
orthogonal. -/
theorem piSingle_phi_eq_one_unique (φ : (Π i, A i) →ₐ[K] F) {i j : ι}
    (hi : φ (Pi.single i (1 : A i)) = 1)
    (hj : φ (Pi.single j (1 : A j)) = 1) : i = j := by
  by_contra hij
  have hprod : φ (Pi.single i (1 : A i)) * φ (Pi.single j (1 : A j)) = 0 := by
    rw [← map_mul]
    have hzero : Pi.single i (1 : A i) * Pi.single j (1 : A j) = 0 := by
      ext k
      by_cases hki : k = i
      · subst hki
        simp [Pi.single_apply, Ne.symm hij]
      · by_cases hkj : k = j
        · subst hkj
          simp [Pi.single_apply, hki]
        · simp [Pi.single_apply, hki, hkj]
    rw [hzero, map_zero]
  rw [hi, hj, mul_one] at hprod
  exact one_ne_zero hprod

end PiFactorizationIngredients

section PiFactorizationAssembly

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
variable {F : Type u} [Field F] [Algebra K F]

/-- The forward direction of the product-factorization comparison: factor phi
through the unique coordinate i0 with phi (Pi.single i0 1) = 1. -/
noncomputable def algHomPiForward (φ : (Π i, A i) →ₐ[K] F) :
    Σ i, A i →ₐ[K] F :=
  let i0 := Classical.choose (exists_piSingle_phi_eq_one K A φ)
  let hi : φ (Pi.single i0 (1 : A i0)) = 1 :=
    Classical.choose_spec (exists_piSingle_phi_eq_one K A φ)
  let g : A i0 →ₐ[K] F :=
    AlgHom.mk'
      { toFun := fun a => φ (Pi.single i0 a)
        map_one' := hi
        map_mul' := fun a b => by
          rw [← map_mul, ← Pi.single_mul]
        map_zero' := by simp
        map_add' := fun a b => by
          rw [← map_add, ← Pi.single_add] }
      (fun c a => by
        have hsingle : Pi.single i0 (c • a) = c • Pi.single i0 a := by
          ext j
          by_cases h : j = i0
          · subst h
            simp [Pi.smul_apply]
          · rw [Pi.single_eq_of_ne h, Pi.smul_apply, Pi.single_eq_of_ne h]
            simp
        change φ (Pi.single i0 (c • a)) = c • φ (Pi.single i0 a)
        rw [hsingle, map_smul])
  ⟨i0, g⟩

/-- The inverse direction: precompose a coordinate algebra map with the
projection (evaluation) at that coordinate. -/
noncomputable def algHomPiInverse (s : Σ i, A i →ₐ[K] F) :
    (Π i, A i) →ₐ[K] F :=
  s.2.comp (Pi.evalAlgHom K A s.1)

/-- Factorization lemma: if phi (Pi.single i0 1) = 1, then phi is determined by
its value on the i0-th coordinate. -/
theorem phi_eq_phi_piSingle (φ : (Π i, A i) →ₐ[K] F) {i0 : ι}
    (hi : φ (Pi.single i0 (1 : A i0)) = 1) (a : Π i, A i) :
    φ a = φ (Pi.single i0 (a i0)) := by
  calc
    φ a = φ (∑ i, Pi.single i (a i)) := by
      rw [Finset.univ_sum_single a]
    _ = ∑ i, φ (Pi.single i (a i)) := by rw [map_sum]
    _ = φ (Pi.single i0 (a i0)) := by
      rw [Finset.sum_eq_single i0]
      · intro j _ hji
        have hj0 : φ (Pi.single j (1 : A j)) = 0 := by
          rcases piSingle_phi_eq_zero_or_one K A φ j with h | h
          · exact h
          · exact absurd (piSingle_phi_eq_one_unique K A φ hi h)
              (fun heq => hji heq.symm)
        calc
          φ (Pi.single j (a j)) =
              φ (Pi.single j (1 : A j) * Pi.single j (a j)) := by
            rw [← Pi.single_mul]
            simp
          _ = φ (Pi.single j (1 : A j)) * φ (Pi.single j (a j)) := by
            rw [map_mul]
          _ = 0 := by rw [hj0, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i0) h

/-- One-sided inverse: the inverse map applied to the forward map recovers phi. -/
theorem algHomPiInverse_algHomPiForward (φ : (Π i, A i) →ₐ[K] F) :
    algHomPiInverse K A (algHomPiForward K A φ) = φ := by
  ext a
  dsimp only [algHomPiForward, algHomPiInverse]
  change φ (Pi.single (Classical.choose (exists_piSingle_phi_eq_one K A φ))
    (a (Classical.choose (exists_piSingle_phi_eq_one K A φ)))) = φ a
  exact (phi_eq_phi_piSingle K A φ
    (Classical.choose_spec (exists_piSingle_phi_eq_one K A φ)) a).symm

end PiFactorizationAssembly

section CoordinateKilling

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
variable {F : Type u} [Field F] [Algebra K F]

/-- If phi sends the i0-th idempotent to 1, it sends every other
idempotent to 0. -/
theorem phi_single_one_eq_zero_of_ne (φ : (Π i, A i) →ₐ[K] F) {i0 : ι}
    (hi : φ (Pi.single i0 (1 : A i0)) = 1) {j : ι} (hji : j ≠ i0) :
    φ (Pi.single j (1 : A j)) = 0 := by
  rcases piSingle_phi_eq_zero_or_one K A φ j with h | h
  · exact h
  · exact absurd (piSingle_phi_eq_one_unique K A φ hi h) (fun heq => hji heq.symm)

/-- If phi sends the i0-th idempotent to 1, it kills the whole j-th coordinate
for every j different from i0. -/
theorem phi_single_apply_eq_zero_of_ne (φ : (Π i, A i) →ₐ[K] F) {i0 : ι}
    (hi : φ (Pi.single i0 (1 : A i0)) = 1) {j : ι} (hji : j ≠ i0) (a : A j) :
    φ (Pi.single j a) = 0 := by
  have hj0 : φ (Pi.single j (1 : A j)) = 0 :=
    phi_single_one_eq_zero_of_ne K A φ hi hji
  calc
    φ (Pi.single j a) = φ (Pi.single j (1 : A j) * Pi.single j a) := by
      rw [← Pi.single_mul]
      simp
    _ = φ (Pi.single j (1 : A j)) * φ (Pi.single j a) := by rw [map_mul]
    _ = 0 := by rw [hj0, zero_mul]

end CoordinateKilling

/-! ## 2d. Two-sided product-to-Sigma equivalence -/

section PiSigmaEquivalence

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
variable {F : Type u} [Field F] [Algebra K F]

/-- Dependent single-function evaluation, by substitution on the index. -/
lemma pi_single_apply_cast {i0 i : ι} (hidx : i0 = i) (a : A i0) :
    (Pi.single i0 a : (j : ι) → A j) i = cast (congrArg A hidx) a := by
  subst hidx
  simp [Pi.single_eq_same]

/-- Cast application for algebra homomorphisms transported along an index equality. -/
lemma cast_algHom_apply {i0 i : ι} (hidx : i0 = i) (g' : A i0 →ₐ[K] F) (a : A i) :
    (cast (congrArg (fun j => A j →ₐ[K] F) hidx) g') a =
      g' (cast (congrArg A hidx.symm) a) := by
  cases hidx
  rfl

/-- Casting an element along an equality and back is the identity. -/
lemma cast_cast_symm {i0 i : ι} (hidx : i0 = i) (a : A i) :
    cast (congrArg A hidx) (cast (congrArg A hidx.symm) a) = a := by
  cases hidx
  rfl

/- The two-sided product-to-Sigma comparison is now actual: the right inverse
`algHomPiForward_algHomPiInverse` and the resulting `algHomPiToSigmaEquiv_symm_apply`
are proved below in `PiSigmaRightInverse`/`PiSigmaSymm`. -/

end PiSigmaEquivalence

/-! ## 2e. Cardinal/injection route to the product-to-Sigma equivalence -/

section PiSigmaCardinal
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type u) [∀ i, Field (A i)] [∀ i, Algebra K (A i)]
variable [∀ i, FiniteDimensional K (A i)]
variable {F : Type u} [Field F] [Algebra K F]

noncomputable instance sigmaAlgHomFintype : Fintype (Σ i, A i →ₐ[K] F) :=
  inferInstance

/-- The forward factorisation map is injective (its inverse is `algHomPiInverse`). -/
theorem algHomPiForward_injective :
    Function.Injective (algHomPiForward (K := K) (A := A) (F := F)) := by
  intro φ ψ h
  have h' := congrArg (algHomPiInverse (K := K) (A := A) (F := F)) h
  rwa [algHomPiInverse_algHomPiForward (K := K) (A := A) (F := F) φ,
    algHomPiInverse_algHomPiForward (K := K) (A := A) (F := F) ψ] at h'

/-- The inverse factorisation map is injective: two Sigma points with the same
composite map have the same index and the same coordinate map. -/
theorem algHomPiInverse_injective :
    Function.Injective (algHomPiInverse (K := K) (A := A) (F := F)) := by
  rintro ⟨i, g⟩ ⟨j, h⟩ heq
  have h1 := congrArg (fun φ : (Π i, A i) →ₐ[K] F => φ (Pi.single i (1 : A i))) heq
  have h1' : (1 : F) = h (((Pi.single i (1 : A i)) : (k : ι) → A k) j) := by
    simpa [algHomPiInverse, Pi.single_eq_same] using h1
  have hji : j = i := by
    by_contra hne
    have h0 : (Pi.single i (1 : A i) : (k : ι) → A k) j = 0 := by
      simp [Pi.single_apply, hne]
    rw [h0, map_zero] at h1'
    exact one_ne_zero h1'
  revert h
  subst hji
  intro h heq h1 h1'
  refine Sigma.ext_iff.mpr ⟨rfl, ?_⟩
  apply heq_of_eq
  apply AlgHom.ext
  intro a
  have h2 := congrArg (fun φ : (Π i, A i) →ₐ[K] F => φ (Pi.single j a)) heq
  simpa [algHomPiInverse, Pi.single_eq_same] using h2

/-- The two factorisation maps are inverse bijections by the cardinal argument. -/
theorem algHomPiForward_bijective :
    Function.Bijective (algHomPiForward (K := K) (A := A) (F := F)) := by
  letI : Fintype ((Π i, A i) →ₐ[K] F) :=
    Fintype.ofInjective (algHomPiForward (K := K) (A := A) (F := F))
      (algHomPiForward_injective (K := K) (A := A) (F := F))
  apply (Fintype.bijective_iff_injective_and_card (algHomPiForward (K := K) (A := A) (F := F))).mpr
  refine ⟨algHomPiForward_injective (K := K) (A := A) (F := F), ?_⟩
  apply Nat.le_antisymm
  · exact Fintype.card_le_of_injective (algHomPiForward (K := K) (A := A) (F := F))
      (algHomPiForward_injective (K := K) (A := A) (F := F))
  · exact Fintype.card_le_of_injective (algHomPiInverse (K := K) (A := A) (F := F))
      (algHomPiInverse_injective (K := K) (A := A) (F := F))

/-- **Product-to-Sigma equivalence** for a finite family of finite-dimensional
fields, via the cardinal/injection route (no dependent Sigma equality). -/
noncomputable def algHomPiToSigmaEquiv :
    ((Π i, A i) →ₐ[K] F) ≃ (Σ i, A i →ₐ[K] F) :=
  Equiv.ofBijective (algHomPiForward (K := K) (A := A) (F := F))
    (algHomPiForward_bijective (K := K) (A := A) (F := F))

end PiSigmaCardinal

/-! ## 2f. Restriction to fixed fields (step 4ii, actual restriction/kernel) -/

section GaloisRestriction

noncomputable def galoisGroupToAlgEquiv (σ : galoisGroup K) :
    SeparableClosure K ≃ₐ[K] SeparableClosure K :=
  show Gal(SeparableClosure K/K) from σ

variable (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K))

/-- Restriction of an absolute Galois automorphism to the fixed field of `H`. -/
noncomputable def galoisRestrictFixedField :
    galoisGroup K → (openSubgroupFixedField K H →ₐ[K] SeparableClosure K) :=
  fun σ => (galoisGroupToAlgEquiv K σ).toAlgHom.comp
    (IntermediateField.val (openSubgroupFixedField K H))

@[simp] theorem galoisRestrictFixedField_apply
    (σ : galoisGroup K) (x : openSubgroupFixedField K H) :
    galoisRestrictFixedField K H σ x = galoisGroupToAlgEquiv K σ x := rfl

/-- The restriction equals the inclusion iff the automorphism fixes the fixed field. -/
theorem galoisRestrictFixedField_eq_val_iff_fixes (σ : galoisGroup K) :
    galoisRestrictFixedField K H σ =
        IntermediateField.val (openSubgroupFixedField K H) ↔
      galoisGroupToAlgEquiv K σ ∈
        (openSubgroupFixedField K H).fixingSubgroup := by
  constructor
  · intro h
    rw [IntermediateField.mem_fixingSubgroup_iff
      (K := openSubgroupFixedField K H) (galoisGroupToAlgEquiv K σ)]
    intro x hx
    have hx' := congrArg (fun f : openSubgroupFixedField K H →ₐ[K] SeparableClosure K =>
      f ⟨x, hx⟩) h
    simpa using hx'
  · intro h
    apply AlgHom.ext
    intro x
    have := (IntermediateField.mem_fixingSubgroup_iff
      (K := openSubgroupFixedField K H) (galoisGroupToAlgEquiv K σ)).mp h x.1 x.2
    simpa using this

/-- The fixing subgroup of the fixed field of `H` is `H` itself (as a subgroup
of the absolute Galois group). -/
theorem openSubgroupFixedField_fixingSubgroup_eq :
    (openSubgroupFixedField K H).fixingSubgroup =
      (H.toSubgroup : Subgroup (galoisGroup K)) := by
  let c : ClosedSubgroup (galoisGroup K) :=
    { toSubgroup := (H.toSubgroup : Subgroup (galoisGroup K))
      isClosed' := H.isClosed }
  have hL := InfiniteGalois.fixingSubgroup_fixedField c
  simpa [c, openSubgroupFixedField] using hL

/-- Kernel of the restriction map: restriction equals the inclusion iff σ ∈ H. -/
theorem galoisRestrictFixedField_eq_val_iff_mem (σ : galoisGroup K) :
    galoisRestrictFixedField K H σ =
        (openSubgroupFixedField K H).val ↔ σ ∈ H.toSubgroup := by
  rw [galoisRestrictFixedField_eq_val_iff_fixes,
    openSubgroupFixedField_fixingSubgroup_eq]
  change (σ : Gal(SeparableClosure K/K)) ∈
      (H.toSubgroup : Subgroup (galoisGroup K)) ↔ σ ∈ H.toSubgroup
  rfl

@[simp] theorem galoisGroupToAlgEquiv_one :
    galoisGroupToAlgEquiv K (1 : galoisGroup K) = AlgEquiv.refl := rfl

@[simp] theorem galoisGroupToAlgEquiv_mul (σ τ : galoisGroup K) :
    galoisGroupToAlgEquiv K (σ * τ) =
      galoisGroupToAlgEquiv K σ * galoisGroupToAlgEquiv K τ := by
  ext x
  rfl

@[simp] theorem galoisGroupToAlgEquiv_inv (σ : galoisGroup K) :
    galoisGroupToAlgEquiv K σ⁻¹ = (galoisGroupToAlgEquiv K σ)⁻¹ := by
  ext x
  rfl

lemma algEquiv_mul_apply {e₁ e₂ : SeparableClosure K ≃ₐ[K] SeparableClosure K} (x) :
    (e₁ * e₂) x = e₁ (e₂ x) := rfl

def leftCosetSetoid : Setoid (galoisGroup K) where
  r σ τ := galoisGroupToAlgEquiv K (σ⁻¹ * τ) ∈
    (openSubgroupFixedField K H).fixingSubgroup
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro σ
      have h : σ⁻¹ * σ = (1 : galoisGroup K) := by group
      rw [h, galoisGroupToAlgEquiv_one]
      exact (openSubgroupFixedField K H).fixingSubgroup.one_mem
    · intro σ τ h
      have hτσ : τ⁻¹ * σ = (σ⁻¹ * τ)⁻¹ := by group
      rw [hτσ, galoisGroupToAlgEquiv_inv]
      exact Subgroup.inv_mem _ h
    · intro σ τ υ h1 h2
      have hmul : σ⁻¹ * υ = (σ⁻¹ * τ) * (τ⁻¹ * υ) := by group
      rw [hmul, galoisGroupToAlgEquiv_mul]
      exact Subgroup.mul_mem _ h1 h2

abbrev leftCosetQuotient : Type u :=
  Quotient (leftCosetSetoid K H)

theorem galoisRestrictFixedField_eq_of_rel {σ τ : galoisGroup K}
    (hrel : galoisGroupToAlgEquiv K (σ⁻¹ * τ) ∈
      (openSubgroupFixedField K H).fixingSubgroup) :
    galoisRestrictFixedField K H σ = galoisRestrictFixedField K H τ := by
  ext x
  simp only [galoisRestrictFixedField_apply]
  have hx : galoisGroupToAlgEquiv K (σ⁻¹ * τ) x = x :=
    (IntermediateField.mem_fixingSubgroup_iff
      (K := openSubgroupFixedField K H) (galoisGroupToAlgEquiv K (σ⁻¹ * τ))).mp
      hrel x.1 x.2
  have hτ : galoisGroupToAlgEquiv K τ =
      galoisGroupToAlgEquiv K σ * galoisGroupToAlgEquiv K (σ⁻¹ * τ) := by
    conv_lhs => rw [show τ = σ * (σ⁻¹ * τ) from by group]
    rw [galoisGroupToAlgEquiv_mul]
  rw [hτ, algEquiv_mul_apply, hx]

noncomputable def galoisRestrictQuotient :
    leftCosetQuotient K H →
      (openSubgroupFixedField K H →ₐ[K] SeparableClosure K) :=
  Quotient.lift (fun σ : galoisGroup K => galoisRestrictFixedField K H σ)
    (fun σ τ hrel => galoisRestrictFixedField_eq_of_rel K H hrel)

theorem galoisRestrictQuotient_injective :
    Function.Injective (galoisRestrictQuotient K H) := by
  intro q₁ q₂ h
  induction q₁ using Quotient.inductionOn with
  | h σ =>
    induction q₂ using Quotient.inductionOn with
    | h τ =>
      apply Quotient.sound
      apply (galoisRestrictFixedField_eq_val_iff_fixes K H (σ⁻¹ * τ)).mp
      ext x
      simp only [galoisRestrictFixedField_apply]
      have h_eq : galoisRestrictFixedField K H σ =
          galoisRestrictFixedField K H τ := by
        simpa [galoisRestrictQuotient] using h
      have hx := congrArg (fun f : openSubgroupFixedField K H →ₐ[K] SeparableClosure K =>
        f x) h_eq
      simp only [galoisRestrictFixedField_apply] at hx
      have hτ : galoisGroupToAlgEquiv K τ =
          galoisGroupToAlgEquiv K σ * galoisGroupToAlgEquiv K (σ⁻¹ * τ) := by
        conv_lhs => rw [show τ = σ * (σ⁻¹ * τ) from by group]
        rw [galoisGroupToAlgEquiv_mul]
      rw [hτ, algEquiv_mul_apply] at hx
      have hxinj := (galoisGroupToAlgEquiv K σ).injective hx
      simpa using hxinj.symm

/-- **Frozen exact card**: surjectivity of the coset restriction map, equivalently
extension of every K-embedding of L_H to an absolute Galois automorphism.  No
inhabitant is constructed. -/
structure GaloisCosetSurjectivityCard (K : Type u) [Field K]
    (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K)) where
  /-- Surjectivity of the actual coset restriction map. -/
  surjective : Function.Surjective (galoisRestrictQuotient K H)

/-- Conversion of a finite continuous G_K-set to the genuine category of finite
continuous G_K-sets. -/
noncomputable def FiniteContinuousGSet.toContinuousGaloisSet
    (X : FiniteContinuousGSet K) : FiniteContinuousGaloisSetCategory K :=
  ⟨X.toGSet, X.stabilizer_isOpen⟩

/-! ## 2g. Extension of embeddings to the separable closure (step 4ii surjectivity input) -/

section GaloisExtension

variable (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K))

/-- Every K-embedding of the fixed field `L_H` extends to a K-algebra
endomorphism of the separable closure. -/
theorem exists_algHom_separableClosure_extension
    (f : openSubgroupFixedField K H →ₐ[K] SeparableClosure K) :
    ∃ ψ : SeparableClosure K →ₐ[K] SeparableClosure K,
      AlgHom.restrictDomain (openSubgroupFixedField K H) ψ = f := by
  haveI : Algebra.IsAlgebraic K (SeparableClosure K) :=
    separableClosure.isAlgebraic K (AlgebraicClosure K)
  haveI : Algebra.IsAlgebraic (openSubgroupFixedField K H) (SeparableClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) (openSubgroupFixedField K H)
  haveI : Algebra.IsSeparable K (SeparableClosure K) :=
    separableClosure.isSeparable K (AlgebraicClosure K)
  haveI : Algebra.IsSeparable (openSubgroupFixedField K H) (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable (F := K) (L := openSubgroupFixedField K H) (E := SeparableClosure K)
  refine IntermediateField.exists_algHom_of_splits' (F := K)
    (E := SeparableClosure K) (K := SeparableClosure K)
    (L := openSubgroupFixedField K H) f ?_
  intro s
  refine ⟨(Algebra.IsAlgebraic.isIntegral (K := openSubgroupFixedField K H)).1 s, ?_⟩
  exact IsSepClosed.splits_codomain (f := f.toRingHom) (minpoly (openSubgroupFixedField K H) s)
    (Algebra.IsSeparable.isSeparable (openSubgroupFixedField K H) s)

/-- **Frozen exact card**: every injective K-algebra endomorphism of the
separable closure is bijective (equivalently, its image is the whole separable
closure).  No inhabitant is constructed. -/
structure SeparableClosureEndomorphismBijectiveCard (K : Type u) [Field K] where
  /-- Every K-endomorphism of the separable closure is bijective. -/
  bijective : ∀ ψ : SeparableClosure K →ₐ[K] SeparableClosure K,
    Function.Bijective ψ

theorem separableClosureEndomorphism_surjective
    (ψ : SeparableClosure K →ₐ[K] SeparableClosure K) :
    Function.Surjective ψ :=
  (AlgHom.normal_bijective (F := K) (E := SeparableClosure K)
    (K := SeparableClosure K) ψ).2

theorem separableClosureEndomorphism_bijective
    (ψ : SeparableClosure K →ₐ[K] SeparableClosure K) :
    Function.Bijective ψ :=
  AlgHom.normal_bijective (F := K) (E := SeparableClosure K)
    (K := SeparableClosure K) ψ

/-- The bijectivity card is now inhabited. -/
def separableClosureEndomorphismBijectiveCard :
    SeparableClosureEndomorphismBijectiveCard K where
  bijective := separableClosureEndomorphism_bijective K

noncomputable def galoisGroupOfAlgEquiv
    (e : SeparableClosure K ≃ₐ[K] SeparableClosure K) : galoisGroup K :=
  show Gal(SeparableClosure K/K) from e

/-- Every K-embedding of `L_H` comes from an absolute Galois automorphism. -/
theorem exists_galoisGroup_restrict_eq
    (f : openSubgroupFixedField K H →ₐ[K] SeparableClosure K) :
    ∃ σ : galoisGroup K, galoisRestrictFixedField K H σ = f := by
  obtain ⟨ψ, hψ⟩ := exists_algHom_separableClosure_extension K H f
  let e : SeparableClosure K ≃ₐ[K] SeparableClosure K :=
    AlgEquiv.ofBijective ψ (separableClosureEndomorphism_bijective K ψ)
  refine ⟨galoisGroupOfAlgEquiv K e, ?_⟩
  rw [← hψ]
  rfl

theorem galoisRestrictQuotient_surjective :
    Function.Surjective (galoisRestrictQuotient K H) := by
  intro f
  obtain ⟨σ, hσ⟩ := exists_galoisGroup_restrict_eq K H f
  refine ⟨Quotient.mk (leftCosetSetoid K H) σ, ?_⟩
  change galoisRestrictFixedField K H σ = f
  exact hσ

theorem galoisRestrictQuotient_bijective :
    Function.Bijective (galoisRestrictQuotient K H) :=
  ⟨galoisRestrictQuotient_injective K H, galoisRestrictQuotient_surjective K H⟩

noncomputable def galoisCosetAlgHomEquiv :
    leftCosetQuotient K H ≃
      (openSubgroupFixedField K H →ₐ[K] SeparableClosure K) :=
  Equiv.ofBijective (galoisRestrictQuotient K H) (galoisRestrictQuotient_bijective K H)

/-- The surjectivity card is now inhabited. -/
def galoisCosetSurjectivityCard : GaloisCosetSurjectivityCard K H where
  surjective := galoisRestrictQuotient_surjective K H

end GaloisExtension

end GaloisRestriction

/-! ## 3. Frozen exact remaining cards -/

/-- Frozen card: packaging the fixed field of an open subgroup as a finite etale
K-algebra.  No inhabitant is constructed. -/
structure FixedFieldFiniteEtaleCard (K : Type u) [Field K] where
  /-- The finite etale K-algebra attached to an open subgroup. -/
  fixedFieldFiniteEtale :
    OpenSubgroup (Iut.AbsoluteGaloisProfinite K) → CommAlgCat.FiniteEtale.{u} K

/-- The fixed-field finite etale card is now inhabited by the actual construction
of the fixed field as a finite etale K-algebra. -/
noncomputable def fixedFieldFiniteEtaleCard :
    FixedFieldFiniteEtaleCard K where
  fixedFieldFiniteEtale := openSubgroupFixedFieldFiniteEtale K

/-- Frozen card: the object map from finite continuous G_K-sets to finite etale
K-algebras, with a G_K-EQUIVARIANT fiber isomorphism in the action category
(not an isomorphism of underlying finite types), and the object-level roundtrip. -/
structure GSetToEtaleFiberCard (K : Type u) [Field K] where
  /-- The fixed-field finite etale card. -/
  fixedFieldCard : FixedFieldFiniteEtaleCard K
  /-- The object map from finite continuous G_K-sets to finite etale algebras. -/
  toFiniteEtale : FiniteContinuousGaloisSetCategory K → CommAlgCat.FiniteEtale.{u} K
  /-- The fiber of the resulting finite etale algebra is G_K-equivariantly the
  given finite continuous G_K-set. -/
  fiber_isomorphism : ∀ X : FiniteContinuousGaloisSetCategory K,
    Nonempty (finiteEtaleObjectToGSet K (toFiniteEtale X) ≅ X.obj)
  /-- Object-level roundtrip with the task-74 object map, G_K-equivariantly. -/
  roundtrip : ∀ X : FiniteContinuousGaloisSetCategory K,
    Nonempty (finiteEtaleObjectToGSet K (toFiniteEtale X) ≅ X.obj)

/-- Frozen card: naturality/functoriality and the unit/counit of the induced
equivalence, on top of the fiber/roundtrip card, using the continuous category
and the equivariant `GaloisNaturalityCard` of GaloisCorrespondence. -/
structure GSetToEtaleNaturalityCard (K : Type u) [Field K] where
  /-- The object-level fiber/roundtrip card. -/
  fiberCard : GSetToEtaleFiberCard K
  /-- Equivariant naturality with the continuous target category. -/
  map_compatibility : GaloisNaturalityCard K
  /-- The full equivalence is the frozen field Galois correspondence card. -/
  equivalenceCard : FieldGaloisCorrespondence K

/-! ## 4. Fiber decomposition of the orbit-product object (fiber step) -/

namespace FiniteContinuousGSet

/-- The fiber `Hom(A_X, Kbar)` of the orbit-product algebra splits as the Sigma
of the coset quotient spaces `G_K/H_q`, using the actual cardinal-route
product-to-Sigma equivalence and the actual coset equivalence of step 4ii. -/
noncomputable def fiberProductSigmaEquiv (X : FiniteContinuousGSet K) :
    (↥(gSetToFiniteEtaleObject X) →ₐ[K] SeparableClosure K) ≃
      (Σ q : X.orbitIndex, leftCosetQuotient K (X.orbitStabilizer q)) := by
  classical
  letI : ∀ q : X.orbitIndex, FiniteDimensional K
      ↥(openSubgroupFixedField K (X.orbitStabilizer q)) := fun q =>
    X.orbitFixedField_finiteDimensional q
  exact (algHomPiToSigmaEquiv K
      (fun q : X.orbitIndex => ↥(openSubgroupFixedField K (X.orbitStabilizer q)))
      (F := SeparableClosure K)).trans
    (Equiv.sigmaCongrRight (fun q => (galoisCosetAlgHomEquiv K (X.orbitStabilizer q)).symm))

end FiniteContinuousGSet

/-- **Frozen exact card**: the orbit decomposition identification of the finite
continuous G_K-set with the Sigma of its coset quotients, and its compatibility
with the action-category fiber isomorphisms.  No inhabitant is constructed. -/
structure FiberOrbitIdentificationCard (K : Type u) [Field K]
    (X : FiniteContinuousGSet K) where
  /-- Orbit decomposition of the underlying finite G_K-set. -/
  decomposition : X.toGSet.V ≃
    (Σ q : X.orbitIndex, leftCosetQuotient K (X.orbitStabilizer q))

/-- Bridge between the custom left-coset quotient and Mathlib's subgroup
quotient `G_K ⧸ H`. -/
noncomputable def leftCosetQuotientEquivQuotient
    (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K)) :
    leftCosetQuotient K H ≃ (galoisGroup K ⧸ H.toSubgroup) := by
  refine Quotient.congr (Equiv.refl _) ?_
  intro a b
  rw [leftCosetSetoid, QuotientGroup.leftRel_apply]
  exact (galoisRestrictFixedField_eq_val_iff_fixes K H (a⁻¹ * b)).symm.trans
    (galoisRestrictFixedField_eq_val_iff_mem K H (a⁻¹ * b))

/-- Orbit decomposition of the underlying finite continuous G_K-set into the
coset quotient spaces of the orbit stabilizers. -/
noncomputable def orbitDecomposition (X : FiniteContinuousGSet K) :
    X.toGSet.V ≃ (Σ q : X.orbitIndex, leftCosetQuotient K (X.orbitStabilizer q)) :=
  (MulAction.selfEquivSigmaOrbits (Iut.AbsoluteGaloisProfinite K) X.toGSet.V).trans
    (Equiv.sigmaCongrRight (fun q =>
      (MulAction.orbitEquivQuotientStabilizer (Iut.AbsoluteGaloisProfinite K)
        (Quotient.out q)).trans
        (leftCosetQuotientEquivQuotient K (X.orbitStabilizer q)).symm))

/-- The orbit-identification card is now inhabited. -/
noncomputable def fiberOrbitIdentificationCard (X : FiniteContinuousGSet K) :
    FiberOrbitIdentificationCard K X where
  decomposition := orbitDecomposition K X

section CosetAction

variable (X : FiniteContinuousGSet K)

instance sigmaCosetMulAction :
    MulAction (galoisGroup K)
      (Σ q : X.orbitIndex, leftCosetQuotient K (X.orbitStabilizer q)) where
  smul g p := ⟨p.1, Quotient.map (fun σ => g * σ) (by
    intro a b h
    have h' : (g * a)⁻¹ * (g * b) = a⁻¹ * b := by group
    change galoisGroupToAlgEquiv K ((g * a)⁻¹ * (g * b)) ∈
      (openSubgroupFixedField K (X.orbitStabilizer p.1)).fixingSubgroup
    rw [h']
    exact h) p.2⟩
  one_smul p := by
    obtain ⟨q, c⟩ := p
    refine Sigma.ext_iff.mpr ⟨rfl, ?_⟩
    apply heq_of_eq
    induction c using Quotient.inductionOn with
    | h σ =>
      apply Quotient.sound
      show galoisGroupToAlgEquiv K ((1 * σ)⁻¹ * σ) ∈
        (openSubgroupFixedField K (X.orbitStabilizer q)).fixingSubgroup
      simpa using (openSubgroupFixedField K (X.orbitStabilizer q)).fixingSubgroup.one_mem
  mul_smul g h p := by
    obtain ⟨q, c⟩ := p
    refine Sigma.ext_iff.mpr ⟨rfl, ?_⟩
    apply heq_of_eq
    induction c using Quotient.inductionOn with
    | h σ =>
      apply Quotient.sound
      change galoisGroupToAlgEquiv K (((g * h) * σ)⁻¹ * (g * (h * σ))) ∈
        (openSubgroupFixedField K (X.orbitStabilizer q)).fixingSubgroup
      have h1 : (((g * h) * σ)⁻¹ * (g * (h * σ))) = (1 : galoisGroup K) := by group
      rw [h1, galoisGroupToAlgEquiv_one]
      exact (openSubgroupFixedField K (X.orbitStabilizer q)).fixingSubgroup.one_mem

end CosetAction

section OrbitCanonicalMap

variable (X : FiniteContinuousGSet K)

instance leftCosetQuotientMulAction
    (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K)) :
    MulAction (galoisGroup K) (leftCosetQuotient K H) where
  smul g c := Quotient.map (fun σ => g * σ) (by
    intro a b h
    have h' : (g * a)⁻¹ * (g * b) = a⁻¹ * b := by group
    change galoisGroupToAlgEquiv K ((g * a)⁻¹ * (g * b)) ∈
      (openSubgroupFixedField K H).fixingSubgroup
    rw [h']
    exact h) c
  one_smul c := by
    induction c using Quotient.inductionOn with
    | h σ =>
      apply Quotient.sound
      show galoisGroupToAlgEquiv K ((1 * σ)⁻¹ * σ) ∈
        (openSubgroupFixedField K H).fixingSubgroup
      simpa using (openSubgroupFixedField K H).fixingSubgroup.one_mem
  mul_smul g h c := by
    induction c using Quotient.inductionOn with
    | h σ =>
      apply Quotient.sound
      change galoisGroupToAlgEquiv K (((g * h) * σ)⁻¹ * (g * (h * σ))) ∈
        (openSubgroupFixedField K H).fixingSubgroup
      have h1 : (((g * h) * σ)⁻¹ * (g * (h * σ))) = (1 : galoisGroup K) := by group
      rw [h1, galoisGroupToAlgEquiv_one]
      exact (openSubgroupFixedField K H).fixingSubgroup.one_mem

noncomputable def orbitCanonicalMap (q : X.orbitIndex) :
    leftCosetQuotient K (X.orbitStabilizer q) →
      MulAction.orbit (Iut.AbsoluteGaloisProfinite K) (Quotient.out q) :=
  Quotient.lift (fun σ => ⟨σ • Quotient.out q, ⟨σ, rfl⟩⟩) (by
    intro a b hrel
    apply Subtype.ext
    have hab : a⁻¹ * b ∈ (X.orbitStabilizer q).toSubgroup :=
      (galoisRestrictFixedField_eq_val_iff_mem K (X.orbitStabilizer q) (a⁻¹ * b)).mp
        ((galoisRestrictFixedField_eq_val_iff_fixes K (X.orbitStabilizer q) (a⁻¹ * b)).mpr hrel)
    have hfix : (a⁻¹ * b) • Quotient.out q = Quotient.out q := by
      change a⁻¹ * b ∈ MulAction.stabilizer (Iut.AbsoluteGaloisProfinite K)
        (Quotient.out q) at hab
      exact MulAction.mem_stabilizer_iff.mp hab
    have hb : b = a * (a⁻¹ * b) := by group
    calc a • Quotient.out q = a • ((a⁻¹ * b) • Quotient.out q) := by rw [hfix]
      _ = (a * (a⁻¹ * b)) • Quotient.out q := (mul_smul a (a⁻¹ * b) (Quotient.out q)).symm
      _ = b • Quotient.out q := by rw [← hb])

theorem orbitCanonicalMap_smul (q : X.orbitIndex) (g : galoisGroup K)
    (c : leftCosetQuotient K (X.orbitStabilizer q)) :
    orbitCanonicalMap K X q (g • c) = g • orbitCanonicalMap K X q c := by
  induction c using Quotient.inductionOn with
  | h σ =>
    apply Subtype.ext
    change (g * σ) • Quotient.out q = g • σ • Quotient.out q
    rw [mul_smul]

theorem orbitCanonicalMap_bijective (q : X.orbitIndex) :
    Function.Bijective (orbitCanonicalMap K X q) := by
  constructor
  · intro c d h
    induction c using Quotient.inductionOn with
    | h a =>
      induction d using Quotient.inductionOn with
      | h b =>
        have hout : a • Quotient.out q = b • Quotient.out q := congrArg Subtype.val h
        apply Quotient.sound
        apply (galoisRestrictFixedField_eq_val_iff_fixes K (X.orbitStabilizer q) (a⁻¹ * b)).mp
        apply (galoisRestrictFixedField_eq_val_iff_mem K (X.orbitStabilizer q) (a⁻¹ * b)).mpr
        change a⁻¹ * b ∈ MulAction.stabilizer (Iut.AbsoluteGaloisProfinite K) (Quotient.out q)
        rw [MulAction.mem_stabilizer_iff]
        calc (a⁻¹ * b) • Quotient.out q = a⁻¹ • (b • Quotient.out q) := mul_smul _ _ _
          _ = a⁻¹ • (a • Quotient.out q) := by rw [hout]
          _ = Quotient.out q := by simp
  · intro y
    obtain ⟨x, hx⟩ := y
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
    exact ⟨Quotient.mk (leftCosetSetoid K (X.orbitStabilizer q)) g, rfl⟩

end OrbitCanonicalMap

theorem existingDecompositionInverse_representative (X : FiniteContinuousGSet K)
    (q : X.orbitIndex) (σ : galoisGroup K) :
    (orbitDecomposition K X).symm
        ⟨q, Quotient.mk (leftCosetSetoid K (X.orbitStabilizer q)) σ⟩ =
      σ • Quotient.out q := rfl

theorem existingDecompositionInverse_equivariant (X : FiniteContinuousGSet K)
    (g : galoisGroup K)
    (s : Σ q : X.orbitIndex, leftCosetQuotient K (X.orbitStabilizer q)) :
    (orbitDecomposition K X).symm (g • s) =
      g • (orbitDecomposition K X).symm s := by
  obtain ⟨q, c⟩ := s
  induction c using Quotient.inductionOn with
  | h σ =>
    change (g * σ) • Quotient.out q = g • (σ • Quotient.out q)
    exact mul_smul g σ (Quotient.out q)

theorem existingDecomposition_equivariant (X : FiniteContinuousGSet K)
    (g : galoisGroup K) (x : X.toGSet.V) :
    orbitDecomposition K X (g • x) = g • orbitDecomposition K X x := by
  apply (orbitDecomposition K X).symm.injective
  rw [Equiv.symm_apply_apply, existingDecompositionInverse_equivariant,
    Equiv.symm_apply_apply]

theorem galoisRestrictFixedField_mul
    (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K))
    (g σ : galoisGroup K) :
    galoisRestrictFixedField K H (g * σ) =
      (galoisGroupToAlgEquiv K g).toAlgHom.comp
        (galoisRestrictFixedField K H σ) := by
  ext x
  simp [galoisRestrictFixedField_apply, galoisGroupToAlgEquiv_mul]

theorem galoisRestrictQuotient_smul
    (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K))
    (g : galoisGroup K) (c : leftCosetQuotient K H) :
    galoisRestrictQuotient K H (g • c) =
      (galoisGroupToAlgEquiv K g).toAlgHom.comp
        (galoisRestrictQuotient K H c) := by
  induction c using Quotient.inductionOn with
  | h σ =>
    change galoisRestrictFixedField K H (g * σ) =
      (galoisGroupToAlgEquiv K g).toAlgHom.comp
        (galoisRestrictFixedField K H σ)
    exact galoisRestrictFixedField_mul K H g σ

theorem galoisCosetAlgHomEquiv_smul
    (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K))
    (g : galoisGroup K) (c : leftCosetQuotient K H) :
    galoisCosetAlgHomEquiv K H (g • c) =
      (galoisGroupToAlgEquiv K g).toAlgHom.comp
        (galoisCosetAlgHomEquiv K H c) := by
  change galoisRestrictQuotient K H (g • c) =
    (galoisGroupToAlgEquiv K g).toAlgHom.comp (galoisRestrictQuotient K H c)
  exact galoisRestrictQuotient_smul K H g c

theorem galoisCosetAlgHomEquiv_symm_comp
    (H : OpenSubgroup (Iut.AbsoluteGaloisProfinite K))
    (g : galoisGroup K)
    (ψ : openSubgroupFixedField K H →ₐ[K] SeparableClosure K) :
    (galoisCosetAlgHomEquiv K H).symm
        ((galoisGroupToAlgEquiv K g).toAlgHom.comp ψ) =
      g • (galoisCosetAlgHomEquiv K H).symm ψ := by
  rw [Equiv.symm_apply_eq]
  rw [galoisCosetAlgHomEquiv_smul]
  rw [Equiv.apply_symm_apply]

/-! ## 2d-bis. Actual dependent-Sigma right inverse -/

section PiSigmaRightInverse

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (K : Type u) [Field K]
variable (A : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
variable {F : Type u} [Field F] [Algebra K F]

lemma algHomPiForward_fst (φ : (Π i, A i) →ₐ[K] F) :
    (algHomPiForward K A φ).1 =
      Classical.choose (exists_piSingle_phi_eq_one K A φ) := rfl

lemma algHomPiForward_snd_apply (φ : (Π i, A i) →ₐ[K] F)
    (a : A (algHomPiForward K A φ).1) :
    (algHomPiForward K A φ).2 a =
      φ (Pi.single (algHomPiForward K A φ).1 a) := rfl

theorem algHomPiForward_algHomPiInverse (s : Σ i, A i →ₐ[K] F) :
    algHomPiForward K A (algHomPiInverse K A s) = s := by
  obtain ⟨q, ψ⟩ := s
  set φ : (Π i, A i) →ₐ[K] F := algHomPiInverse K A ⟨q, ψ⟩ with hφ
  have hq : φ (Pi.single q (1 : A q)) = 1 := by
    simp [hφ, algHomPiInverse]
  have hfst : (algHomPiForward K A φ).1 = q := by
    rw [algHomPiForward_fst]
    exact piSingle_phi_eq_one_unique K A φ
      (Classical.choose_spec (exists_piSingle_phi_eq_one K A φ)) hq
  have hcast :
      cast (congrArg (fun j => A j →ₐ[K] F) hfst)
          (algHomPiForward K A φ).2 = ψ := by
    apply AlgHom.ext
    intro a
    rw [cast_algHom_apply (A := A) (K := K) hfst, algHomPiForward_snd_apply]
    change ψ ((Pi.single (algHomPiForward K A φ).1
      (cast (congrArg A hfst.symm) a)) q) = ψ a
    have hsingle :
        (Pi.single (algHomPiForward K A φ).1
          (cast (congrArg A hfst.symm) a)) q =
        cast (congrArg A hfst) (cast (congrArg A hfst.symm) a) :=
      pi_single_apply_cast A hfst _
    rw [hsingle, cast_cast_symm A hfst]
  exact Sigma.ext hfst (cast_eq_iff_heq.mp hcast)

end PiSigmaRightInverse

section PiSigmaSymm

variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable (K : Type u) [Field K]
variable (A : ι → Type u) [∀ i, Field (A i)] [∀ i, Algebra K (A i)]
variable [∀ i, FiniteDimensional K (A i)]
variable {F : Type u} [Field F] [Algebra K F]

theorem algHomPiToSigmaEquiv_symm_apply (s : Σ i, A i →ₐ[K] F) :
    (algHomPiToSigmaEquiv K A (F := F)).symm s =
      algHomPiInverse K A s := by
  apply (algHomPiToSigmaEquiv K A (F := F)).injective
  rw [Equiv.apply_symm_apply]
  change s = algHomPiForward K A (algHomPiInverse K A s)
  exact (algHomPiForward_algHomPiInverse (K := K) (A := A) (F := F) s).symm

end PiSigmaSymm

namespace FiniteContinuousGSet

variable (X : FiniteContinuousGSet K)

/-- The Pi-domain form of the fiber product-Sigma equivalence: the same map as
`fiberProductSigmaEquiv`, but with the product Pi type as domain so the
`FiniteDimensional`/`CommRing` instances match syntactically. -/
noncomputable def fiberProductSigmaEquivPi :
    ((Π q : X.orbitIndex, ↥(openSubgroupFixedField K (X.orbitStabilizer q))) →ₐ[K]
      SeparableClosure K) ≃
      (Σ q : X.orbitIndex, leftCosetQuotient K (X.orbitStabilizer q)) := by
  classical
  letI : ∀ q : X.orbitIndex, FiniteDimensional K
      ↥(openSubgroupFixedField K (X.orbitStabilizer q)) := fun q =>
    openSubgroupFixedField_finiteDimensional K (X.orbitStabilizer q)
  exact (algHomPiToSigmaEquiv K
      (fun q : X.orbitIndex => ↥(openSubgroupFixedField K (X.orbitStabilizer q)))
      (F := SeparableClosure K)).trans
    (Equiv.sigmaCongrRight (fun q =>
      (galoisCosetAlgHomEquiv K (X.orbitStabilizer q)).symm))

theorem fiberProductSigmaEquivPi_symm_apply
    (s : Σ q : X.orbitIndex, leftCosetQuotient K (X.orbitStabilizer q)) :
    (fiberProductSigmaEquivPi K X).symm s =
      algHomPiInverse K
        (fun q : X.orbitIndex => ↥(openSubgroupFixedField K (X.orbitStabilizer q)))
        ⟨s.1, galoisCosetAlgHomEquiv K (X.orbitStabilizer s.1) s.2⟩ := by
  obtain ⟨q, c⟩ := s
  rw [Equiv.symm_apply_eq]
  classical
  letI : ∀ q : X.orbitIndex, FiniteDimensional K
      ↥(openSubgroupFixedField K (X.orbitStabilizer q)) := fun q =>
    openSubgroupFixedField_finiteDimensional K (X.orbitStabilizer q)
  change (⟨q, c⟩ : Σ q : X.orbitIndex, leftCosetQuotient K (X.orbitStabilizer q)) =
    (Equiv.sigmaCongrRight (fun q =>
      (galoisCosetAlgHomEquiv K (X.orbitStabilizer q)).symm))
      (algHomPiForward K
        (fun q : X.orbitIndex => ↥(openSubgroupFixedField K (X.orbitStabilizer q)))
        (algHomPiInverse K
          (fun q : X.orbitIndex => ↥(openSubgroupFixedField K (X.orbitStabilizer q)))
          ⟨q, galoisCosetAlgHomEquiv K (X.orbitStabilizer q) c⟩))
  rw [algHomPiForward_algHomPiInverse]
  change (⟨q, c⟩ : Σ q : X.orbitIndex, leftCosetQuotient K (X.orbitStabilizer q)) =
    ⟨q, (galoisCosetAlgHomEquiv K (X.orbitStabilizer q)).symm
      (galoisCosetAlgHomEquiv K (X.orbitStabilizer q) c)⟩
  rw [Equiv.symm_apply_apply]

theorem fiberProductSigmaEquivPi_symm_comp (g : galoisGroup K)
    (s : Σ q : X.orbitIndex, leftCosetQuotient K (X.orbitStabilizer q)) :
    (fiberProductSigmaEquivPi K X).symm (g • s) =
      (galoisGroupToAlgEquiv K g).toAlgHom.comp
        ((fiberProductSigmaEquivPi K X).symm s) := by
  obtain ⟨q, c⟩ := s
  rw [fiberProductSigmaEquivPi_symm_apply (K := K) (X := X),
    fiberProductSigmaEquivPi_symm_apply (K := K) (X := X)]
  change algHomPiInverse K
      (fun q : X.orbitIndex => ↥(openSubgroupFixedField K (X.orbitStabilizer q)))
      ⟨q, galoisCosetAlgHomEquiv K (X.orbitStabilizer q) (g • c)⟩ =
    (galoisGroupToAlgEquiv K g).toAlgHom.comp
      (algHomPiInverse K
        (fun q : X.orbitIndex => ↥(openSubgroupFixedField K (X.orbitStabilizer q)))
        ⟨q, galoisCosetAlgHomEquiv K (X.orbitStabilizer q) c⟩)
  rw [galoisCosetAlgHomEquiv_smul]
  change ((galoisGroupToAlgEquiv K g).toAlgHom.comp
      (galoisCosetAlgHomEquiv K (X.orbitStabilizer q) c)).comp
      (Pi.evalAlgHom K (fun q : X.orbitIndex => ↥(openSubgroupFixedField K (X.orbitStabilizer q))) q) =
    (galoisGroupToAlgEquiv K g).toAlgHom.comp
      ((galoisCosetAlgHomEquiv K (X.orbitStabilizer q) c).comp
        (Pi.evalAlgHom K (fun q : X.orbitIndex => ↥(openSubgroupFixedField K (X.orbitStabilizer q))) q))
  rw [AlgHom.comp_assoc]

theorem fiberProductSigmaEquivPi_comp (g : galoisGroup K)
    (φ : (Π q : X.orbitIndex, ↥(openSubgroupFixedField K (X.orbitStabilizer q))) →ₐ[K]
      SeparableClosure K) :
    fiberProductSigmaEquivPi K X ((galoisGroupToAlgEquiv K g).toAlgHom.comp φ) =
      g • fiberProductSigmaEquivPi K X φ := by
  have h := fiberProductSigmaEquivPi_symm_comp K X g (fiberProductSigmaEquivPi K X φ)
  rw [Equiv.symm_apply_apply] at h
  have h2 := congrArg (fiberProductSigmaEquivPi K X) h
  rw [Equiv.apply_symm_apply] at h2
  exact h2.symm

theorem fiberProductSigmaEquiv_eq_arrowCongr_trans :
    fiberProductSigmaEquiv K X =
      (AlgEquiv.arrowCongr (gSetToFiniteEtaleObjectAlgEquiv X)
        (AlgEquiv.refl (A₁ := SeparableClosure K))).trans
        (fiberProductSigmaEquivPi K X) := by
  apply Equiv.ext
  intro f
  rfl

theorem fiberProductSigmaEquiv_symm_comp (g : galoisGroup K)
    (s : Σ q : X.orbitIndex, leftCosetQuotient K (X.orbitStabilizer q)) :
    (fiberProductSigmaEquiv K X).symm (g • s) =
      (galoisGroupToAlgEquiv K g).toAlgHom.comp
        ((fiberProductSigmaEquiv K X).symm s) := by
  rw [fiberProductSigmaEquiv_eq_arrowCongr_trans (K := K) (X := X)]
  rw [Equiv.symm_trans_apply]
  rw [fiberProductSigmaEquivPi_symm_comp]
  change ((galoisGroupToAlgEquiv K g).toAlgHom.comp
      ((fiberProductSigmaEquivPi K X).symm s)).comp
      (gSetToFiniteEtaleObjectAlgEquiv X).toAlgHom =
    (galoisGroupToAlgEquiv K g).toAlgHom.comp
      (((fiberProductSigmaEquivPi K X).symm s).comp
        (gSetToFiniteEtaleObjectAlgEquiv X).toAlgHom)
  rw [AlgHom.comp_assoc]

theorem fiberProductSigmaEquiv_comp (g : galoisGroup K)
    (φ : ↥(gSetToFiniteEtaleObject X) →ₐ[K] SeparableClosure K) :
    fiberProductSigmaEquiv K X ((galoisGroupToAlgEquiv K g).toAlgHom.comp φ) =
      g • fiberProductSigmaEquiv K X φ := by
  apply (fiberProductSigmaEquiv K X).symm.injective
  rw [Equiv.symm_apply_apply, fiberProductSigmaEquiv_symm_comp,
    Equiv.symm_apply_apply]

noncomputable def fiberActionEquiv (X : FiniteContinuousGSet K) :
    (↥(gSetToFiniteEtaleObject X) →ₐ[K] SeparableClosure K) ≃
      ↥(X.toGSet.V) :=
  (fiberProductSigmaEquiv K X).trans (orbitDecomposition K X).symm

theorem fiberActionEquiv_comp (X : FiniteContinuousGSet K) (g : galoisGroup K)
    (φ : ↥(gSetToFiniteEtaleObject X) →ₐ[K] SeparableClosure K) :
    fiberActionEquiv K X ((galoisGroupToAlgEquiv K g).toAlgHom.comp φ) =
      (X.toGSet.ρ g).hom (fiberActionEquiv K X φ) := by
  rw [fiberActionEquiv, Equiv.trans_apply, fiberProductSigmaEquiv_comp K X g φ,
    existingDecompositionInverse_equivariant]
  rfl

noncomputable def fiberActionIsoOfEquiv (X : FiniteContinuousGSet K)
    (e : (↥(gSetToFiniteEtaleObject X) →ₐ[K] SeparableClosure K) ≃ ↥(X.toGSet.V))
    (he : ∀ (g : galoisGroup K)
      (φ : ↥(gSetToFiniteEtaleObject X) →ₐ[K] SeparableClosure K),
      e ((galoisGroupToAlgEquiv K g).toAlgHom.comp φ) =
        (X.toGSet.ρ g).hom (e φ)) :
    finiteEtaleObjectToGSet K (gSetToFiniteEtaleObject X) ≅ X.toGSet :=
  Action.mkIso (FintypeCat.equivEquivIso e) (by
    intro g
    ext φ
    change e ((galoisGroupToAlgEquiv K g).toAlgHom.comp φ) =
      (X.toGSet.ρ g).hom (e φ)
    exact he g φ)

noncomputable def fiberActionIso (X : FiniteContinuousGSet K) :
    finiteEtaleObjectToGSet K (gSetToFiniteEtaleObject X) ≅ X.toGSet :=
  fiberActionIsoOfEquiv K X (fiberActionEquiv K X) (fiberActionEquiv_comp K X)

noncomputable def ofContinuousGaloisSet
    (Y : FiniteContinuousGaloisSetCategory K) : FiniteContinuousGSet K where
  toGSet := Y.obj
  stabilizer_isOpen := Y.property

@[simp] theorem ofContinuousGaloisSet_toGSet (Y : FiniteContinuousGaloisSetCategory K) :
    (ofContinuousGaloisSet (K := K) Y).toGSet = Y.obj := rfl


noncomputable def gSetToEtaleFiberCard : GSetToEtaleFiberCard K where
  fixedFieldCard := fixedFieldFiniteEtaleCard K
  toFiniteEtale Y :=
    gSetToFiniteEtaleObject (ofContinuousGaloisSet (K := K) Y)
  fiber_isomorphism Y :=
    ⟨fiberActionIso K (ofContinuousGaloisSet (K := K) Y)⟩
  roundtrip Y :=
    ⟨fiberActionIso K (ofContinuousGaloisSet (K := K) Y)⟩

end FiniteContinuousGSet

/-! ## 6. Assembly hooks for the final naturality card

These are packaging definitions (no new mathematics): they turn an already
supplied continuous-category equivalence plus its objectwise equivariant fiber
compatibility into `GaloisNaturalityCard`, and combine it with the actual
`gSetToEtaleFiberCard` and a supplied `FieldGaloisCorrespondence` into
`GSetToEtaleNaturalityCard`.  They do NOT inhabit the missing equivalence. -/

noncomputable def galoisNaturalityCardOfEquivalence
    (E : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌ FiniteContinuousGaloisSetCategory K)
    (hfib : ∀ A : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ,
      Nonempty (((E.functor.obj A).obj) ≅ finiteEtaleObjectToGSet K A.unop)) :
    GaloisNaturalityCard K where
  equivalence := E
  fiber_compatibility := hfib

noncomputable def gSetToEtaleNaturalityCardOfFieldCorrespondence
    (F : FieldGaloisCorrespondence K)
    (hfib : ∀ A : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ,
      Nonempty (((F.equivalence.functor.obj A).obj) ≅
        finiteEtaleObjectToGSet K A.unop)) :
    GSetToEtaleNaturalityCard K where
  fiberCard := FiniteContinuousGSet.gSetToEtaleFiberCard K
  map_compatibility := galoisNaturalityCardOfEquivalence K F.equivalence hfib
  equivalenceCard := F

noncomputable def fieldGaloisCorrespondenceOfEquivalence
    (E : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌ FiniteContinuousGaloisSetCategory K) :
    FieldGaloisCorrespondence K where
  equivalence := E
  specEssentialSurjectivity :=
    LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecEssentialSurjectivity.fieldGaloisCorrespondence_specEssentialSurjectivity K

end LeanFormal.IUT.IUTII.Frobenioid.Example36.GSetToEtaleAlgebra
