import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.Galois.Infinite

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Foundation F1d: object-level Galois correspondence

This file extends the field-side Galois-category foundations of
`Example36EtaleCoverFoundations` with the object-level correspondence between
finite étale `K`-algebras and finite `G_K`-sets.

Proved (actual):
* the fiber object map `finiteEtaleObjectToGSet` sending a finite étale
  `K`-algebra `A` to the finite `G_K`-set of `K`-algebra maps `A → SeparableClosure K`,
  with its `FintypeCat` carrier and the actual `G_K`-action;
* the decomposition of every finite étale `K`-algebra as a finite product of
  finite separable field extensions (Mathlib's
  `Algebra.Etale.iff_exists_algEquiv_prod`, applied to the `Algebra.Etale`
  property of the finite étale algebra);
* openness of the fixing subgroup `Gal(Kbar/L) ≤ G_K` for a finite-dimensional
  intermediate field `L` (Mathlib infinite Galois theory), i.e. the finite
  separable extension side of the correspondence.

Frozen cards (no inhabitant, no fake equivalence):
* `FiniteEtaleFiberContinuityCard`: the forward fiber action
  Hom_K(A, SeparableClosure K) has open point stabilizers (the continuity
  condition needed for the target category);
* `FiniteGSetToFiniteEtaleObjectCard`: the converse object map from finite
  CONTINUOUS G_K-sets (open stabilizers) to finite etale K-algebras, with a
  G_K-EQUIVARIANT fiber isomorphism in the action category, not a mere
  isomorphism of underlying finite sets;
* `GaloisObjectCorrespondenceCard`: the two G_K-equivariant fiber roundtrips
  with the actual object maps;
* `GaloisNaturalityCard`: the exact unit/counit/equivalence and natural-fiber
  requirements, with the target the category of finite continuous G_K-sets.
The full category equivalence is frozen as `FieldGaloisCorrespondence` in
`Example36EtaleCoverFoundations` (also targeting the continuous category) and
is not asserted here.

Boundary: no curve Pi_1 and no theta/q-pilot claim; object level only, no fake
category equivalence.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace GaloisCorrespondence

open CategoryTheory
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

universe u

variable (K : Type u) [Field K]

/-! ## 1. The finite G_K-set associated to a finite étale K-algebra -/

/-- The fiber of a finite étale `K`-algebra: its finite set of `K`-algebra
maps to the separable closure. -/
abbrev finiteEtaleFiberSet (A : CommAlgCat.FiniteEtale.{u} K) : FintypeCat.{u} :=
  (FieldFiniteEtaleCategory.fiberSeparableClosure (K := K)).obj (Opposite.op A)

/-- The actual action of `G_K` on the fiber set, by postcomposition with the
automorphism of the separable closure. -/
instance finiteEtaleFiberSetMulAction (A : CommAlgCat.FiniteEtale.{u} K) :
    MulAction ↥(Iut.AbsoluteGaloisProfinite K)
      ↥(finiteEtaleFiberSet (K := K) A) where
  smul σ f :=
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K).toAlgHom.comp f
  one_smul f := rfl
  mul_smul σ τ f := rfl

/-- The object-level map from finite étale `K`-algebras to finite `G_K`-sets. -/
noncomputable def finiteEtaleObjectToGSet (A : CommAlgCat.FiniteEtale.{u} K) :
    FiniteGaloisSetCategory K :=
  Action.FintypeCat.ofMulAction ↥(Iut.AbsoluteGaloisProfinite K)
    (finiteEtaleFiberSet (K := K) A)

@[simp]
theorem finiteEtaleObjectToGSet_V (A : CommAlgCat.FiniteEtale.{u} K) :
    (finiteEtaleObjectToGSet K A).V = finiteEtaleFiberSet (K := K) A := rfl


/-! ## 2. Decomposition into finite products of finite separable fields -/

/-- **Object-level decomposition.**  Every finite étale `K`-algebra is a finite
product of finite separable field extensions (Mathlib's
`Algebra.Etale.iff_exists_algEquiv_prod`). -/
theorem finiteEtale_decomposition (A : CommAlgCat.FiniteEtale.{u} K) :
    ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u) (_ : ∀ i, Field (Ai i))
      (_ : ∀ i, Algebra K (Ai i)) (_ : A.obj ≃ₐ[K] Π i, Ai i),
        ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) := by
  exact (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := A.obj)).mp
    A.property.right

/-! ## 3. Finite separable extensions give open fixing subgroups -/

/-- For a finite-dimensional intermediate field `L` of a Galois extension `F/K`,
the fixing subgroup `Gal(F/L) ≤ Gal(F/K)` is open: the finite separable
extension side of the Galois correspondence. -/
theorem finiteIntermediateField_fixingSubgroup_isOpen
    {F : Type u} [Field F] [Algebra K F] [IsGalois K F]
    (L : IntermediateField K F) [FiniteDimensional K L] :
    IsOpen L.fixingSubgroup.carrier :=
  IntermediateField.fixingSubgroup_isOpen L

/-! ## 4. The frozen object-level correspondence cards (continuous target, equivariant) -/

/-- **Frozen card: continuity of the forward fiber action.**  The G_K-action on
Hom_K(A, SeparableClosure K) has open point stabilizers: the action factors
through the finite quotient defined by the finite-dimensional subextension
generated by the finitely many images of a finite set of algebra generators.
This is the continuity condition needed for the forward object map to land in
the category of finite continuous G_K-sets.  No inhabitant is constructed here. -/
structure FiniteEtaleFiberContinuityCard (K : Type u) [Field K] where
  /-- Every point stabilizer of the fiber action is open in G_K. -/
  stabilizer_isOpen : ∀ (A : CommAlgCat.FiniteEtale.{u} K)
      (f : ↥(finiteEtaleFiberSet (K := K) A)),
    IsOpen
      (MulAction.stabilizer (Iut.AbsoluteGaloisProfinite K) f :
        Set (Iut.AbsoluteGaloisProfinite K))

/-- **Frozen card: the converse object map on finite continuous G_K-sets.**  The
object map from finite continuous G_K-sets (open stabilizers) to finite etale
K-algebras, with a G_K-EQUIVARIANT fiber isomorphism: the isomorphism is an
isomorphism in the action category Action FintypeCat G_K, not merely an
isomorphism of the underlying finite sets.  No inhabitant is provided. -/
structure FiniteGSetToFiniteEtaleObjectCard (K : Type u) [Field K] where
  /-- The continuity card for the forward fiber action. -/
  continuity : FiniteEtaleFiberContinuityCard K
  /-- The object map from finite continuous G_K-sets to finite etale K-algebras. -/
  toFiniteEtale : FiniteContinuousGaloisSetCategory K → CommAlgCat.FiniteEtale K
  /-- The fiber of the resulting finite etale algebra is the given finite
  continuous G_K-set, G_K-EQUIVARIANTLY. -/
  fiber_isomorphism : ∀ X : FiniteContinuousGaloisSetCategory K,
    Nonempty (finiteEtaleObjectToGSet K (toFiniteEtale X) ≅ X.obj)

/-- **Frozen card: the object-level correspondence with G_K-equivariant
roundtrips.**  The roundtrips are isomorphisms in the action category (equivariant
maps), not isomorphisms of the underlying finite sets, and the target is the
genuine category of finite continuous G_K-sets. -/
structure GaloisObjectCorrespondenceCard (K : Type u) [Field K] where
  /-- The continuity card for the forward fiber action. -/
  continuity : FiniteEtaleFiberContinuityCard K
  /-- The object map from finite etale K-algebras to finite continuous G_K-sets. -/
  finiteEtaleToGSet : CommAlgCat.FiniteEtale K → FiniteContinuousGaloisSetCategory K
  /-- The forward object map forgets to the actual fiber G_K-set. -/
  finiteEtaleToGSet_obj : ∀ A : CommAlgCat.FiniteEtale K,
    (finiteEtaleToGSet A).obj = finiteEtaleObjectToGSet K A
  /-- The converse object map card. -/
  setToFiniteEtale : FiniteGSetToFiniteEtaleObjectCard K
  /-- Left fiber roundtrip on objects, G_K-equivariantly. -/
  fiber_roundtrip_left : ∀ A : CommAlgCat.FiniteEtale K,
    Nonempty (finiteEtaleObjectToGSet K
      (setToFiniteEtale.toFiniteEtale (finiteEtaleToGSet A)) ≅
        (finiteEtaleToGSet A).obj)
  /-- Right fiber roundtrip on objects, G_K-equivariantly. -/
  fiber_roundtrip_right : ∀ X : FiniteContinuousGaloisSetCategory K,
    Nonempty ((finiteEtaleToGSet (setToFiniteEtale.toFiniteEtale X)).obj ≅ X.obj)

/-- **Frozen card: exact unit/counit and natural-fiber requirements.**  The full
equivalence is with the category of finite continuous G_K-sets; the fiber
compatibility is a G_K-equivariant (action-category) isomorphism, not an
isomorphism of underlying finite sets.  The unit/counit are those of the
equivalence itself and are therefore not duplicated here; the fiber
compatibility is recorded objectwise against the actual forward fiber object map. -/
structure GaloisNaturalityCard (K : Type u) [Field K] where
  /-- The field category equivalence, with the continuous G_K-set target and its
  unit/counit data. -/
  equivalence : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌ FiniteContinuousGaloisSetCategory K
  /-- Objectwise G_K-equivariant natural-fiber compatibility: the fiber of the
  algebra attached by the equivalence to a finite etale K-algebra is
  G_K-equivariantly isomorphic to the actual fiber object map. -/
  fiber_compatibility : ∀ A : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ,
    Nonempty ((
      equivalence.functor.obj A).obj ≅ finiteEtaleObjectToGSet K A.unop)

end GaloisCorrespondence

end Example36
end LeanFormal.IUT.IUTII.Frobenioid