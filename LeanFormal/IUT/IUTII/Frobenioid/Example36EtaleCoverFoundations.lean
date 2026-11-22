import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Action.Continuous
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve
import Iut.Foundations.Orbicurve

/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
# Finite etale cover foundations (IUT I, Def. 3.1(b),(d): the D6 curve-Pi card)

This module builds actual foundations for the finite-etale cover category used by
the D6/orbicurve line, instead of restating a card:

1. For a scheme S, the category FiniteEtaleCover S of finite etale covers of S:
   the full subcategory of Over S on objects whose structure morphism is both
   etale (AlgebraicGeometry.Etale) and finite (AlgebraicGeometry.IsFinite), with
   its forgetful functor to Over S and to Scheme, and the base-change (pullback)
   functor along a morphism of base schemes.  Everything is proved from Mathlib's
   morphism-property API (Etale and IsFinite are stable under base change), not
   assumed.
2. For a field K, the field-side category (CommAlgCat.FiniteEtale K)ᵒᵖ of finite
   etale K-algebras (Mathlib), its fiber functor to FintypeCat for a geometric
   point, the separably closed equivalence with FintypeCat (Mathlib's
   CommAlgCat.FiniteEtale.equivOfIsSepClosed), and the object-level Spec
   comparison sending a finite etale K-algebra to a finite etale cover of Spec K
   (etale and finite proved from the algebra structure via Mathlib's
   HasRingHomProperty.Spec_iff and IsFinite.SpecMap_iff).
3. The absolute Galois group side: Iut.AbsoluteGaloisProfinite K is the profinite
   Galois group of K; Mathlib's Galois-category theory makes
   Action FintypeCat (AbsoluteGaloisProfinite K) a GaloisCategory with fiber
   functor Action.forget FintypeCat _ and IsFundamentalGroup for its automorphism
   group.  Mathlib's continuous-action refinement ContAction cannot be applied
   directly to FintypeCat (there is no HasForget₂ FintypeCat TopCat instance in
   Mathlib 4.32.2), which is recorded as a precise API stop in section 6.
4. The precise residual gap is frozen as FieldGaloisCorrespondence (an
   equivalence of categories (CommAlgCat.FiniteEtale K)ᵒᵖ ≌ finite G_K-sets
   compatible with fiber functors) together with the scheme-side essential
   surjectivity of the Spec comparison.  Mathlib proves the separably closed
   special case but does NOT prove the Galois correspondence for a general field,
   and does not prove that every finite etale cover of Spec K is the Spec of a
   finite etale K-algebra (affineness/essential surjectivity).

Boundary: no curve Pi_1, no fake Galois category, no card-only substitute.  The
missing equivalences are isolated as named structures and are not asserted.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

universe u

/-! ## 1. Finite etale covers of a scheme -/

/-- A structure morphism f : X ⟶ S is a finite etale cover when it is both etale
and finite. -/
def IsFiniteEtaleHom {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Etale f ∧ IsFinite f

/-- The category of finite etale covers of a scheme S: the full subcategory of
Over S on finite etale structure morphisms. -/
abbrev FiniteEtaleCover (S : Scheme.{u}) : Type (u + 1) :=
  (ObjectProperty.FullSubcategory fun X : Over S => IsFiniteEtaleHom X.hom)

namespace FiniteEtaleCover

variable {S T : Scheme.{u}}

/-- The underlying scheme-over-S object of a finite etale cover. -/
def toOver (X : FiniteEtaleCover S) : Over S := X.obj

/-- The underlying scheme of a finite etale cover. -/
def carrier (X : FiniteEtaleCover S) : Scheme.{u} := X.obj.left

/-- The structure morphism of a finite etale cover. -/
def structureMap (X : FiniteEtaleCover S) : carrier X ⟶ S := X.obj.hom

/-- The structure morphism of a finite etale cover is etale. -/
theorem etale_structureMap (X : FiniteEtaleCover S) : Etale (structureMap X) :=
  X.property.1

/-- The structure morphism of a finite etale cover is finite. -/
theorem finite_structureMap (X : FiniteEtaleCover S) : IsFinite (structureMap X) :=
  X.property.2

/-- The forgetful functor from finite etale covers to schemes over S. -/
def forgetOver (S : Scheme.{u}) : FiniteEtaleCover S ⥤ Over S :=
  ObjectProperty.ι (fun X : Over S => IsFiniteEtaleHom X.hom)

/-- The forgetful functor from finite etale covers to schemes. -/
def forget (S : Scheme.{u}) : FiniteEtaleCover S ⥤ Scheme.{u} :=
  forgetOver S ⋙ Over.forget S

/-- A finite etale cover built from a structure morphism with the two property
proofs. -/
def mk {X : Scheme.{u}} (f : X ⟶ S) (het : Etale f) (hfin : IsFinite f) :
    FiniteEtaleCover S :=
  ⟨Over.mk f, ⟨het, hfin⟩⟩

@[simp] theorem mk_carrier {X : Scheme.{u}} (f : X ⟶ S) (het : Etale f)
    (hfin : IsFinite f) : carrier (mk (S := S) f het hfin) = X := rfl

/-- Base change of a finite etale cover morphism is again finite etale: this is
Mathlib's stability of Etale and IsFinite under base change. -/
theorem finiteEtale_pullback {S T : Scheme.{u}} (g : T ⟶ S) {X : Scheme.{u}}
    {f : X ⟶ S} (het : Etale f) (hfin : IsFinite f) :
    Etale (Limits.pullback.snd f g) ∧ IsFinite (Limits.pullback.snd f g) := by
  haveI := het
  haveI := hfin
  exact ⟨inferInstance, inferInstance⟩

/-- Base change (pullback) of finite etale covers along g : T ⟶ S.  The base
change functor acts on the underlying Over objects by Over.pullback g; the cover
property is preserved by finiteEtale_pullback. -/
def pullback (g : T ⟶ S) [Limits.HasPullbacksAlong g] :
    FiniteEtaleCover S ⥤ FiniteEtaleCover T :=
  ObjectProperty.lift
    (fun X : Over T => IsFiniteEtaleHom X.hom)
    (forgetOver S ⋙ Over.pullback g)
    (by
      intro X
      constructor
      · change Etale ((Over.pullback g).obj X.obj).hom
        rw [show ((Over.pullback g).obj X.obj).hom =
          Limits.pullback.snd X.obj.hom g from
          Over.pullback_obj_hom (f := g) (g := X.obj)]
        exact (finiteEtale_pullback g X.property.1 X.property.2).1
      · change IsFinite ((Over.pullback g).obj X.obj).hom
        rw [show ((Over.pullback g).obj X.obj).hom =
          Limits.pullback.snd X.obj.hom g from
          Over.pullback_obj_hom (f := g) (g := X.obj)]
        exact (finiteEtale_pullback g X.property.1 X.property.2).2)

/-- The pullback of a cover along g has structure morphism
pullback.snd X.structureMap g. -/
theorem pullback_structureMap (g : T ⟶ S) [Limits.HasPullbacksAlong g]
    (X : FiniteEtaleCover S) :
    structureMap ((pullback g).obj X) =
      Limits.pullback.snd (structureMap X) g := by
  exact Over.pullback_obj_hom (f := g) (g := X.obj)

/-- The forgetful functor to schemes over S is faithful. -/
theorem forgetOver_faithful (S : Scheme.{u}) : (forgetOver S).Faithful :=
  (ObjectProperty.fullyFaithfulι
    (fun X : Over S => IsFiniteEtaleHom X.hom)).faithful

end FiniteEtaleCover

/-! ## 2. The field case: finite etale K-algebras -/

/-- The field-side finite etale cover category: the opposite of the category of
finite etale K-algebras.  This is the category whose objects are the finite etale
K-algebras and whose morphisms are reversed algebra homomorphisms, the same
variance as covers of Spec K. -/
abbrev FieldFiniteEtaleCategory (K : Type u) [Field K] :=
  (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ

namespace FieldFiniteEtaleCategory

variable (K : Type u) [Field K]

/-- A finite etale K-algebra is an object of the field-side category. -/
def ofAlg (A : Type u) [CommRing A] [Algebra K A] [Module.Finite K A]
    [Algebra.Etale K A] : FieldFiniteEtaleCategory K :=
  Opposite.op (CommAlgCat.FiniteEtale.of K A : CommAlgCat.FiniteEtale K)

/-- The fiber functor of the field-side category at a geometric point Omega,
sending a finite etale algebra to its set of K-algebra maps to Omega. -/
def fiber (Omega : Type u) [Field Omega] [Algebra K Omega] :
    FieldFiniteEtaleCategory K ⥤ FintypeCat :=
  CommAlgCat.FiniteEtale.fiber K Omega

/-- The fiber functor at the separable closure of K (the geometric point used by
the absolute Galois group). -/
def fiberSeparableClosure : FieldFiniteEtaleCategory K ⥤ FintypeCat :=
  fiber K (SeparableClosure K)

/-- The geometric-point fiber functor is the fiber at the separable closure. -/
theorem fiberSeparableClosure_eq :
    fiberSeparableClosure K = fiber K (SeparableClosure K) :=
  rfl

/-- For a separably closed field Omega, the finite etale Omega-algebras are
antiequivalent to finite sets (Mathlib).  This is the base case of the Galois
correspondence, proved rather than assumed. -/
def separablyClosedEquivalence (Omega : Type u) [Field Omega] [IsSepClosed Omega] :
    FieldFiniteEtaleCategory Omega ≌ FintypeCat :=
  CommAlgCat.FiniteEtale.equivOfIsSepClosed Omega

end FieldFiniteEtaleCategory

/-! ## 3. The object-level Spec comparison with covers of Spec K -/

variable (K : Type u) [Field K]

/-- The structure morphism Spec A ⟶ Spec K attached to a finite etale K-algebra
A. -/
def finiteEtaleAlgebraStructureMap (A : CommAlgCat.FiniteEtale K) :
    Spec (CommRingCat.of A.obj) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K A.obj))

/-- The structure morphism is etale: it is Spec of the etale algebra map. -/
theorem finiteEtaleAlgebraStructureMap_etale (A : CommAlgCat.FiniteEtale K) :
    Etale (finiteEtaleAlgebraStructureMap K A) := by
  rw [finiteEtaleAlgebraStructureMap]
  exact (AlgebraicGeometry.HasRingHomProperty.Spec_iff
    (P := @AlgebraicGeometry.Etale) (Q := @RingHom.Etale)).mpr
    (RingHom.etale_algebraMap.mpr A.property.right)

/-- The structure morphism is finite: it is Spec of a finite algebra map. -/
theorem finiteEtaleAlgebraStructureMap_finite (A : CommAlgCat.FiniteEtale K) :
    IsFinite (finiteEtaleAlgebraStructureMap K A) := by
  rw [finiteEtaleAlgebraStructureMap]
  exact (AlgebraicGeometry.IsFinite.SpecMap_iff
    (R := CommRingCat.of K) (S := CommRingCat.of A.obj)
    (f := CommRingCat.ofHom (algebraMap K A.obj))).mpr
    (RingHom.finite_algebraMap.mpr A.property.left)

/-- Every finite etale K-algebra gives a finite etale cover of Spec K. -/
def finiteEtaleAlgebraCover (A : CommAlgCat.FiniteEtale K) :
    FiniteEtaleCover (Spec (CommRingCat.of K)) :=
  FiniteEtaleCover.mk (finiteEtaleAlgebraStructureMap K A)
    (finiteEtaleAlgebraStructureMap_etale K A)
    (finiteEtaleAlgebraStructureMap_finite K A)

/-- The carrier of the cover attached to a finite etale K-algebra is Spec A. -/
@[simp] theorem finiteEtaleAlgebraCover_carrier (A : CommAlgCat.FiniteEtale K) :
    FiniteEtaleCover.carrier (finiteEtaleAlgebraCover K A) =
      Spec (CommRingCat.of A.obj) := rfl

/-- Object-level Spec comparison: the assignment on objects of the field-side
category to finite etale covers of Spec K is defined and proved finite etale. -/
def finiteEtaleAlgebraCoverObj :
    FieldFiniteEtaleCategory K → FiniteEtaleCover (Spec (CommRingCat.of K)) :=
  fun A => finiteEtaleAlgebraCover K A.unop

/-- Every object of the field-side category is realized as a finite etale cover
of Spec K (object level of the candidate Spec comparison functor). -/
theorem exists_cover_of_fieldObject (A : FieldFiniteEtaleCategory K) :
    ∃ C : FiniteEtaleCover (Spec (CommRingCat.of K)),
      FiniteEtaleCover.carrier C = Spec (CommRingCat.of A.unop.obj) :=
  ⟨finiteEtaleAlgebraCoverObj K A, rfl⟩

/-! ## 4. The absolute Galois group and finite G_K-sets -/

/-- The carrier of the absolute Galois group of K is a group. -/
theorem absoluteGaloisProfinite_group :
    Nonempty (Group ↥(Iut.AbsoluteGaloisProfinite K)) :=
  ⟨inferInstance⟩

/-- The carrier of the absolute Galois group of K is a topological group. -/
theorem absoluteGaloisProfinite_isTopologicalGroup :
    Nonempty (IsTopologicalGroup ↥(Iut.AbsoluteGaloisProfinite K)) :=
  ⟨inferInstance⟩

/-- The carrier of the absolute Galois group of K is compact. -/
theorem absoluteGaloisProfinite_compactSpace :
    Nonempty (CompactSpace ↥(Iut.AbsoluteGaloisProfinite K)) :=
  ⟨inferInstance⟩

/-- The tree's absolute Galois group is Mathlib's profinite Galois group of K at
the separable closure. -/
theorem absoluteGaloisProfinite_def :
    Iut.AbsoluteGaloisProfinite K =
      InfiniteGalois.profiniteGalGrp K (SeparableClosure K) :=
  rfl

/-- The category of finite G_K-sets: actions of the absolute Galois group on
finite sets.  Mathlib's Galois-category theory makes it a Galois category. -/
abbrev FiniteGaloisSetCategory (K : Type u) [Field K] : Type (u + 1) :=
  Action FintypeCat.{u} ↥(Iut.AbsoluteGaloisProfinite K)

instance finiteGaloisSetCategory_galoisCategory :
    GaloisCategory (FiniteGaloisSetCategory K) :=
  inferInstance

/-- The fiber functor of the finite G_K-set Galois category. -/
abbrev finiteGaloisSetFiber : FiniteGaloisSetCategory K ⥤ FintypeCat.{u} :=
  Action.forget FintypeCat.{u} ↥(Iut.AbsoluteGaloisProfinite K)

instance finiteGaloisSetFiber_fiberFunctor :
    PreGaloisCategory.FiberFunctor (finiteGaloisSetFiber K) :=
  inferInstance

/-- The automorphism group of the fiber functor is a fundamental group in the
sense of Galois categories (Mathlib). -/
instance finiteGaloisSetFiber_isFundamentalGroup :
    PreGaloisCategory.IsFundamentalGroup (finiteGaloisSetFiber K)
      (Aut (finiteGaloisSetFiber K)) :=
  inferInstance

/-- The continuity condition for a finite G_K-set: every point stabilizer is open
in G_K.  Since a finite set carries the discrete topology, this is exactly the
condition that the action of the profinite group G_K is continuous; it is NOT
automatic for an abstract finite action (a finite-index subgroup of a compact
group need not be open unless its action is continuous). -/
def IsContinuousFiniteGaloisSet (X : FiniteGaloisSetCategory K) : Prop :=
  ∀ x : ↥X.V,
    IsOpen
      (MulAction.stabilizer (Iut.AbsoluteGaloisProfinite K) x :
        Set (Iut.AbsoluteGaloisProfinite K))

/-- The genuine category of finite continuous G_K-sets: finite G_K-sets with open
point stabilizers, as a full subcategory of Action FintypeCat G_K.  Morphisms are
the G_K-equivariant maps inherited from the action category. -/
abbrev FiniteContinuousGaloisSetCategory (K : Type u) [Field K] : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (fun X : FiniteGaloisSetCategory K => IsContinuousFiniteGaloisSet (K := K) X)

/-- The forgetful functor from finite continuous G_K-sets to all finite G_K-sets. -/
def forgetFiniteContinuousGaloisSet :
    FiniteContinuousGaloisSetCategory K ⥤ FiniteGaloisSetCategory K :=
  ObjectProperty.ι _

/-! ## 5. The exact remaining gap: the field Galois correspondence -/

/-- The frozen residual gap of the field case: the Galois correspondence between
finite etale K-algebras and finite CONTINUOUS G_K-sets (open point stabilizers),
compatible with the fiber functors.  The target category is
FiniteContinuousGaloisSetCategory, not the category of all abstract finite
G_K-actions: continuity is a genuine condition on a finite action of a profinite
group.  No inhabitant is constructed here. -/
structure FieldGaloisCorrespondence (K : Type u) [Field K] where
  /-- The candidate equivalence between finite etale K-algebras and finite
  continuous G_K-sets. -/
  equivalence :
    (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌ FiniteContinuousGaloisSetCategory K
  /-- The scheme-side object comparison is essentially surjective: every finite
  etale cover of Spec K is isomorphic to Spec A for a finite etale K-algebra A. -/
  specEssentialSurjectivity :
    ∀ C : FiniteEtaleCover (Spec (CommRingCat.of K)),
      ∃ A : CommAlgCat.FiniteEtale K,
        Nonempty (C ≅ finiteEtaleAlgebraCover K A)

/-- A field Galois correspondence supplies the category equivalence between finite
etale K-algebras and finite CONTINUOUS G_K-sets (the main field of the frozen
structure). -/
theorem FieldGaloisCorrespondence.categoryEquivalence
    (G : FieldGaloisCorrespondence K) :
    Nonempty ((CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌ FiniteContinuousGaloisSetCategory K) :=
  ⟨G.equivalence⟩

/-- The field Galois correspondence implies the object-level comparison is
surjective onto finite etale covers of Spec K (one direction of the frozen
structure, made explicit). -/
theorem FieldGaloisCorrespondence.spec_essentially_surjective
    (G : FieldGaloisCorrespondence K)
    (C : FiniteEtaleCover (Spec (CommRingCat.of K))) :
    ∃ A : CommAlgCat.FiniteEtale K,
      Nonempty (C ≅ finiteEtaleAlgebraCover K A) :=
  G.specEssentialSurjectivity C

/-- The separably closed special case of the residual gap is available: finite
etale algebras over a separably closed field are equivalent to finite sets. -/
def separablyClosed_galoisCorrespondenceBase (Omega : Type u) [Field Omega]
    [IsSepClosed Omega] : FieldFiniteEtaleCategory Omega ≌ FintypeCat.{u} :=
  FieldFiniteEtaleCategory.separablyClosedEquivalence Omega

/-- For a separably closed field the finite etale cover category is a Galois
category via the equivalence with finite sets (Mathlib's base case). -/
theorem separablyClosed_finiteEtale_galoisCategory (Omega : Type u) [Field Omega]
    [IsSepClosed Omega] :
    Nonempty (FieldFiniteEtaleCategory Omega ≌ FintypeCat.{u}) :=
  ⟨separablyClosed_galoisCorrespondenceBase Omega⟩

/-! ## 6. Where the current API stops (frozen, exact)

The following are the only gaps preventing the D6 curve-Pi foundation from being
complete at the level of this file; each is a theorem-level statement that is NOT
proved by Mathlib 4.32.2 and is NOT asserted here:

* FieldGaloisCorrespondence K: the Galois correspondence
  (FiniteEtale K)ᵒᵖ ≌ finite G_K-sets (with fiber-functor compatibility).
  Available in Mathlib: the Galois category structure and fundamental-group API
  for Action FintypeCat G (used above), and the separably closed base case
  CommAlgCat.FiniteEtale.equivOfIsSepClosed.
* FieldGaloisCorrespondence.specEssentialSurjectivity: every finite etale cover of
  Spec K is affine and of the form Spec A with A finite etale over K.  The
  object-level map finiteEtaleAlgebraCover is constructed and proved finite etale
  here; essential surjectivity is not proved.
* full functoriality of the object-level Spec comparison
  finiteEtaleAlgebraCoverObj (the graph map is defined; the functor laws require
  the affine/finite-etale-cover comparison and are not installed).
* the continuous target: FiniteContinuousGaloisSetCategory is now defined as the
  full subcategory of finite G_K-sets with open point stabilizers, with
  G_K-equivariant maps inherited from the action category, and
  FieldGaloisCorrespondence targets it (not all abstract finite actions).  The
  remaining open point is the continuity of the forward fiber action
  Hom_K(A, SeparableClosure K); it is frozen as
  FiniteEtaleFiberContinuityCard in Example36GaloisCorrespondence.
* the D6 curve side: the passage from the finite etale cover category of a curve
  X_F to the geometric fundamental group requires a connectedness/geometric point
  story that is outside Mathlib's current etale homotopy API; only the
  scheme-theoretic cover category and the field-side comparison are built here.

No statement above is silently assumed: the gaps are isolated as structures and
explicitly marked as unproved.
-/

end LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations