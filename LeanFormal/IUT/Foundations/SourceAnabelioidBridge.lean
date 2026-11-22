import Iut.Foundations.SourceAnabelioid
import Iut.Foundations.SourceAnabelioidComponents
import Iut.Foundations.SourceAnabelioidSlice
import Iut.Foundations.SourceConnectedAnabelioidSlice
import Iut.Foundations.SourceContinuousAnabelioid
import Iut.Foundations.GaloisImage
import Iut.Foundations.GaloisComplement
import Iut.Foundations.SourceCombinatorialUniversalCover
import Iut.Foundations.SourceConnectedCoveringCategory
import Iut.Foundations.SourceConnectedFiniteEtaleConverse

/-!
# Umbrella bridge to the Iut anabelioid and stack-top source stack

Single import surface for the ten `Iut.Foundations` modules selected as
package P2 of the source-absorption evaluation (see
`logs/coordination/iut-foundations-inventory-20261016.md`; file list
`tmp/iut-foundations-inventory-20261016/absorption-files.txt`):

* anabelioid stack (`Anabelioid7`): `SourceAnabelioid`,
  `SourceAnabelioidComponents`, `SourceAnabelioidSlice`,
  `SourceConnectedAnabelioidSlice`, `SourceContinuousAnabelioid`,
  `GaloisImage`, `GaloisComplement`;
* stack-top constructions (`StackTop3`): `SourceCombinatorialUniversalCover`,
  `SourceConnectedCoveringCategory`, `SourceConnectedFiniteEtaleConverse`.

Intended consumers are the source-facing gluing and anti-collapse layers of
the Theorem 3.11 indeterminacy file set: the anabelioid/slice carriers give
the `B(G)⁰`- and slice-level objects of the etale-picture, `GaloisImage` /
`GaloisComplement` give the image/complement comparison interfaces of the
pre-Galois category, and `SourceCombinatorialUniversalCover` /
`SourceConnectedCoveringCategory` / `SourceConnectedFiniteEtaleConverse` give
the combinatorial universal-cover and covering-category objects on top of
them.

The declarations below are LF-namespaced `abbrev` aliases for this
carrier-level interface; the theorems keep their original `Iut.` names and
are reachable through this module's imports. This module adds no new
mathematical content and discharges no audit obligation; the source-facing
obligations remain pending until the carriers are instantiated.
-/

namespace LeanFormal.IUT

namespace SourceAnabelioidBridge

universe u v w x

open CategoryTheory
open scoped FintypeCatDiscrete

abbrev PointedAnabelioidHom (source target : Iut.EtaleFundamentalGroup.{u}) :=
  Iut.SourcePointedAnabelioidHom source target

abbrev ActionComponent (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G) :=
  Iut.SourceActionComponent G S

abbrev ActionComponentFiber (G : ProfiniteGrp.{u}) (S : ContAction FintypeCat.{u} G)
    (component : Iut.SourceActionComponent G S) :=
  Iut.SourceActionComponentFiber G S component

abbrev SliceComponentCarrier {G : ProfiniteGrp.{u}} {S : ContAction FintypeCat.{u} G}
    (T : Over S) (component : Iut.SourceActionComponent G S) :=
  Iut.SourceSliceComponentCarrier T component

noncomputable abbrev SliceComponentFamily (G : ProfiniteGrp.{u})
    (S : ContAction FintypeCat.{u} G) :=
  Iut.SourceSliceComponentFamily G S

noncomputable abbrev SliceComponentFamilyCarrier {G : ProfiniteGrp.{u}}
    {S : ContAction FintypeCat.{u} G} (family : Iut.SourceSliceComponentFamily G S) :=
  Iut.SourceSliceComponentFamilyCarrier family

abbrev InducedSet (G : Type u) [Group G] (H : Subgroup G) (T : Type u) [MulAction H T] :=
  Iut.SourceInducedSet G H T

abbrev PaperInducedSet (G : Type u) [Group G] (H : Subgroup G) (T : Type u)
    [MulAction H T] :=
  Iut.SourcePaperInducedSet G H T

abbrev DependentSection {G : ProfiniteGrp.{u}} {S : ContAction FintypeCat.{u} G}
    (T : Over S) :=
  Iut.SourceDependentSection T

abbrev FiniteEtaleFunctorFactorization {C : Type u} [Category.{v} C] {D : Type w}
    [Category.{x} D] [Limits.HasBinaryProducts C] (pullback : C ⥤ D) :=
  Iut.SourceFiniteEtaleFunctorFactorization pullback

abbrev ConnectedFiniteEtaleHom (source target : Iut.EtaleFundamentalGroup.{u}) :=
  Iut.SourceConnectedFiniteEtaleHom source target

abbrev ContinuousActionFiber (G : Type u) [Group G] [TopologicalSpace G] :=
  Iut.continuousActionFiber G

abbrev GaloisImageFactorization {C : Type (u + 1)} [Category.{u, u + 1} C] {X Y : C}
    (f : X ⟶ Y) :=
  CategoryTheory.PreGaloisCategory.ImageFactorization f

noncomputable abbrev GaloisComplementComparisonIso {C : Type (u + 1)}
    [Category.{u, u + 1} C] [CategoryTheory.GaloisCategory C] (F : C ⥤ FintypeCat.{u})
    [CategoryTheory.PreGaloisCategory.FiberFunctor F] {X₁ Z₁ Y₁ X₂ Z₂ Y₂ : C}
    (i₁ : X₁ ⟶ Y₁) (u₁ : Z₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) (u₂ : Z₂ ⟶ Y₂)
    (h₁ : CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.BinaryCofan.mk i₁ u₁))
    (h₂ : CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.BinaryCofan.mk i₂ u₂))
    (x : X₁ ≅ X₂) (y : Y₁ ≅ Y₂) (square : i₁ ≫ y.hom = x.hom ≫ i₂) :=
  CategoryTheory.PreGaloisCategory.complementComparisonIso F i₁ u₁ i₂ u₂ h₁ h₂ x y square

abbrev UniversalVertex {Vertex : Type u} (graph : SimpleGraph Vertex) (root : Vertex) :=
  Iut.SourceCombinatorialUniversalCover.UniversalVertex graph root

abbrev DeckTransformation {Vertex : Type u} (graph : SimpleGraph Vertex) (root : Vertex) :=
  Iut.SourceCombinatorialUniversalCover.UniversalVertex.DeckTransformation graph root

abbrev ConnectedCoveringCategory (G : ProfiniteGrp.{u}) :=
  Iut.SourceConnectedCoveringCategory G

abbrev EquivalenceBasepointFiber {H : ProfiniteGrp.{u}} {D : Type (u + 1)}
    [Category.{u, u + 1} D] (equivalence : D ≌ ContAction FintypeCat.{u} H) :=
  Iut.SourceEquivalenceBasepoint.fiber equivalence

noncomputable abbrev ConnectedSourceEquivalence {G : ProfiniteGrp.{u}}
    {D : Type (u + 1)} [Category.{u, u + 1} D] [CategoryTheory.GaloisCategory D]
    {pullback : ContAction FintypeCat.{u} G ⥤ D}
    (factorization : Iut.SourceFiniteEtaleFunctorFactorization pullback) :=
  Iut.SourceFiniteEtaleFunctorFactorization.connectedSourceEquivalence factorization

end SourceAnabelioidBridge

end LeanFormal.IUT
