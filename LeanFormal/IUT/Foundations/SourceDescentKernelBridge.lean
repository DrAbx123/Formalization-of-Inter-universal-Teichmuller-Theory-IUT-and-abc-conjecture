import Iut.Foundations.SourceKernelOrbit
import Iut.Foundations.SourceNestedNormalQuotientSystem
import Iut.Foundations.SourceProfiniteCosetSystem
import Iut.Foundations.SourceTemperoid
import Iut.Foundations.SourceTemperoidQuotient
import Iut.Foundations.SourceTemperoidOrbitDecomposition
import Iut.Foundations.SourceTemperoidAssociatedQuotient
import Iut.Foundations.SourceTemperoidComponentFamily
import Iut.Foundations.SourceTemperoidRestrictionComponentFamily

/-!
# Umbrella bridge to the Iut kernel-orbit and temperoid descent stack

Single import surface for the nine `Iut.Foundations` modules selected as
package P1 of the source-absorption evaluation (see
`logs/coordination/iut-foundations-inventory-20261016.md`, section N):

* kernel-orbit descent: `SourceKernelOrbit`, `SourceNestedNormalQuotientSystem`,
  `SourceProfiniteCosetSystem`;
* countable temperoids: `SourceTemperoid`, `SourceTemperoidQuotient`,
  `SourceTemperoidOrbitDecomposition`, `SourceTemperoidAssociatedQuotient`,
  `SourceTemperoidComponentFamily`, `SourceTemperoidRestrictionComponentFamily`.

Intended consumers are the Theorem 3.11 indeterminacy layers (Ind1) / (Ind2)
and their quotient/orbit transport kernels: the kernel-orbit carriers provide
the descent through `ker(q)`-orbits, and the associated-quotient and
orbit-decomposition constructions provide the link compatibility that does
not identify distinct representatives.

The declarations below are LF-namespaced `abbrev` aliases for the carrier-level
interface; the theorems keep their original `Iut.` names and are reachable
through this module's imports. This module adds no new mathematical content.
The audit obligations `IUT-III.Ind1` / `IUT-III.Ind2` remain pending until the
source-facing carriers are instantiated; this bridge alone does not discharge
them.
-/

namespace LeanFormal.IUT

namespace SourceDescentKernelBridge

universe u

abbrev KernelOrbitFiber {Pi G : Type u} [Group Pi] [TopologicalSpace Pi]
    [Group G] [TopologicalSpace G] (q : Pi →ₜ* G) (A : Type u) [MulAction Pi A] :=
  Iut.SourceKernelOrbit.Fiber q A

noncomputable abbrev KernelOrbitTargetAction {Pi G : Type u} [Group Pi] [TopologicalSpace Pi]
    [Group G] [TopologicalSpace G] (q : Pi →ₜ* G)
    (surjective : Function.Surjective q) (A : Type u) [MulAction Pi A] :
    MulAction G (Iut.SourceKernelOrbit.Fiber q A) :=
  Iut.SourceKernelOrbit.targetAction q surjective A

abbrev TemperoidAction (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :=
  Iut.SourceTemperoidAction G

abbrev ConnectedTemperoid (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :=
  Iut.SourceConnectedTemperoid G

abbrev TemperoidKernelQuotientFiber {Pi G : Type u} [Group Pi]
    [TopologicalSpace Pi] [IsTopologicalGroup Pi] [Group G] [TopologicalSpace G]
    (q : Pi →ₜ* G) (X : Iut.SourceTemperoidAction Pi) :=
  Iut.SourceTemperoidKernelQuotient.Fiber q X

noncomputable abbrev TemperoidKernelQuotientFunctor {Pi G : Type u} [Group Pi]
    [TopologicalSpace Pi] [IsTopologicalGroup Pi] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (q : Pi →ₜ* G) (surjective : Function.Surjective q)
    (openMap : IsOpenMap q) :
    CategoryTheory.Functor (Iut.SourceTemperoidAction Pi)
      (Iut.SourceTemperoidAction G) :=
  Iut.SourceTemperoidKernelQuotient.functor q surjective openMap

abbrev AssociatedQuotientCarrier {Local Deck : Type u} [Group Local]
    [TopologicalSpace Local] [IsTopologicalGroup Local] [Group Deck]
    (source : Iut.SourceTemperoidAction Local)
    (sourceDeckAction : Deck →* CategoryTheory.Aut source)
    (X : Type u) [MulAction Deck X] :=
  Iut.SourceTemperoidAssociatedQuotient.Carrier source sourceDeckAction X

end SourceDescentKernelBridge

end LeanFormal.IUT
