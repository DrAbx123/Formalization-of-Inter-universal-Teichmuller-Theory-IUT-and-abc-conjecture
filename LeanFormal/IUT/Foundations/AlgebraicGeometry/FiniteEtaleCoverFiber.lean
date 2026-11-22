import LeanFormal.IUT.IUTII.Frobenioid.Example36SpecCoverEquivalenceFinal

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry

universe u

open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {S : Scheme.{u}}

noncomputable def geometricFiberFunctor (Omega : Type u) [Field Omega] [IsSepClosed Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ S) [Limits.HasPullbacksAlong x] :
    FiniteEtaleCover S ⥤ FintypeCat.{u} :=
  FiniteEtaleCover.pullback x
    ⋙ (SpecCoverEquivalenceFinal.specCoverEquivalence Omega).inverse
    ⋙ EtaleCoverFoundations.FieldFiniteEtaleCategory.fiber Omega Omega

noncomputable abbrev geometricFiber (Omega : Type u) [Field Omega] [IsSepClosed Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ S) [Limits.HasPullbacksAlong x]
    (X : FiniteEtaleCover S) : FintypeCat.{u} :=
  (geometricFiberFunctor Omega x).obj X


theorem geometricFiberFunctor_map_id (Omega : Type u) [Field Omega] [IsSepClosed Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ S) [Limits.HasPullbacksAlong x]
    (X : FiniteEtaleCover S) :
    (geometricFiberFunctor Omega x).map (𝟙 X) =
      𝟙 ((geometricFiberFunctor Omega x).obj X) :=
  (geometricFiberFunctor Omega x).map_id X

theorem geometricFiberFunctor_map_comp (Omega : Type u) [Field Omega] [IsSepClosed Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ S) [Limits.HasPullbacksAlong x]
    {X Y Z : FiniteEtaleCover S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (geometricFiberFunctor Omega x).map (f ≫ g) =
      (geometricFiberFunctor Omega x).map f ≫ (geometricFiberFunctor Omega x).map g :=
  (geometricFiberFunctor Omega x).map_comp f g

end LeanFormal.IUT.Foundations.AlgebraicGeometry