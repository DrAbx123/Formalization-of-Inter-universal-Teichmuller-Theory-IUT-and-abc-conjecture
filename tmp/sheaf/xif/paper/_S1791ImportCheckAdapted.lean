import tmp.sheaf.xif.paper.S1791MonoComplementActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open Iut
namespace LeanFormal.IUT.XiFPaper.S1791MonoComplementActual

variable {F : Type u} [Field F] {X : HyperbolicOrbicurve F}
local instance : Category.{u + 1, u + 1} (OrbicurveFiniteEtaleCover X) :=
  LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728CoverCategory11 (F := F) (X := X)

example [HasFiniteCoproducts (OrbicurveFiniteEtaleCover X)]
    {A B : OrbicurveFiniteEtaleCover X} (i : A ⟶ B) [Mono i]
    (h : S1791MonoComponentFactorizationAPI (F := F) (X := X) i) :
    LeanFormal.IUT.XiFPaper.S1763CoverQuotientsActual.S1763MonoComplementRequired F X i :=
  S1791MonoComplementRequired_of_clopenComponentFactorization (F := F) (X := X) i h

end LeanFormal.IUT.XiFPaper.S1791MonoComplementActual
