import tmp.sheaf.xif.paper.S2866SMapCompZActual
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2866EqProbe
open Iut
open LeanFormal.IUT.XiFPaper.S2858Z2MapCompActual
open LeanFormal.IUT.XiFPaper.S2865SMapFinActual
open LeanFormal.IUT.XiFPaper.S2866SMapCompZActual
variable {F : Type u} [Field F]
variable (X : Iut.HyperbolicOrbicurve F)
variable (inv : X.Hom X)
variable (invSq : Iut.HyperbolicOrbicurve.Hom.TwoIso
  (Iut.HyperbolicOrbicurve.Hom.comp inv inv) (Iut.HyperbolicOrbicurve.Hom.id X))
example : sMapCompZ X inv invSq 1 1 =
    (leftUnitorIso X (𝟙 X.stack.fiber)).symm := by
  rfl
example : sMapCompZ X inv invSq 1 (Multiplicative.ofAdd (1 : ZMod 2)) =
    (leftUnitorIso X (invM X inv)).symm := by
  rfl
end LeanFormal.IUT.XiFPaper.S2866EqProbe
end