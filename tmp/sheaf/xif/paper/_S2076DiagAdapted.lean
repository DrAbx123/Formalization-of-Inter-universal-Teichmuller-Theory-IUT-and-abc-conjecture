import tmp.sheaf.xif.paper._S2076P1
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
namespace Test
universe u v w
variable {A' : Type u} {B' : Type v} {C' : Type w} [Category.{u} A'] [Category.{v} B']
  [Category.{w} C'] (L : A' ⥤ C') (R : B' ⥤ C')
example {X Y : Comma L R} (a : X.left ⟶ Y.left) (b : X.right ⟶ Y.right)
    (h : L.map a ≫ Y.hom = X.hom ≫ R.map b) :
    (S1836IsoCommaFst L R).map
      (ObjectProperty.homMk (P := fun Y : Comma L R => IsIso Y.hom)
        (CommaMorphism.mk a b h)) = a := rfl
end Test
