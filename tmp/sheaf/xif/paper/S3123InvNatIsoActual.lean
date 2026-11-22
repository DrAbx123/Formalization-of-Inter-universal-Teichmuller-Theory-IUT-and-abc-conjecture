import tmp.sheaf.xif.paper.S3123InvNatActual
import tmp.sheaf.xif.paper.S3123ObjEqActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual
open LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual
open LeanFormal.IUT.XiFPaper.S3123InvAppActual
open LeanFormal.IUT.XiFPaper.S3123InvNatActual

namespace LeanFormal.IUT.XiFPaper.S3123InvNatIsoActual

variable {l : PrimeGeFive}

set_option allowUnsafeReducibility true in
attribute [local irreducible] S3123FiberAppInv

set_option maxHeartbeats 800000 in
noncomputable def S3123InvIsoApp
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) (X : (S3123Right (l := l)).obj a) :
    (((S3123Right (l := l)).map g).toFunctor ⋙
        (S3123FiberAppInv (l := l) b).toFunctor).obj X ≅
      ((S3123FiberAppInv (l := l) a).toFunctor ⋙
        ((S3123Left (l := l)).map g).toFunctor).obj X := by
  let I := (Opposite.unop b.as ⟶ S3123BaseChangedScheme (l := l))
  let X' : Discrete I := by
    dsimp only [CategoryTheory.Cat.of, CategoryTheory.Bundled.of,
      CategoryTheory.Bundled.α] at X ⊢
    exact X
  let Y' : Discrete I := by
    dsimp only [CategoryTheory.Cat.of, CategoryTheory.Bundled.of,
      CategoryTheory.Bundled.α] ⊢
    exact ((S3123Left (l := l)).map g).toFunctor.obj
      ((S3123FiberAppInv (l := l) a).toFunctor.obj X)
  exact S3123DiscreteIsoOfHom (I := I) (X := X') (Y := Y') (by
    simpa only [CategoryTheory.Cat.Hom.comp_toFunctor, Functor.comp_obj]
      using S3123FiberNatTransInvApp (l := l) g X)

@[simp] lemma S3123InvIsoApp_hom
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) (X : (S3123Right (l := l)).obj a) :
    (S3123InvIsoApp (l := l) g X).hom =
      S3123FiberNatTransInvApp (l := l) g X := by
  simp [S3123InvIsoApp, S3123DiscreteIsoOfHom]

set_option maxHeartbeats 800000 in
noncomputable def S3123FiberNatIsoInv
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) :=
  CategoryTheory.Cat.Hom.isoMk
    (NatIso.ofComponents
      (F := ((S3123Right (l := l)).map g).toFunctor ⋙
        (S3123FiberAppInv (l := l) b).toFunctor)
      (G := (S3123FiberAppInv (l := l) a).toFunctor ⋙
        ((S3123Left (l := l)).map g).toFunctor)
      (fun X => S3123InvIsoApp (l := l) g X)
      (fun {X Y} f => by
        simpa only [S3123InvIsoApp_hom,
          CategoryTheory.Cat.Hom.comp_toFunctor, Functor.comp_obj,
          Functor.comp_map]
          using S3123FiberNatTransInv_naturality (l := l) g f))

#check S3123FiberNatIsoInv

end LeanFormal.IUT.XiFPaper.S3123InvNatIsoActual
end
