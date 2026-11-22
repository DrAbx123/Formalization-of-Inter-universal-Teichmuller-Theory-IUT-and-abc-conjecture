import tmp.sheaf.xif.paper.S3123UnitCompExplicitActual
import tmp.sheaf.xif.paper.S3123ObjEqActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual
open LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual
open LeanFormal.IUT.XiFPaper.S3123LeftCoeActual
open LeanFormal.IUT.XiFPaper.S3123LeftExplicitActual
open LeanFormal.IUT.XiFPaper.S3123LeftMapActual
open LeanFormal.IUT.XiFPaper.S3123LeftMapIdActual
open LeanFormal.IUT.XiFPaper.S3123LeftMapCompActual
open LeanFormal.IUT.XiFPaper.S3123LeftExplicit2Actual
open LeanFormal.IUT.XiFPaper.S3123UnitCompExplicitActual
open LeanFormal.IUT.XiFPaper.S3123ObjEqActual

namespace LeanFormal.IUT.XiFPaper.S3123UnitNatExplicitActual

variable {l : PrimeGeFive}

@[simp] lemma S3123UnitCompExplicit_hom
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    (P : Opposite.unop U.as ⟶ S3123BaseChangedScheme (l := l)) :
    (S3123UnitCompExplicit (l := l) U P).hom =
      Discrete.eqToHom (by
        simp only [S3123FiberAppExplicit_apply]
        exact (Equiv.apply_symm_apply _ P).symm) := rfl

set_option maxHeartbeats 800000 in
instance S3123UnitNatRightHomSubsingleton
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    (X Y : (S3123Right (l := l)).obj U) :
    Subsingleton (X ⟶ Y) := by
  let I := ((Over.map (S3123BaseSpecMap (l := l))).obj (Opposite.unop U.as) ⟶
    S1419AffineOver (l := l))
  let hcat : (S3123Right (l := l)).obj U = Cat.of (Discrete I) :=
    S3123Right_obj_eq (l := l) U
  let X' : Cat.of (Discrete I) := hcat ▸ X
  let Y' : Cat.of (Discrete I) := hcat ▸ Y
  have h : Subsingleton (X' ⟶ Y') :=
    S3123FiberNatTransActual.S3123DiscreteHomSubsingleton _ _ _
  refine Eq.rec (motive := fun (C : Cat) (hC : (S3123Right (l := l)).obj U = C) =>
    Subsingleton ((hC ▸ X) ⟶ (hC ▸ Y))) h hcat

set_option maxHeartbeats 800000 in
lemma S3123UnitNatExplicit
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    {X Y : S3123LeftObj (l := l) U} (f : X ⟶ Y) :
    (𝟭 (S3123LeftObj (l := l) U)).map f ≫
        (S3123UnitCompExplicit (l := l) U Y.as).hom =
      (S3123UnitCompExplicit (l := l) U X.as).hom ≫
        ((S3123FiberAppExplicit (l := l) U ≫
          S3123FiberAppInvExplicit (l := l) U).toFunctor.map f) := by
  rcases X with ⟨x⟩
  rcases Y with ⟨y⟩
  rw [S3123UnitCompExplicit_hom, S3123UnitCompExplicit_hom]
  exact Subsingleton.elim _ _

#check S3123UnitNatExplicit

end LeanFormal.IUT.XiFPaper.S3123UnitNatExplicitActual
end
