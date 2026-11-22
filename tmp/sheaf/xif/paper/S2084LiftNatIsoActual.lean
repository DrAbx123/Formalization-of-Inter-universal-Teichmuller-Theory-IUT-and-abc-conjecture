import tmp.sheaf.xif.paper.S2083LiftConeCompatActual

/-! # S2084: general lift cone hom/isos and liftNatIso

Mirrors S1985 `liftConeHomForward`, `liftConeIso`, `liftNatIso` for an
arbitrary `S2074GeneralCone`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2084LiftNatIsoActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S1985SiteLiftNaturalityActual
open LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2078ConeAtLiftAppActual
open LeanFormal.IUT.XiFPaper.S2079GeneralLiftNatActual
open LeanFormal.IUT.XiFPaper.S2081Cone1Actual
open LeanFormal.IUT.XiFPaper.S2082Cone2Actual
open LeanFormal.IUT.XiFPaper.S2083LiftConeCompatActual

universe u
variable {A B C : S1728Cover}
variable (f : S1728CoverMap A C) (g : S1728CoverMap B C)

noncomputable def S2084liftConeHomForward (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    S1893Cone.Hom
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↑(c.W.obj U)).obj
          ((c.W.map φ).toFunctor ⋙ S2078LiftApp f g c V))
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↑(c.W.obj U)).obj
          (S2078LiftApp f g c U ⋙ (S1890IsoCommaMap f g φ).toFunctor)) :=
  ⟨(S2079LiftNatConeA (f := f) (g := g) c φ,
    S2079LiftNatConeB (f := f) (g := g) c φ), by
    apply NatTrans.ext
    funext x
    dsimp only
    simp only [NatTrans.comp_app, Functor.whiskerRight_app]
    rw [S2081cone1_commutes_app, S2082cone2_commutes_app]
    dsimp only [S2079LiftNatConeA, S2079LiftNatConeB]
    exact S2083liftCone_compat f g c φ x⟩

noncomputable def S2084liftConeIso (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    Iso
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↑(c.W.obj U)).obj
          ((c.W.map φ).toFunctor ⋙ S2078LiftApp f g c V))
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↑(c.W.obj U)).obj
          (S2078LiftApp f g c U ⋙ (S1890IsoCommaMap f g φ).toFunctor)) := by
  haveI hA : IsIso (S2084liftConeHomForward f g c φ).toA := by
    change IsIso ((c.toA.naturality φ).hom.toNatTrans)
    infer_instance
  haveI hB : IsIso (S2084liftConeHomForward f g c φ).toB := by
    change IsIso ((c.toB.naturality φ).hom.toNatTrans)
    infer_instance
  letI : IsIso (C := S1893Cone (f.map.app V).toFunctor (g.map.app V).toFunctor
      ↑(c.W.obj U)) (S2084liftConeHomForward f g c φ) :=
    coneHom_isIso (m := S2084liftConeHomForward f g c φ)
  exact asIso (S2084liftConeHomForward f g c φ)

noncomputable def S2084liftNatIso (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    Iso (((c.W.map φ).toFunctor ⋙ S2078LiftApp f g c V))
      (S2078LiftApp f g c U ⋙ (S1890IsoCommaMap f g φ).toFunctor) :=
  Functor.FullyFaithful.preimageIso
    (Functor.FullyFaithful.ofFullyFaithful
      (S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↑(c.W.obj U)))
    (S2084liftConeIso f g c φ)

#print axioms S2084liftConeHomForward
#print axioms S2084liftNatIso

end LeanFormal.IUT.XiFPaper.S2084LiftNatIsoActual

end
