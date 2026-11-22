import tmp.sheaf.xif.paper.S2517StackPresentationActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517StackPresentationActual
open LeanFormal.IUT.XiFPaper.S2517StackHomActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2517InvObjActual

noncomputable def S2517SStackOrb : Iut.EtaleStackOverField F where
  fiber := Iut.schemeRepresentableEtalePseudofunctor F S2482AffineOver
  isStack := S2482RepresentableIsStack
  orbicurveSignature := some Iut.OrbicurveSignature.oncePuncturedElliptic

noncomputable def S2517StackHomOrb (C : FiniteEtaleCover S2482AffineScheme) :
    Iut.EtaleStackOverField.Hom (S2517TStack (S2517CScheme C)) S2517SStackOrb :=
  S1742StrongTransOfHom (F := F) (S2517OverMap C)

noncomputable def S2517RepBaseChangeOrb (C : FiniteEtaleCover S2482AffineScheme)
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      (Iut.schemeRepresentableEtalePseudofunctor F S2517S)) :
    Iut.EtaleStackBaseChangePresentation (S2517StackHomOrb C) T q where
  pullbackScheme := S2517PullbackScheme C T q
  projection := S2517Projection C T q
  projectionMap := S2517ProjectionMap C T q
  toSource := S1742StrongTransOfHom (S2517ToSource C T q)
  commutes := S2517Commutes C T q
  isPullback := (S2517RepBaseChange C T q).isPullback

noncomputable def S2517InvObj (C : FiniteEtaleCover S2482AffineScheme) :
    Iut.OrbicurveFiniteEtaleCover S2482Orbicurve where
  source := S2517TStack (S2517CScheme C)
  map := S2517StackHomOrb C
  finiteEtale :=
    { baseChange := fun T q => S2517RepBaseChangeOrb C T q
      hasProperty := fun T q => by
        let g : T.left ⟶ S2482AffineScheme := (S2517G T q).left
        have h := LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations.FiniteEtaleCover.finiteEtale_pullback (S := S2482AffineScheme) (T := T.left)
          (g := g) (f := C.obj.hom) C.property.1 C.property.2
        change IsFinite (S2517Projection C T q).left ∧
          Etale (S2517Projection C T q).left
        exact ⟨h.2, h.1⟩ }

#check S2517InvObj

end LeanFormal.IUT.XiFPaper.S2517InvObjActual
end