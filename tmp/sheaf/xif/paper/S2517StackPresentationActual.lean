import tmp.sheaf.xif.paper.S2517StackHomActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2512StackOpenImmersionUB
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2521RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S2517StackHomActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2517StackPresentationActual

noncomputable def S2517Square (C : FiniteEtaleCover S2482AffineScheme)
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      (Iut.schemeRepresentableEtalePseudofunctor F S2517S)) :
    Iut.EtalePseudofunctorSquare
      (S1742YS (F := F) (S2517PullbackScheme C T q))
      (S1742YS (F := F) (S2517CScheme C))
      (S1742YS (F := F) T)
      (S1742YS (F := F) S2517S) where
  toX := S1742StrongTransOfHom (S2517ToSource C T q)
  toY := (S2517ProjectionMap C T q).transformation
  xToBase := S1742StrongTransOfHom (S2517OverMap C)
  yToBase := q
  commutes := S2517Commutes C T q

noncomputable def S2517RepBaseChange (C : FiniteEtaleCover S2482AffineScheme)
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F T)
      (Iut.schemeRepresentableEtalePseudofunctor F S2517S)) :
    Iut.EtaleStackBaseChangePresentation (S2517StackHom C) T (S2517Point T q) where
  pullbackScheme := S2517PullbackScheme C T q
  projection := S2517Projection C T q
  projectionMap := S2517ProjectionMap C T q
  toSource := S1742StrongTransOfHom (S2517ToSource C T q)
  commutes := S2517Commutes C T q
  isPullback := by
    let sq := S2517Square C T q
    have hpb : IsPullback (S2517ToSource C T q).left
        (S2517Projection C T q).left
        (S2512BaseF sq).left (S2512BaseG sq).left := by
      rw [show S2512BaseF sq = S2517OverMap C from by
            change S1742HomOfStrongTrans sq.xToBase = S2517OverMap C
            rw [show sq.xToBase = S1742StrongTransOfHom (S2517OverMap C) from rfl,
              S1742HomOfStrongTrans_strongTransOfHom],
          show S2512BaseG sq = S2517G T q from rfl]
      exact IsPullback.of_hasPullback C.obj.hom (S2517G T q).left
    exact S2512Witness (P := S2517PullbackScheme C T q)
      (pX := S2517ToSource C T q)
      (pY := S2517Projection C T q)
      (sq := sq) hpb rfl rfl

#check S2517RepBaseChange

end LeanFormal.IUT.XiFPaper.S2517StackPresentationActual
end