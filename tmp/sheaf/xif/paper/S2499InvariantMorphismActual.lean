import tmp.sheaf.xif.paper.S2498InvariantStrongTransActual
import tmp.sheaf.xif.paper.S1932BuildA

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2496cFMapActual
open LeanFormal.IUT.XiFPaper.S2497InvariantSchemeActual
open LeanFormal.IUT.XiFPaper.S2498InvariantStrongTransActual
open LeanFormal.IUT.XiFPaper.S2470SignActionActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2499InvariantMorphismActual

theorem S2499CatHom₂Subsingleton
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    (A B : (S2482Orbicurve.stack.fiber).obj U ⟶ (S2495cF.stack.fiber).obj U) :
    Subsingleton (A ⟶ B) :=
  S1932NatTransSubsingleton (Discrete.isDiscrete _) A B

instance S2499StrongTransSubsingleton
    (A B : Iut.HyperbolicOrbicurve.Hom S2482Orbicurve S2495cF) :
    Subsingleton (A ⟶ B) := by
  constructor
  intro m n
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro U
  exact (S2499CatHom₂Subsingleton U (A.app U) (B.app U)).elim _ _

noncomputable def S2499InvariantMorphism :
    Iut.OrbicurveSignInvariantMorphism S2470SignAction S2495cF where
  map := S2496Map
  invariant := S2498Invariant
  cocycle := by
    let A : Iut.HyperbolicOrbicurve.Hom S2482Orbicurve S2495cF :=
      Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp S2470SignAction.inversion S2470SignAction.inversion)
        S2496Map
    exact (S2499StrongTransSubsingleton A S2496Map).elim _ _

#check S2499InvariantMorphism
#print axioms S2499InvariantMorphism

end LeanFormal.IUT.XiFPaper.S2499InvariantMorphismActual
end
