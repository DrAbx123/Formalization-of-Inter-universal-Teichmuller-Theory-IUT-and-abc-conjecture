import tmp.sheaf.xif.paper.S2519InvFunctorActual
import tmp.sheaf.xif.paper.S2482QiOrbicurveActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517StackHomActual
open LeanFormal.IUT.XiFPaper.S2519InvFunctorActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open Iut
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2519InvEquivalenceGoalActual

noncomputable def S2519BasePoint :
    Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor F S2482AffineOver)
      S2482Orbicurve.stack.fiber :=
  Pseudofunctor.StrongTrans.id _

/-- The exact fully-faithful target for S2519InvFunctor. -/
def S2519InvFunctorFullFaithful : Prop :=
  S2519InvFunctor.Full ∧ S2519InvFunctor.Faithful

/-- The exact essential-surjectivity target. -/
def S2519InvFunctorEssSurj : Prop :=
  S2519InvFunctor.EssSurj

/-- The scheme cover candidate obtained by base-changing an orbicurve cover
along the identity point. -/
noncomputable def S2519PreimageCover
    (E : OrbicurveFiniteEtaleCover S2482Orbicurve) :
    FiniteEtaleCover S2482AffineScheme :=
  let bc := E.finiteEtale.baseChange S2482AffineOver S2519BasePoint
  ⟨Over.mk bc.projection.left,
    (E.finiteEtale.hasProperty S2482AffineOver S2519BasePoint).2,
    (E.finiteEtale.hasProperty S2482AffineOver S2519BasePoint).1⟩

/-- The exact essential-surjectivity goal, with the candidate preimage. -/
def S2519InvFunctorEssSurjGoal : Prop :=
  ∀ E : OrbicurveFiniteEtaleCover S2482Orbicurve,
    Nonempty (S2517InvObj (S2519PreimageCover E) ≅ E)

#check S2519InvFunctorFullFaithful
#check S2519InvFunctorEssSurj
#check S2519PreimageCover
#check S2519InvFunctorEssSurjGoal

end LeanFormal.IUT.XiFPaper.S2519InvEquivalenceGoalActual
end
