import tmp.sheaf.xif.paper.S2560S2514LiftUniqueActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2558ConcreteWitnessPlanActual
open LeanFormal.IUT.XiFPaper.S2559ConcreteWitnessRefinementPlanActual
open LeanFormal.IUT.XiFPaper.S2514IdentityFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2560S2514LiftUniqueActual

namespace LeanFormal.IUT.XiFPaper.S2560S2514LiftUniqueActual.Probe

#check @S2560S2514LiftUnique
#check @S2560S2514TerminalCoverLiftUnique
#check @S2560S2514IdWitnessLiftUnique
#check @S2560LiftUnique_of_toY_id
#check @S2560S2514BaseChange
#check @S2560S2514IdWitness_lift
#check @S2560S2514IdWitness_liftTwoCell

#print axioms S2560S2514LiftUnique
#print axioms S2560S2514TerminalCoverLiftUnique
#print axioms S2560S2514IdWitnessLiftUnique
#print axioms S2560LiftUnique_of_toY_id
#print axioms S2560S2514BaseChange
#print axioms S2560S2514IdWitness_lift
#print axioms S2560S2514IdWitness_liftTwoCell

theorem terminalCoverLiftUnique_test :
    S2559HasLiftUnique (map := Pseudofunctor.StrongTrans.id S2482Orbicurve.stack.fiber)
      S2514TerminalCover.finiteEtale :=
  S2560S2514TerminalCoverLiftUnique

#print axioms terminalCoverLiftUnique_test

end LeanFormal.IUT.XiFPaper.S2560S2514LiftUniqueActual.Probe
end
