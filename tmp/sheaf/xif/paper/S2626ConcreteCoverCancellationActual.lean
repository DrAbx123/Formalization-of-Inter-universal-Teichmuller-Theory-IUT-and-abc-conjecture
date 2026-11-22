import tmp.sheaf.xif.paper.S2625D6CoverCancellationData
import tmp.sheaf.xif.paper.S2622M1ConcreteWitnessActual
import tmp.sheaf.xif.paper.S2514IdentityFiniteEtaleActual
import tmp.sheaf.xif.paper.S2482QiOrbicurveActual

/-! # S2626: concrete cover with cancellation (identity cover) -/

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2514IdentityFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2619RightCancellationActual
open LeanFormal.IUT.XiFPaper.S2620M1CoherenceFields
open LeanFormal.IUT.XiFPaper.S2622M1ConcreteWitnessActual

namespace LeanFormal.IUT.XiFPaper.S2626ConcreteCoverCancellationActual

universe u

/-- Generalized (non-S1728-specific) wrapper: any cover of an orbicurve over
S1726K together with the two cancellation fields. -/
structure CoverWithCancellation
    {X : Iut.HyperbolicOrbicurve S1726K}
    (cover : Iut.OrbicurveFiniteEtaleCover X) : Type 1 where
  cancelRight : RightCancellation cover.map
  cancelWitness : M1RightCancellationWitness cover.map

/-- The identity (terminal) cover of the S2482 orbicurve over S1726K, with
cancellation fields supplied by S2622. -/
noncomputable def terminalCoverWithCancellation :
    CoverWithCancellation
      (S2514TerminalCover (F := S1726K) (X := S2482Orbicurve (F := S1726K))) where
  cancelRight := rightCancellationId (S2482Orbicurve (F := S1726K)).stack
  cancelWitness := m1RightCancellationWitnessId (S2482Orbicurve (F := S1726K)).stack

#check terminalCoverWithCancellation
#print axioms terminalCoverWithCancellation

end LeanFormal.IUT.XiFPaper.S2626ConcreteCoverCancellationActual
end
