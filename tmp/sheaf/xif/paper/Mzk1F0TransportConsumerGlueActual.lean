import tmp.sheaf.xif.paper.Mzk1F0StepTransportProvedActual

/-! # Mzk1F0TransportConsumerGlueActual — consumer-form glue for the PROVED f5 transport

Small glue module (no new mathematics): re-exposes the PROVED
`f0StepTransportInput_proved` in the consumer forms used downstream and derives the
two-step composed transport by applying it twice.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1F0TransportConsumerGlueActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.PaperScopeLemma24Actual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepTransportProvedActual

universe u

/-- Consumer form: backward transport of the paper-scope target along one f0 step. -/
theorem f0StepTransport_pointwise (S : Finset (P1Point Qbar)) (beta : P1Point Qbar)
    (alpha0 : Qbar) :
    PaperScopeLemma24Target (stepSetP1 S alpha0) (f0Map alpha0 beta) ->
      PaperScopeLemma24Target S beta :=
  f0StepTransportInput_proved S beta alpha0

/-- Two-step composition: transport twice along two f0 steps. -/
theorem f0StepTransport_comp (S : Finset (P1Point Qbar)) (beta : P1Point Qbar)
    (alpha0 alpha1 : Qbar) :
    PaperScopeLemma24Target (stepSetP1 (stepSetP1 S alpha0) alpha1)
        (f0Map alpha1 (f0Map alpha0 beta)) ->
      PaperScopeLemma24Target S beta :=
  fun h =>
  f0StepTransportInput_proved S beta alpha0
    (f0StepTransportInput_proved (stepSetP1 S alpha0) (f0Map alpha0 beta) alpha1 h)

/-- Consumer package: a goal at the step-level target yields the base target. -/
structure F0TransportGoalData (S : Finset (P1Point Qbar)) (beta : P1Point Qbar) where
  alpha0 : Qbar
  goal : PaperScopeLemma24Target (stepSetP1 S alpha0) (f0Map alpha0 beta)

/-- Consuming the package: the base target holds. -/
theorem F0TransportGoalData.target {S : Finset (P1Point Qbar)} {beta : P1Point Qbar}
    (d : F0TransportGoalData S beta) : PaperScopeLemma24Target S beta :=
  f0StepTransport_pointwise S beta d.alpha0 d.goal

#check f0StepTransport_pointwise
#check f0StepTransport_comp
#check F0TransportGoalData

end LeanFormal.IUT.XiFPaper.Mzk1F0TransportConsumerGlueActual
end
