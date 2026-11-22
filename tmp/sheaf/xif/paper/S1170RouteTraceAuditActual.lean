import LeanFormal.IUT.IUTIII.Theorem311.ParametricCarrier

-- S1170: actual routeTrace for ParametricCarrier.AlgorithmInput.
-- Required data: carrier.core.applyStep, carrier.core.level-independent
-- routeTarget; input.source and input.route.  routeTrace records the
-- intermediate choices and their endpoint; endpoint = runAlgorithm.target.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1170RouteTraceAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.ParametricTheorem311
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.MultiradialKernel.Core

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-- Actual trace: intermediate choices after each route step plus endpoint. -/
structure RouteTrace (Choice : Type v) where
  states : List Choice
  endpoint : Choice

/-- routeTrace over a route, starting at a choice.  It uses only
carrier.core (applyStep) and the route list. -/
def routeTrace (carrier : Carrier Label Choice) :
    List (RouteStep Label) → Choice → RouteTrace Choice
  | [], c => { states := [], endpoint := c }
  | step :: rest, c =>
      let c' := applyStep carrier.core step c
      let t := routeTrace carrier rest c'
      { states := c' :: t.states, endpoint := t.endpoint }

/-- RouteTrace states length is exactly the route length. -/
theorem routeTrace_states_length
    (carrier : Carrier Label Choice) (route : List (RouteStep Label))
    (c : Choice) :
    (routeTrace carrier route c).states.length = route.length := by
  induction route generalizing c with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [routeTrace, ih]

/-- The routeTrace endpoint is exactly routeTarget. -/
theorem routeTrace_endpoint_eq_routeTarget
    (carrier : Carrier Label Choice) (route : List (RouteStep Label))
    (c : Choice) :
    (routeTrace carrier route c).endpoint =
      routeTarget carrier route c := by
  induction route generalizing c with
  | nil => rfl
  | cons step rest ih =>
      cases step <;> simp [routeTrace, routeTarget, ih]

/-- For an actual AlgorithmInput, the run target is the routeTrace endpoint. -/
theorem routeTrace_endpoint_eq_runAlgorithm_target
    (carrier : Carrier Label Choice) (input : AlgorithmInput carrier) :
    (routeTrace carrier input.route input.source).endpoint =
      (runAlgorithm carrier input).target := by
  rw [routeTrace_endpoint_eq_routeTarget, runAlgorithm_target,
    algorithmTarget]

/-- Concrete SourceRun-style projection: forgetRun may use the trace endpoint. -/
def routeTraceForgetRun
    (carrier : Carrier Label Choice) (input : AlgorithmInput carrier) : Choice :=
  (routeTrace carrier input.route input.source).endpoint

theorem routeTraceForgetRun_eq_runAlgorithm_target
    (carrier : Carrier Label Choice) (input : AlgorithmInput carrier) :
    routeTraceForgetRun carrier input = (runAlgorithm carrier input).target :=
  routeTrace_endpoint_eq_runAlgorithm_target carrier input

#check routeTrace
#check routeTrace_states_length
#check routeTrace_endpoint_eq_routeTarget
#check routeTrace_endpoint_eq_runAlgorithm_target
#check routeTraceForgetRun_eq_runAlgorithm_target

end LeanFormal.IUT.XiFPaper.S1170RouteTraceAuditActual

end