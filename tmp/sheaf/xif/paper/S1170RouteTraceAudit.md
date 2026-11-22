# S1170: actual routeTrace for ParametricCarrier

Read:
- LeanFormal/IUT/IUTIII/Theorem311/ParametricCarrier.lean
  (AlgorithmInput, AlgorithmOutput, runAlgorithm, routeTarget, applyStep/applyRoute)
- LeanFormal/IUT/IUTIII/Theorem311/Output/SourceMultiradialPresentationWiring.lean
  (sourcePresentationOfCarrier, sourceAlgorithmOfCarrier)

Lean audit: tmp/sheaf/xif/paper/S1170RouteTraceAuditActual.lean — EXIT=0.

## Required data for routeTrace

routeTrace needs only:
- carrier : ParametricTheorem311.Carrier Label Choice;
- carrier.core : Core Label Choice, specifically applyStep carrier.core step c;
- route : List (RouteStep Label);
- initial c : Choice (input.source for AlgorithmInput).

It does not need carrier.profile, connector, automorphism data, or ind2 data.

## Actual definition

structure RouteTrace (Choice) where
  states : List Choice
  endpoint : Choice

def routeTrace (carrier) :
    List (RouteStep Label) → Choice → RouteTrace Choice
  | [], c => { states := [], endpoint := c }
  | step :: rest, c =>
      let c' := applyStep carrier.core step c
      let t := routeTrace carrier rest c'
      { states := c' :: t.states, endpoint := t.endpoint }

## Target relation

- routeTrace_states_length:
    (routeTrace carrier route c).states.length = route.length.
- routeTrace_endpoint_eq_routeTarget:
    (routeTrace carrier route c).endpoint = routeTarget carrier route c.
- routeTrace_endpoint_eq_runAlgorithm_target:
    for input : AlgorithmInput carrier,
    (routeTrace carrier input.route input.source).endpoint
      = (runAlgorithm carrier input).target.
- routeTraceForgetRun carrier input := trace endpoint; equals runAlgorithm target.

Thus the actual output target is exactly the last state of the route trace, and a
SourceRun/forgetRun may use this endpoint without adding hypotheses.

## What is still absent

- strip interpretation stripOfChoice / stripOfRun / diagramOfRun: no
  Choice -> SourceFTimesMuPrimeStrip V;
- operation-arrow realization and commEnv square: exact gap, no inhabitant;
- reduced Choice still drops carrier core/profile/connector/input route.
