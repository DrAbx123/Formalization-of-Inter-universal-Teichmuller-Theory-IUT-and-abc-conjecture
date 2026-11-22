# S1153: ParametricCarrier algorithm output audit

Files read:
- LeanFormal/IUT/IUTIII/Theorem311/ParametricCarrier.lean
- LeanFormal/IUT/IUTIII/Theorem311/Output/SourceMultiradialPresentationWiring.lean
- LeanFormal/IUT/IUTIII/Theorem311/SourceMultiradialTwoActionEquivalence.lean

Lean audit: tmp/sheaf/xif/paper/S1153AlgorithmOutputAuditActual.lean — EXIT=0.

## 1. Actual algorithm data produced by runAlgorithm

AlgorithmInput (ParametricTheorem311.AlgorithmInput carrier):
- source : Choice;
- route : List (RouteStep Label);
- source_image_nonempty : (carrier.profile.possibleImage source).Nonempty.

runAlgorithm carrier input : AlgorithmOutput carrier input, with fields:
- target := algorithmTarget carrier input = routeTarget carrier input.route input.source;
- target_eq : target = algorithmTarget carrier input (rfl);
- level_monotone :
    carrier.core.level input.source <= carrier.core.level target,
  from routeTarget_level_monotone / verticalBudget;
- profile_monotone :
    carrier.profile.logVolume input.source <= carrier.profile.logVolume target,
  from routeTarget_profile_monotone (logVolume_applyRoute_le);
- target_image_upper :
    forall z in possibleImage input.source,
      exists w in possibleImage target, z <= w,
  from routeTarget_image_upper / possibleImage_applyRoute_ind3_upper.

Intermediate actual data: routeTarget, algorithmTarget, verticalBudget,
horizontalRoute, canonicalRoute, Ind1/Ind2/Ind3 certificates, IndependenceBundle.
These use carrier.core (level, ind1, ind2, ind3), carrier.profile
(logVolume, possibleImage), carrier.connector.

## 2. What the reduced records keep

SourceTheorem311MultiradialPresentation G I n Choice:
- output : Choice;
- processionAction : G ->* Equiv.Perm Choice.

SourceTheorem311MultiradialAlgorithm G1 G2 I n Choice:
- presentation : SourceTheorem311MultiradialPresentation G1 I n Choice;
- ind2Action : G2 ->* Equiv.Perm Choice;
- ind1_ind2_commute : the two permutation actions commute.

sourceAlgorithmOfCarrier carrier autom ind2Data input:
- output := (runAlgorithm carrier input).target;
- processionAction := autom.act (W.1);
- ind2Action := ind2Data.ind2 (W.4);
- commute := ind2Data.ind2_commute.

sourcePresentationOfCarrier is the same without ind2Data.

## 3. What is lost in the reduced Choice

The reduced output type is only Choice. Lost:
- carrier.core: level, base, ind1, ind2, ind3 operations and levels;
- carrier.profile: logVolume and possibleImage;
- carrier.connector and its horizontal/target laws;
- input.source and input.route (only the final target is kept);
- input.source_image_nonempty;
- target_eq, level_monotone, profile_monotone, target_image_upper;
- verticalBudget and canonicalRoute data;
- all Ind1/Ind2/Ind3 certificates and IndependenceBundle.

Kept only: final Choice output and the two permutation actions (W.1, W.4)
plus their commutation. R3 functor is not constructed; R2 (a)(b)(c) are not
constructed; W.3 source-column/fPrimeStripAt compatibility is not expressible
in the current interfaces.

## 4. SourceRun shape (S1153 audit)

structure SourceRun (carrier) (autom) (ind2Data) (input) where
  source : Choice
  source_eq : source = input.source
  route : List (RouteStep Label)
  route_eq : route = input.route
  output : AlgorithmOutput carrier input
  output_is_run : output = runAlgorithm carrier input

Actual: sourceRunOf carrier autom ind2Data input fills all fields by rfl/runAlgorithm.

forgetRun carrier autom ind2Data input R :
  SourceTheorem311MultiradialAlgorithm G1 G2 I n Choice
:= sourceAlgorithmOfCarrier carrier autom ind2Data input.

forgetRun_output:
  (forgetRun ... R).presentation.output = R.output.target.

So SourceRun preserves carrier/core/profile context, input source/route, the full
AlgorithmOutput (target and all monotonicity/upper proofs), while forgetRun keeps
only the reduced Choice target and the two actions.

## 5. Exact source obligations / status

- carrier CC.1 connector and CC.2 ind3_level_eq are carrier fields (hypotheses);
- W.1 SourceProcessionAutomorphismData and W.4 Ind2ActionData are hypotheses;
- source-level W.1/W.4 remain open; finite Q(i)-at-5 kernel form supplies them;
- W.3 compatibility with OriginalInput.fPrimeStripAt is not expressible;
- reduced form: output is abstract Choice, (a)(b)(c) not constructed.
No unconditional source-level algorithm is asserted.
