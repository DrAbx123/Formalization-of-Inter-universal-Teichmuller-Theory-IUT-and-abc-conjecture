# C9IUTBridgeSkeleton: compile and scope record

Task: task-469. Date: 2026-10-25. Author: transport.
No Lean source edits outside this skeleton. No toy data, no axiom, no sorry.

## 0. Deliverable

- Lean file: tmp/sheaf/n8/closure/C9IUTBridgeSkeleton.lean
- lines: 71
- SHA256: 77630E00778741255F733F2E42118A1D2F3D80A9E1E3519539C061AF694838D3

## 1. Compile

Command:

    Set-Location D:\lean
    pwsh -NoProfile -File tmp\n8-20261018\lead\lean-serial.ps1 env lean -j1 tmp\sheaf\n8\closure\C9IUTBridgeSkeleton.lean

Result:

    EXIT=0
    no stdout/stderr errors

Only the named skeleton file was created/edited. No Project files, no other
Lean sources, and no task-268 files were modified.

## 2. Imports

    LeanFormal.IUT.IUTIII.Theorem311.SourceTheorem311ReferenceContract
    LeanFormal.IUT.IUTIII.Corollary312.StepXI.ContractSourceReduction
    LeanFormal.IUT.IUTIII.Corollary312.StepXI.ParametricStepXI
    LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume

These are the actual contract, Step-XI, parametric Step-XI, and source hull
volume modules named by the task.

## 3. Actual types used

The structure C9IUTBridgeData is parameterized by:

    R : SourceTheorem311Realization l Label Choice
        (actual Theorem 3.11 source realization,
         SourceHodgeTheaterBridge)

    I : Theorem311Source.OriginalInput l V
        (actual initial Theta-data input)

    v : V
    Rimg : I.SourceImageRealization v
    n : Theorem311Source.OriginalInput.ThetaPilotCarrier l
    k : Type, [Field k] [NumberField k]
    selectedLowerPlaces : Finset (NumberField.FinitePlace k)
    parameters : (lowerPlace : selectedLowerPlaces) ->
      NumberFieldFinitePlace.FinitePlaceQCandidate lowerPlace.val

Its fields are:

    sourceOutput : Theorem311Source.Theorem311Output R.input
    qPilotLog : Real
    qPilotLog_source :
      qPilotLog =
        ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
          selectedLowerPlaces parameters
    hull : Submonoid (I.ThetaPilotPoint v)
    hull_eq : hull = I.sourceHolomorphicHull v Rimg n
    hullVolume : ENNReal
    hullVolume_eq : hullVolume = I.sourceHullVolume v Rimg n
    c1SourceBridge : C1SourceBridge qPilotLog hullVolume

No type is a new toy carrier: sourceOutput is the actual Theorem 3.11 output
type of R.input; qPilotLog is tied by equality to the actual normalized signed
q-log; hull and hullVolume are tied by equality to the actual
sourceHolomorphicHull and sourceHullVolume; c1SourceBridge is the explicit
missing proposition.

## 4. C1SourceBridge

    def C1SourceBridge (qPilotLog : Real) (hullVolume : ENNReal) : Prop :=
      qPilotLog <= hullVolume.toReal

This is an explicit Prop, not an axiom and not a sorry. The skeleton does not
prove it and does not inhabit C9IUTBridgeData. It records the remaining bridge
inequality as a field so that a future file can supply the actual source
theorem.

Caveat: the exact source bridge is stronger than this real inequality
(namely, the q-pilot log-volume is a possible output log-volume and the source
normalization must be compared through the determinant/hull interface). The
field is intentionally a named explicit target, not a claimed source theorem.

## 5. No axioms, no sorry

Search of the Lean file for sorry/axiom: no declaration uses either.
The word "sorry" occurs only in the docstring statement that there is none.
No axiom command, no opaque, no unsafe.

## 6. Scope and status

This is a typed bridge skeleton, not a construction of C1. It does not:

- construct a SourceTheorem311Realization or any of its fields;
- construct a SourceImageRealization;
- prove C1SourceBridge;
- identify the actual q-pilot with a paper q-pilot beyond the named source
  normalization equality;
- prove P6/Cor 3.12.

It does provide the actual source output/q/hull field types and the exact
missing-bridge Prop in one module that compiles against the project.

status: skeleton compiled; C1 open.
