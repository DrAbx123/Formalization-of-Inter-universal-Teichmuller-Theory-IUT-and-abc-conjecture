# S946: qPilot carrier audit

Date: 2026-10-30. Audit only; no no-go.

## Paper q-pilot object actual surface

PaperQPilotObject fields:
* boundary : SourceProcessionBoundary.Input;
* strip : FPrimeStrip V;
* oneColumn : SourceOneColumnArithmeticHolomorphicStructure V;
* lineBundle : PaperLineBundleCarrier (Fmod);
* logKummer : SourceKummerArrow G envStrip strip;
* qPilotLogVolume : Real.

There is no single geometric carrier field; the object is a tuple of these
component structures, and qPilotLogVolume is a Real scalar (no set carrier).

## Model carrier

s914R = qPilotPaperRegion and s914S = paperRootThetaHullNonzero are both
subsets of qVFamTensorBlock T b.  model_R_S_same_carrier records the S914
containment; the S924/S927 V(R)<=V(S) comparison is therefore same-carrier at
the model level, not cross-carrier between R and S.

## Exact bridge to the paper object

PaperQPilotCarrierBridge:
  Carrier : Type;
  toModel : Carrier -> qVFamTensorBlock T b;
  qPilotImage : Set Carrier;
  qPilotImage_subset_R : toModel '' qPilotImage subset s914R;
  carries_strip / carries_oneColumn / carries_lineBundle / carries_kummer : Prop.

S946PaperQPilotCarrierBridgeRequired := Nonempty PaperQPilotCarrierBridge.
No inhabitant is asserted.

Thus V(R)<=V(S) is a valid model-carrier inequality, but its identification
with the paper qPilot object requires the carrier bridge above.  No claim that
the model comparison is invalid; no no-go, no fake carrier.
