# S1480: actual O(-D) fractional-ideal q-pilot line bundle

Date: 2026-10-31. EXIT=0; olean generated.

## What was simplified in S1457

S1457 OrigXiFPaperQPilotObjectActual used
OrigXiFPaperCompletionLineBundleCarrier: total = base field k, localization =
algebraMap k (Completion v). That is a completion-localized trivial bundle, not
the paper O(-D) fractional-ideal line bundle.

## New actual construction (this file)

Using OrigXiFPaperLineBundleActual (which builds
OrigXiFPaperQPilotLineBundle from QPilotPaperLineBundleActual.qPilotLineBundle,
the inverse zero-locus fractional ideal) and the actual pole-allowing carrier
OrigXiFPaperLineBundleCarrier:

  OrigXiFPaperLineBundleODIdentified D L :=
    L = OrigXiFPaperLineBundleCarrier I D

  OrigXiFPaperLineBundleODCarrier_identified D :
    OrigXiFPaperLineBundleODIdentified D (OrigXiFPaperLineBundleCarrier I D)

  OrigXiFPaperLineBundleODCarrier_total D :
    (OrigXiFPaperLineBundleCarrier I D).total =
      the actual q-pilot fractional ideal O(-D)

  origXiFPaperQPilotObjectOD O D :
    frozen PaperQPilotObject with lineBundle := actual O(-D) carrier
and paper_lineBundle_identification instantiated by the O(-D) proposition, not
the completion-carrier version.

## Exact first field

D : OrigXiFPaperLineBundleData I, whose only field is the existing exact
  arithmetic_root_eq : X.S.arithmetic = I.initial.arithmetic
for an actual native donor X.  No completion-carrier bundle is used to fill
the identification, and no fake carrier is introduced.

## Consumer

PaperQPilotObject consumers: origXiFPaperQPilotObjectOD returns the frozen
structure with the actual O(-D) line bundle and proved paper_lineBundle_identification.
S1457's completion-carrier object is superseded for line-bundle consumers.

## Verification

EXIT=0; no sorry/axiom/True/PUnit; olean generated.
