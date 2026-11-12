# QPILOT-FIELD-SOURCES — field-by-field inventory for QPilotIdentificationActual

Status: READ-ONLY inventory. No edits to other lanes. Green status below means the module
has an olean in .lake/build/lib/lean; it does NOT mean the identification structure is
unconditionally inhabited. The canonical assembly constructor is conditional on source
donors, which are listed explicitly.

## 1. The structure and its five fields

File: tmp/sheaf/xif/paper/QPilotIdentificationActual.lean (olean 225616 B).

structure QPilotIdentificationActual (I : OriginalInput l V) where
  object          : PaperQPilotObjectActual I
  canonicalStrip  : SourceFTimesMuPrimeStrip V
  strip_eq        : object.strip = canonicalStrip
  canonicalOneColumn : SourceOneColumnArithmeticHolomorphicStructure V
  oneColumn_eq    : object.oneColumn = canonicalOneColumn
  canonicalLogKummer : SourceLogKummerData I object.line.C1
  logKummer_eq    : object.logKummer = canonicalLogKummer
  canonicalOneZero : OneZeroPoint
  oneZero_eq      : object.oneZero = canonicalOneZero

Canonical assembler:
tmp/sheaf/xif/paper/QPilotIdentificationConstruction.lean:34
  qPilotIdentificationActualOfCanonical (L : QPilotLineActual I)
    (F : FPrimeStrip V) (oneColumn : SourceOneColumnArithmeticHolomorphicStructure V)
    : QPilotIdentificationActual I
All four equalities are rfl; the object is built by
paperQPilotObjectActualOfCanonical (QPilotCanonicalConstruction.lean:50).

## 2. Field sources

| field | type definition | green constructor/theorem | olean | status |
|---|---|---|---|---|
| object (PaperQPilotObjectActual) | QPilotObjectActual.lean:154 | paperQPilotObjectActualOfCanonical (QPilotCanonicalConstruction.lean:50) | QPilotCanonicalConstruction 34704 B | green constructor, conditional on L,F,oneColumn |
| canonicalStrip (SourceFTimesMuPrimeStrip) | SourceFTimesMuPrimeStripPolyIsomorphism.lean:164 | SourceFTimesMuPrimeStrip.canonical (F : FPrimeStrip V), :236 | 2383976 B | green; F is an actual strip parameter, no canonical F supplied automatically |
| oneColumn (SourceOneColumnArithmeticHolomorphicStructure) | SourceArithmeticHolomorphicLanding.lean:155 | sourceOneColumnStructureOfNumberField k (:434); generic nonempty (:191) is a gate-only Z/Q witness | 388232 B | green only for V = NumberField.FinitePlace k; generic witness is not the paper 1,circ structure |
| logKummer (SourceLogKummerData) | tmp/sheaf/n8/closure/SourceLogKummerRealization.lean:47 | sourceLogKummerDataActual (C2Actual.lean:32); sourceLogKummerData_nonempty_actual (:58) | C2Actual 68056 B | green, conditional on C1 : SourceInputBinding I |
| oneZero (OneZeroPoint) | QPilotObjectActual.lean:57 | oneZeroPoint (:63); oneZeroPoint_eq (:73) | QPilotObjectActual 319512 B | **unconditional green** |

## 3. qPilotObject / qPilotData chain

### QPilotLineActual (the object.line source)
QPilotObjectActual.lean:84:
  structure QPilotLineActual I where
    C1 : SourceInputBinding I
    C2 : SourceLogKummerData I C1
    C3 : SourcePilotRegionData I

Actual constructors:
- C1: tmp/sheaf/n8/closure/C1Actual.lean:60
    sourceInputBindingOfActual (I) (D : C1ActualData I) : SourceInputBinding I
  C1ActualData has four actual donor fields: placeEquiv, selected, selected_realization,
  fiberMonEquiv. No unconditional inhabitant; the file records the missing production
  declarations. nonempty theorem: sourceInputBinding_nonempty_of_actual (:66).
- C2: C2Actual.lean:32 sourceLogKummerDataActual I C1; requires C1.
- C3: C3Actual.lean:80 sourcePilotRegionDataOfDonors
    (D : SourcePilotRegionDonors I) : SourcePilotRegionData I;
  requires the full ~19-field donor record. nonempty theorem:
  sourcePilotRegion_nonempty_of_donors (:109).

Therefore QPilotIdentificationActual is **not unconditionally inhabited**: the canonical
constructor needs L (C1+C2+C3), F (actual FPrimeStrip), and oneColumn. The field equalities
are rfl once those data exist.

### qPilotData alternatives
- EtTh04QPilotDataActual.lean:53 EtThQPilotData
    thetaMagnitude, qMagnitude, theta_eq, q_negative
  constructor etThQPilotDataOfModel (:60):
    thetaMagnitude := modelThetaValue M,
    qMagnitude := -1,
    q_negative := by norm_num.
  This is a MODEL interface (M : LGPModelSourceClauseMissing l); it is green (olean 88664 B)
  but qMagnitude=-1 is a model placeholder, not the actual q-pilot.
- Mzk1QPilotPreciseActual.lean / Mzk1PaperPreObjectInterfacesActual.lean define a
  structure QPilotData, but those are model/interface files; Mzk1QPilotPreciseActual has
  **no olean** in the current build. Not a green actual source.

## 4. Summary

- All five field type definitions have green modules/oleans.
- oneZero is the only field with an unconditional green inhabitant (oneZeroPoint).
- canonicalStrip has a green constructor from an actual FPrimeStrip; the actual F must be
  supplied (e.g. an OriginalInput prime-strip field); no canonical F is built here.
- oneColumn is green for the actual finite-place carrier of a number field
  (sourceOneColumnStructureOfNumberField); the generic nonempty witness is gate-only and
  explicitly not the paper 1,circ structure.
- logKummer is green conditional on C1; qPilotObject is green conditional on
  C1/C2/C3 + F + oneColumn; qPilotData has only a model interface (EtThQPilotData), not an
  actual q-pilot data object.
- QPilotIdentificationActual itself remains a source obligation: the canonical assembler is
  green and type-checks, but its inhabitant requires the C1/C2/C3 donor chain and the actual
  one-column/strip data. This is a source-donor gap, not a Lean error.
