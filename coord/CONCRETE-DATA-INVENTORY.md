# Concrete IUT data inventory (A982)

## 1. `SourceProcessionBoundary.Input.concreteInput`

`LeanFormal/IUT/IUTIII/Theorem311/SourceProcessionBoundary.lean:431-444` (olean TRUE):
```
def concreteInput (l : PrimeGeFive) :
    Input (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l) where
  theater := ConcreteSourceHistoryLinkBridge.sourceTheater l
  history := ConcreteSourceHistoryLinkBridge.sourceHistory l
  carrier := SourceFiniteParameterized.carrier l
  baseChoice := ConcreteFiniteTheorem311.ProcessionChoice.base
  packetVolume := ...
```
→ gives a COMPLETE boundary `Input` for every `l : PrimeGeFive` (at `V = FinitePrimePlace 2 7`),
NOT an `OriginalInput`/`InitialThetaData`.

## 2. `Concrete*` series (paper dir, selected)

20+ files under `tmp/sheaf/xif/paper/Concrete*.lean`; examples and oleans:
- `ConcreteC3DonorActual` (olean TRUE), `ConcreteC3DonorAssemblyActual`,
  `ConcreteC3DonorCompletionActual`, `ConcreteC3RootCompletionActual`,
  `ConcreteC3RootTensorActual`;
- `ConcretePaperQPilotWitnessActual` (olean TRUE), `ConcretePaperSignedHullActual`,
  `ConcretePaperUnconditionalDataActual`, `ConcretePaperUnconditionalDataUnconditionalActual`,
  `ConcretePaperXiFInclusionActual(±Adapted)`;
- `ConcreteGlobalPilotDataActual`, `ConcreteHnormalActual`, `ConcreteKummerActionOnLiteralIQActual`,
  `ConcreteCompletionImageToLiteralIQActual`, `ConcreteQMagnitudeSourceComparisonActual`,
  `ConcreteCor312ConclusionActual(±Adapted)`;
- `ConcretePaperUnconditionalDataOtherwiseActual` has olean FALSE (one known miss).
They construct concrete C3 donor/paper q-pilot/signed-hull/xi-F data records, but no full
`InitialThetaData` was found (see §5).

## 3. NativeInput / N8NativeInput / NativeC1PaperSource concrete instances

Grep for `def ... : NativeInput` / `def ... : N8NativeInput` / `def ... : NativeC1PaperSource`
over `tmp/sheaf/n8`, `LeanFormal`: NO match.  The A962/A963 C1 donor work therefore remained
conditional on explicit hypotheses (`NativeC1DonorHypotheses`), consistent with this absence.

## 4. Concrete `PrimeGeFive` / `Fact (Nat.Prime ...)` for l = 7, 11, 13

Only local probe instances found (`tmp/sheaf/xif/paper/_ModMonicProbe*.lean:5`
`local instance : Fact (Nat.Prime 13) := ...`).  No registered `PrimeGeFive` instance for
7/11/13 was found in the searched trees.  `PrimeGeFive` can be built from a prime proof and
`5 <= l`, but no ready-to-use instance exists.

## 5. Concrete `InitialThetaData`/`SourceDefinition31Data`/`EllipticCurveData` instances

- `S1487OQPilotScalarEqualityActual.lean:520` (olean TRUE):
  `noncomputable def S1487FaithfulSourceData : SourceDefinition31Data.{0} l` — a concrete
  faithful source data, parameterized by `l` (not an `InitialThetaData`).
- `InitialThetaData` occurrences are constructors/consumers from variables, e.g.
  `SourceDefinition31RootLemmas.toSource`, `Definition31D0D11Aligned.conclusion`,
  `SourceInitialThetaData.toConclusion` — no `def ... : InitialThetaData` concrete term found.

## 6. Judgment: can we assemble an ℓ≥7 thetaData?

Not directly with existing concrete terms:
- boundary: YES (`concreteInput l`, for arbitrary `PrimeGeFive l`);
- source data: YES-ish (`S1487FaithfulSourceData : SourceDefinition31Data l`);
- C3/paper witnesses: partial (Concrete* series, several oleans missing);
- `OriginalInput` concrete assembly: NOT FOUND;
- `InitialThetaData` (lana type) concrete instance: NOT FOUND;
- `PrimeGeFive` instances for 7/11/13: NOT FOUND.
→ Ingredients exist for the boundary/data layer, but a full concrete thetaData cannot be
assembled today without (i) `PrimeGeFive` instances, (ii) an `OriginalInput` builder from
the boundary + S1487 source data, (iii) a C3 L-carrier record (A965/A966 gaps).
