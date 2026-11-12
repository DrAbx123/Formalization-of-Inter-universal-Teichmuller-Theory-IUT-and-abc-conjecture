# L-CARRIER-INVENTORY — L-side q-pilot fields and construction data

Status: READ-ONLY inventory, 2026-11-12. Focus: what abc needs to build the L-version
q-pilot object, and whether C1/C2 change on the L carrier. No files outside coord were
modified.

## 1. SourcePilotRegionDataL — complete fields (S1391)

File: tmp/sheaf/xif/paper/S1391C3LSourcePilotActual.lean:244 (olean 1237696 B).
Carrier: OriginalInput.{0,0,upi,umon,ui} l (FinitePrimePlace 2 7).

Fields:
1. p : Nat
2. hp : Fact p.Prime (instance)
3. place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p
4. q : FinitePlaceQCandidate place.val
5. thetaPacket : FiniteThetaPacket l
6. qUnit : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)^x
7. qUnit_eq : qUnit = candidateUnits (K := I.initial.arithmetic.Fmod) place q
8. qUnitAlgClosure_eq : concreteQUnitAlgebraicClosure (I) place =
     Units.map (algebraMap completion (ConcreteQAlgebraicClosure I place)).toMonoidHom qUnit
9. roots : NatRootSystem (concreteQUnitAlgebraicClosure (I) place)
10. roots' : NatRootSystem (concreteQUnitAlgebraicClosure (I) place)
11. kummerClass : C3LGalois I place -> CyclotomicTower (ConcreteQAlgebraicClosure I place)
12. rootChange : C3LGalois I place -> CyclotomicTower (ConcreteQAlgebraicClosure I place)
13. kummerClass_eq_rootChange : forall sigma, kummerClass sigma = rootChange sigma
14. rootChange_eq : forall sigma, rootChange sigma =
      KummerClass.rootSystemDiff roots (galoisRootsAction I place sigma roots)
15. tensorIndex : Type
16. tensorFintype : Fintype tensorIndex (instance)
17. tensorPlaceIndex : tensorIndex -> Type
18. tensorPlaces : (i) -> tensorPlaceIndex i -> FinitePlaceAtPrime Fmod p
19. tensorTuple : (i) -> tensorPlaceIndex i
20. tensorUnit : (ArithmeticTensorTupleBlock tensorPlaces tensorTuple)^x
21. tensorLanding : CommonPrimeCompletion place -> ArithmeticTensorTupleBlock ...
22. tensorLanding_q : tensorLanding (q.q) = tensorUnit

Actual constructor:
- actualSourcePilotRegionDataL (S1391:329):
    (I : OriginalInput.{0,0,upi,umon,ui} l (FinitePrimePlace 2 7))
    (place : FinitePlaceAtPrime Fmod p) [Fact p.Prime]
    : SourcePilotRegionDataL I
  Uses concreteQCandidate, concreteThetaPacket, concreteQUnit, concreteRootsAlgebraicClosure,
  actualC3KummerClass/actualC3RootChange, concrete tensor unit/landing. Green (olean above).
- sourcePilotRegionLToCore (S1391:285) projects to SourcePilotRegionCore; it preserves
  p, place, q, thetaPacket, qUnit, qUnit_eq, tensor block. actual..._toCore (:357) is rfl.
- actualSourcePilotRegionDataL_roots (:363) and roots' (:369) show the roots are the
  algebraic-closure concrete root systems.

## 2. q / order path from L data

The L record has no separate qOrder field. The path is:
1. D.q : FinitePlaceQCandidate place.val, with D.q.q : completion, D.q.q_ne_zero,
   D.q.valuation_lt_one;
2. D.qUnit : completion units and D.qUnit_eq : qUnit = candidateUnits ... D.q
   (S1391:252-253; core projection :291-294);
3. q-order: FinitePlaceQCandidate.exponent (LeanFormal/IUT/Foundations/NumberField/
   LocalQParameter.lean:67):
     exponent (parameter) : Int := -Multiplicative.toAdd (WithZero.unzero valuation)
   i.e. minus the additive exponent of the valuation, so the q-order is D.q.exponent.
   There is no L-specific qOrder wrapper; if a Nat/order is needed, use this Int and the
   qUnit equality to identify the candidate unit.
4. qUnitAlgClosure_eq (:254) is the explicit link from the completion q unit to the
   algebraic-closure carrier used by the L roots.

## 3. C1/C2 on the L carrier

- SourcePilotRegionDataL does not contain C1 : SourceInputBinding or C2 :
  SourceLogKummerData. Those are separate carrier-facing layers.
- SourceInputBinding I is carrier-dependent: C1ActualData has placeEquiv
  (V = NumberFieldPlaceIndex), selected, selected_realization, fiberMonEquiv for
  I.primeStripAt. On the L carrier V = FinitePrimePlace 2 7 there is no unconditional C1
  instance; it must be supplied (C1ActualData or NativeC1PaperSource packet).
- SourceLogKummerData I C1 is built by sourceLogKummerDataActual (C2Actual:32) from C1
  and I.initial.arithmetic.Fmod only; it does not use the old completion root block or
  the L roots. Thus C2 needs no type change for the L carrier; it only needs a C1 for
  the same I.
- Neither C1 nor C2 is consumed by the L paper q-pilot object:
  OrigXiFPaperQPilotFromSourceLActual.OrigXiFPaperQPilotOfBoundary (:247) uses
  paperQPilotObjectSourceActual with oneColumn/lineBundle/logKummer from actual L data;
  C1/C2 do not appear in its five fields.
- If one targets QPilotIdentificationActual instead, that structure is still
  old-carrier typed: its C3 field is SourcePilotRegionData, not L. L roots cannot replace
  the old completion roots; S1408 needs CompletionRootBlock (completion NatRootSystem).
  So C1/C2 definitions do not change, but QPilotIdentificationActual still needs the
  old C3 completion block.

## 4. Complete field list for the L paper q-pilot object

The green L-version object is
  OrigXiFPaperQPilotFromSourceLActual.OrigXiFPaperQPilotOfBoundary
  (tmp/sheaf/xif/paper/OrigXiFPaperQPilotFromSourceLActual.lean:247; olean 147176 B).

Inputs:
- I : OriginalInput.{0,0,upi,umon,ui} l (FinitePrimePlace 2 7);
- b : OrigXiFQPilotFirstFieldType (l) =
    SourceProcessionBoundary.Input (l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l).
  The exact first field is actual: OrigXiFQPilotFirstFieldType_nonempty (:149) gives
  b := SourceProcessionBoundary.Input.concreteInput l.
- D : SourcePilotRegionDataL I (actual via actualSourcePilotRegionDataL I place) is used
  in the L-side attachment theorems (§5), not in the five data fields.

The constructed PaperQPilotObject fields and their sources:
| field | term | source |
|---|---|---|
| boundary | b | exact first-field input (actual concreteInput) |
| strip | sourceQPilotStrip b | forced by paperQPilotObjectSourceActual strip_eq_source |
| oneColumn | actualOneColumnFinitePrimePlace | OneColumnFinitePrimePlaceActual (olean 43256 B) |
| lineBundle | OrigXiFSourceLLineBundleCarrier I | OrigXiF file :207 |
| logKummer | selfKummerArrow (sourceQPilotStrip b) | actual self Kummer arrow |
| qPilotLogVolume | sourceQPilotSignedLog I.initial | actual source q-pilot scalar |
The four paper_*_identification fields are inherited from paperQPilotObjectSourceActual and
remain the explicit empty-target obligations (not True/PUnit).

Green theorems: OrigXiFPaperQPilotOfBoundary_boundary/strip/oneColumn/lineBundle/
logKummer/qPilotLogVolume/data (:259-312); L-side attachments
OrigXiFActualSourceL_q/qUnit/thetaPacket/qScalar (:181-198),
OrigXiFSourceLLineBundle_fiber_ring (:223), OrigXiFSourceLTensorLanding (:368).

## 5. Verdict

- L record: actual green (S1391 actualSourcePilotRegionDataL); all fields listed in §1.
- q/order: path D.q.q, D.q.exponent, D.qUnit, D.qUnit_eq, D.qUnitAlgClosure_eq; no separate
  qOrder field.
- L paper q-pilot object: **constructible green** via OrigXiFPaperQPilotOfBoundary with
  actual b = concreteInput l and actual I; five data fields actual; q-pilot scalar actual.
- C1/C2: carrier-facing; C1 needs an L-carrier SourceInputBinding (conditional donor);
  C2 follows from C1 with no type change and is not used by the L paper q-pilot object.
- QPilotIdentificationActual L-version: **not constructible from L data alone**; it needs
  C1 and the old C3 SourcePilotRegionData, whose missing piece is the completion root
  block (S1408). Do not substitute L roots for completion roots.
