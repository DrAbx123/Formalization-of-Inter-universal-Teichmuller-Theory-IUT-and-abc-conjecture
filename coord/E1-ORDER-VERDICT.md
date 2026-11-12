# E1 order verdict (A936)

## What is green

- `OrigXiFPaperQPilotFromSourceLActual.lean:247` `OrigXiFPaperQPilotOfBoundary (I) (b)`
  is the ACTUAL L paper q-pilot object; boundary inhabited by
  `OrigXiFQPilotFirstFieldType_nonempty` (= `SourceProcessionBoundary.Input.concreteInput l`);
- its `qPilotLogVolume` field is exactly `sourceQPilotSignedLog I.initial` (:293-296, rfl);
- the L attachments (`OrigXiFActualSourceL_q/qUnit/thetaPacket/qScalar`) are green.

## Actual q order value

NOT COMPUTED: the source q candidate (order/exponent/valuation) is a field of the concrete
source input `I`; no concrete `I` (l=5 carrier with its C3 data) is available in this file.
The signed log of the actual source q is `sourceQPilotSignedLog I.initial`; its numerical
order needs the concrete candidate (`FinitePlaceQCandidate` order/exponent) of that `I`.

## E1 verdict

E1 (`Mzk1E1DictionaryActual`) asks `V_norm = V_hull`.  Its paper form is equivalent to the
q-side contribution being zero (`E1PaperScaledHullForm qSide := qSide = 0`, iff PROVED).

- The q-side contribution is `-sourceQPilotSignedLog I.initial`; it is NOT proved zero;
  therefore **E1 is NOT established for the actual D**.
- Correct identification form (interface): absorb the q-side into the volume comparison:
  `E1AllocationForm V_norm V_hull qSide := V_norm = V_hull + qSide`
  (`e1_allocation_of_zero` PROVED: for `qSide = 0` it reduces to `V_norm = V_hull`).
  This matches the A910 allocation discussion: E1 cannot be a bare equality; it must be
  stated relative to the q-pilot point.

## Machine file

`tmp/sheaf/xif/paper/Mzk1E1OrderActual.lean` (olean + trio): `E1PaperScaledHullForm`,
`e1_iff_qside_zero`, `QSideContribution`, `E1AllocationForm`, `e1_allocation_of_zero`,
`e1OrderRows` (6 rows).

## Next step

Compute the concrete order/exponent of `sourceQPilotSignedLog I.initial`'s q candidate for
a concrete l=5 carrier (needs the concrete `I` plus C1/C2/C3 data), then decide E1 or use
`E1AllocationForm` as the correct interface.
