# P7 #8 CONTRACT — 7 missing rows inhabitant audit

Date: 2026-11-13. Owner: stepxi. Source list: coord/P7-CONTRACT-MAP.md §2.
Lean witness file: tmp/sheaf/xif/paper/Mzk1P7MissingRowsWitnessActual.lean
(pending watchdog).  Status: rows 2 and 7 have actual inhabitants; rows
1,3,4,5,6 have exact obstructions.

| # | missing item | status | witness / exact obstruction |
|---|---|---|---|
| 1 | general qThetaPilotLogVolumeComparison | **GAP** | Interface `GeneralQThetaComparison qRead θRead := qRead ≤ θRead`; actual data are `qPilotLogVolumeReading P` and `thetaPilotHullLogVolumeReal C3`. The required inequality is exactly `qThetaPilotLogVolumeComparison C3 P`, which is not proved; no actual inhabitant. |
| 2 | paper carrier IQ realization | **CONSTRUCTED** | `paperIQCarrierData_actual C3` with `carrier := actualC3LogShellTensorIQ C3`, `carrier_eq := rfl`; theorem `paperIQCarrierData_nonempty`. This is actual C3 Q-span data, not a toy. |
| 3 | (Ob3-3) source identification | **GAP (only reflexive)** | `Ob33SourceIdentification detTheta thetaActual := (detTheta = thetaActual)`; only the reflexive `ob33_interface_weighted_eq_self` exists. The actual det(x)M output arithmetic degree = normalized log-volume equality is not constructed. |
| 4 | multiradial (xi-e)/(xi-f) production | **PARTIAL** | finite Q(i)-at-5 production (`finiteMultiradialAlgorithmDischarge`) and general conditional bridge/finite witness exist; actual production and output types (`n,oR_LGP`, procession/log-Kummer/IPL-SHE-APT) missing. No actual inhabitant. |
| 5 | theta raw Haar vs paper normalized V | **GAP** | Interface `ThetaVFactorIdentification raw dim paperV := (raw = dim * paperV)`. Actual paper normalized V/`C3S1902TransportData` (blockEquiv/region_eq/haarScale) has no inhabitant; only named-input consumers exist. |
| 6 | StepXIContract fields/linkage | **IMPOSSIBLE (proved false)** | `ContractFieldsLinked` is refuted by `linkage_not_linked`; all three contract fields have `evidence = none`. Thus no inhabitant exists; this is a true gap, not an accidental missing value. |
| 7 | exact hull volume upper bound | **CONSTRUCTED with explicit C0; paper C0=0 GAP** | `hullUpperBound_actual M E` proves `HullUpperBound (rootExtensionProductNormalizedLog T (s1902Hull T)) l d f ((5/4)(log d + log f))` from `normalizedLog_hull_le_paperBox`. It is a real inhabitant of the interface but uses C0=(5/4)(logd+logf), not the paper exact C0=0, and it is the raw normalized hull, not paper normalized V. |

## Conclusion

- Actual inhabitants: #2 (IQ carrier data), #7 (hull bound with explicit
  non-paper C0).
- Exact obstructions: #1 (unproved comparison), #3 (actual det identification
  absent), #4 (actual multiradial production absent), #5 (paper V transport
  absent), #6 (contract fields provably unlinked).
- GAP-P7-CONTRACT remains CONDITIONAL/INTERFACE; no row is falsely marked
  DISCHARGED.  No axiom/sorry/toy object used.

End of 7-row status.