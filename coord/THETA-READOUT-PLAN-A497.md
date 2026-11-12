# THETA-READOUT PLAN (A497, hull/det lane)

Status: A497/A498 rebuild plan. No LANA object is used. The deprecated theta readout
`thetaPilotLogImage T b := qPilotLogImage T b / (2*l.value)` is **withdrawn as a
Cor 3.12 reading**: it is, by definition, a function of q, and the derived
`qThetaReadout_ordered` / `qThetaStepXIContract.targetSigned := thetaSigned` /
`target_le_theta := rfl` are arithmetic identities, not paper content.
This file records the independent definitions and the exact remaining gap.

## 1. Independent definitions (target file `ThetaPilotIndependentReadoutActual.lean`)

### 1.1 q/hull readout (hull lane)
- local (literal bad place): `hullReadoutLocal T b := qPilotLogImage T b`
  = `localSignedLog (qVFamily T b) = Real.log ‖(qVFamily T b).q‖` (negative).
  Source: `Mzk1QPilotSHEDoubleImageActual.qPilotLogImage` (green).
- global (on the actual C3 input): `hullReadoutGlobal P := qPilotLogVolumeReading P`
  = `P.signedQPilotLogVolume = -|Real.log ‖P.line.C3.q.q‖|` (S3137, green).
  This is independent of any theta value.

### 1.2 Theta-pilot readout (hull lane)
- preferred: `thetaPilotReadout C3 := thetaPilotHullLogVolumeReal C3`
  = `Real.log ((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal`
  (S3137QThetaPilotLogVolumeReadingsActual / S3137ThetaHullVolumeScalingActual /
  AbsTopIII09ThetaHullScalingActual, all green).
  `thetaPilotHull C3 = actualHolomorphicHull C3 (actualUnitRegion C3) =
  actualC3LogShellTensorRegion C3` (proved: `thetaPilotHull_eq_region`), and the
  measure is the actual C3 tensor Haar `actualC3LogShellTensorHaar C3`.
- alternative (recorded, NOT used): `globalThetaPilotLogVolume T`
  (GlobalThetaPilotLogVolumeActual, green): the raw theta-value procession candidate
  `= (gaussExponentSum / card SignedLabel) * globalQPilotLogMagnitude`; it is a
  positive magnitude of raw `q_v^{j^2}` values, uses SignedLabel (cardinal l)
  instead of the source `Fl*` (cardinal l*), and has no hull; see
  `GlobalThetaPilotFormulaCorrection.md`. Hence it is a different normalization
  and cannot be substituted for the hull reading.

### 1.3 The inequality to be proved (named gap, not proved)
`ThetaHullComparison C3 P : Prop := hullReadoutGlobal P <= thetaPilotReadout C3`.
This is exactly the existing named candidate `qThetaPilotLogVolumeComparison C3 P`
(S3137QThetaPilotLogVolumeReadingsActual:145) and is the real Step (xi-f) content
on one actual C3 input. We restate it and mark it as the named gap; we do **not**
prove it and do not encode it via any q-derived theta reading.

## 2. What differs (normalization/measure audit)
1. **Objects**: q reading is the scalar signed log-volume `-|log q|` of the actual
   paper q-pilot object (clause-B/QPilot scalar identification); theta reading is the
   actual Haar log-volume of the C3 tensor log-shell hull container (C3LogShellTensorBlock).
   They live on the same C3 input but are not definitionally the same kind of measure.
2. **No 2l**: neither independent reading divides by `2l` or `2l*`. The deprecated
   `thetaPilotLogImage = qPilotLogImage/(2l)` introduced the 2l artificially; it must
   not be used.
3. **No sFactor / no weight sum**: both readings are single global quantities on one
   C3 input; `sFactor` and `f_w/[F:Q]`-weights belong to the LANA/global-q
   procession bookkeeping, not to these definitions.
4. **Hull**: the theta container is itself a lambda-O hull (`thetaPilotHull_eq_region`
   proves it equals the region), so the reading is a genuine hull log-volume; the q
   side is a scalar log-volume with no hull operation.

## 3. Consequence for the contract layer (A497 item ③/④)
- `Cor312Conclusion contract := contract.qSigned <= contract.thetaSigned` is weak by
  itself; `StepXIContract.targetSigned` must be an independent det-normalized
  intermediate quantity (hull+det stage output), never `:= thetaSigned`.
- The real content in our bridge is the two IUT IV comparisons of
  `Cor312ToABCBridgeInterface` (`hcomp`); those are the named gap and must not be
  filled by the q<=target<=theta chain.
- `Mzk1QPilotR4Stage5AlignActual.thetaPilotLogImage` and everything derived from it
  (`qThetaDetReadout`, `qThetaReadout_ordered`, `qThetaStepXIContract`,
  `step3115_comparison_proved` as Cor 3.12 evidence) is **deprecated as Cor 3.12
  evidence**; the file may remain for API compatibility but must not be cited as
  progress on Theorem 3.11/Cor 3.12.

## 4. Next executable step
1. `ThetaPilotIndependentReadoutActual.lean` (definitions + bridge equalities +
   named-gap Prop + partial provable facts).
2. Try to prove the gap from the actual C3 p-scaling/normalization laws
   (`S3137ThetaHullVolumeScalingActual`, `S3137C3LogShellPacketNormalizedLogVolumeActual`)
   or record precisely which normalization constant is missing.
