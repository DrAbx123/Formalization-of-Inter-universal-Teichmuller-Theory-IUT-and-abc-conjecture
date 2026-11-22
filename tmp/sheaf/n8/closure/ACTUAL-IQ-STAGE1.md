# N8 actual-IQ closure stage-1 record (2026-10-23)

## C0 TargetSignature
- Object: `N8TargetInput` = `OriginalInput l V`; `N8TargetOutput` = C1 place + actual `SourceTheorem311Realization` + actual source hull/q fields.
- Consumer: C10 `N8FullOutput.base`.
- Deps: `OriginalInput`, `SourceTheorem311Realization`, `SourceImageHullVolume`.
- NL proof responsibility: C1-C9 supply the full output; C0 only freezes roles.
- Gap: `n8_targetOutput_nonempty` named sorry; base target omits IPL/SHE/APT/degree fields (they live in C10 full output).

## C1 SourceInputBinding
- Object: actual place equivalence/selected v/R/fiber value-group comparison; `SourceInputBinding` only place.
- Consumer: C2, C3, C7, C10.
- Deps: `OriginalInput`, `NumberFieldPlaceIndex`, `finitePlaceValueGroup`/`archimedeanValueGroup`.
- NL proof: construct V ≃ NumberFieldPlaceIndex, selected v/R, fiber monoid equivalences.
- Gap: `sourceInputBinding_nonempty` named sorry.

## C2 SourceLogKummerRealization
- Object: finite-place actual unit log, kernel=torsion, log-shell/pre-log-shell equalities.
- Consumer: C4/C5/C9/C10.
- Deps: `sourceLocalLogShellDatum`, `IntegralUnitLogarithmKernel`.
- NL proof: unfold actual log-shell, kernel/log-shell/range equalities.
- Gap: `sourceLogKummerData_nonempty`; G_v action/Kummer/K1K2/archimedean still named gaps.

## C3 SourcePilotRegion
- Object: actual q in completion, theta packet, Kummer class/root change, tensor landing q.
- Consumer: C4/C7/C9/C10.
- Deps: `FiniteThetaPacket`, `FinitePlaceQCandidate`, `ArithmeticTensorTupleBlock`.
- NL proof: qUnit/candidate, roots, tensorLanding_q.
- Gap: `sourcePilotRegion_nonempty`; source q Real vs completion identification open.

## C4 SourceWitnessedOutput
- Object: actual value-monoid witness layer (place/pilot/Ind action data), U/Witness.
- Consumer: independent source witness layer; C7 does not use its U (uses T11).
- Deps: `SourceImageHull`, `ThetaPilotPoint`.
- NL proof: define U as range of eval with Sigma witnesses.
- Gap: Group label correction pending; no named sorry.

## C5 SourceAlgorithmCompatibility
- Object: actual IPLFamilyData field, SHE square, APT algorithm/transport, permitted/pilot labels.
- Consumer: C7, C10.
- Deps: `IPLFamilyData`, `SourceSHETransportLaws`, `APT`.
- NL proof: shared C4 output, operation correspondence.
- Gap: `sourceAlgorithmCompatibility_nonempty`; SHE/APT actual operation construction still sorry/gap.

## T10 IPLFamilyData
- Object: actual `FPrimeStrip` source/target, permitted `FPrimeStripEquiv` family, allowed relation.
- Consumer: C5/C10.
- Deps: `FPrimeStrip`, `FPrimeStripEquiv`, `SourceAdjacentColumnProcessionIsomorphism`.
- NL proof: permitted family/allowed relation by φ.isoMon.
- Gap: `iplFamilyData_nonempty` named sorry.

## C6 C6ActualIQData
- Object: actual `ArithmeticTensorTupleBlock`, canonical hull, `IQHullLogVolumeInterface`, Haar/degree-normalized readouts.
- Consumer: C7/C8/C9/C10.
- Deps: `FinitePlaceIQHullInterface`, `FinitePlaceIQHullSignedLogVolume`, `FinitePlaceNormalizedUnitScalingLogVolume`.
- NL proof: actual constructor using production donors.
- Gap: no named sorry in C6; product/field equivalence not needed here.

## T11 SourceThetaToIQ
- Object: actual theta scale `I.thetaValueAt n 0 j`, `SourceThetaIQInterface` with thetaCompletion/thetaImage; qPilotPoint from C3 q landing.
- Consumer: C7/C8/C9/C10.
- Deps: `I.thetaValueAt`, `C3.tensorLanding`, `C6IQCarrier`.
- NL proof: theta image as tensorLanding of completion; qPilotPoint from q.
- Gap: `sourceThetaIQObligation` named sorry; actual Real theta→completion map missing. This is the central source gap.

## C7 SourceHolomorphicHull
- Object: actual IQ carrier hull family `SourceHolomorphicHullData (T) (n)`; contains T11 image, qPilot, finite positive IQ log-volume.
- Consumer: C8/C9/C10.
- Deps: `C6ActualIQData`, `SourceThetaToIQ`, C5 permitted.
- NL proof: canonical hull contains image and qPilot; use B.iqInterface laws.
- Gap: `sourceHolomorphicHullData_nonempty` named sorry.

## C8 SourceDegreeComparisonIQ
- Object: actual IQ `iqDegree`/`iqMuLog`/`iqHullLogVolume`; equality on C7 hull with T/n/H.
- Consumer: C9/C10.
- Deps: C7, C6.
- NL proof: normalized log-volume equals IQ μlog on canonical hull.
- Gap: `sourceDegreeComparisonIQ` named sorry.

## C9 SourcePilotApproximationIQ
- Object: Values over n/C7, actual_values_bounded, actual_q_approximated.
- Consumer: C10.
- Deps: C8IQ, C7.
- NL proof: Values range; epsilon derivation.
- Gap: `sourcePilotApproximationIQ_stage2` named sorry; source q Real readout still missing (uses iqDegreeAt).

## C10 N8Closure
- Object: actual `N8FullOutput` assembled from C1-C9; no C10 sorry.
- Consumer: downstream Cor312/ABC interface (not wired).
- Deps: all above + C0 base.
- NL proof: construct structure, call C8/C9 named-sorry theorems, C0 base.
- Gap: C10 itself no sorry; dependency closure only; downstream consumers not tested.
