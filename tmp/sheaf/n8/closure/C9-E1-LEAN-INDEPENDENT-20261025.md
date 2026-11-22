# C9 independent Lean mining: E1 and complete C

Task ID: task-369 / C9-E1-LEAN-INDEPENDENT-20261025. Owner: primespine. Date: 2026-10-25.
Consumer: n8-c9-output-region-source-route P6; SHEAF stage1.
Scope: uniform F_mod=Q rho=1; no mixed/E3; no arbitrary; no Lean/Project edits; only this file written.

## 0. Method

Read-only search of `D:/lean/LeanFormal/IUT` for:

- `BPS`, `zeroColumn`, `0-column`, `CompleteC`, `SourceAllowedOutput`, `P6`, `b273`, `12301`, `UniformB273`;
- `ThetaPilotPoint`, `ThetaPilotCarrier`, `sourceHolomorphicHull`, `LiteralArithmeticHullInterface`;
- `OriginalInput`, `SourceNativeInitialThetaData`, `SourceNativeInitialThetaExists`, `HodgeTheater`.

Exact grep counts in `LeanFormal/IUT`: `BPS` 0, `zeroColumn` 0, `0-column` 0, `CompleteC` 0, `SourceAllowedOutput` 0, `P6` 0, `b273` 0, `12301` 0, `UniformB273` 0. The 36 `E1` hits are IUT IV elementary estimates (Section1/ElementaryEstimates), not the C9 E1 statement.

## 1. Verdict

**Lean cannot prove E1 or construct a complete C, because the required global objects and even the E1 proposition are not declared.** The Lean corpus has local/source-interface layers and a value-monoid theta-pilot/hull object, but no global BPS/F^{⊩▶×mu}-prime-strip, no Theta-pilot 0-column/BPS gluing, no complete-C type, no b=273 specialization, no E1 type, and no target/TC/U273/arch declarations.

This is an exact declaration gap, not a hidden theorem. No Lean theorem or axiom states E1; absence of the type is not a mathematical no-go.

## 2. Relevant Lean declarations that do exist

### 2.1 Source input/tuple

- `LeanFormal/IUT/IUTI/InitialTheta/SourceInitialThetaData.lean`: `SourceInitialThetaData` arbitrary tuple with clauses A-F.
- `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean`: `SourceNativeInitialThetaData`, `SourceNativeInitialThetaExists`, and `sourceNativeInitialThetaExists_iff_packaged : SourceNativeInitialThetaExists l ↔ Nonempty (SourceNativeInitialThetaData l)`.
  No inhabitant/actual source C is constructed; the equivalence is a statement about existence, not a witness.

### 2.2 Hodge theater/prime-strip interface

- `LeanFormal/IUT/IUTI/HodgeTheater/HodgeTheaterCore.lean`: `HodgeTheater` = arithmetic data + `FPrimeStrip` + `FiniteThetaPacket`; `HodgeTheaterLink` has prime-strip equivalence and theta-packet alignment.
- `LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean`: `OriginalInput` = `SourceDefinition31Data` + `SourceHodgeTheaterFamily`; it gives `theaterAt`, links, and theta packets, but no BPS/0-column/target.

### 2.3 Theta-pilot value-monoid/hull layer

- `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHull.lean`:
  - `ThetaPilotCarrier := Fin (lStar l.value + 1)`;
  - `ThetaPilotPoint v := ThetaPilotCarrier × SignedLabel → Mon v`;
  - `SourceImageRealization`, `sourceThetaPilotPoint`, `possibleThetaPilotImageSet`, `sourceHolomorphicHull`, `sourceHullVolume`.
  This is a **value-monoid realization** of the theta-pilot/hull, built over an `OriginalInput`; it is not the global BPS/F^{⊩▶×mu} label/gluing, not the Theta-pilot 0-column, and it supplies no target column/arch.
- `CertificateHullWiring.lean`: `sourceThetaPilotFiniteHull`, `sourceRealHullVolume`, `sourceHullVolume_le_theta`; finite/local wiring, not global BPS.
- `SourceImageHull.lean:536-560`: `LiteralArithmeticHullInterface` and `literalHullInterface_impossible : ¬ Nonempty (LiteralArithmeticHullInterface P Scaling)`. The module itself records that the literal paper hull interface is contradictory from the hull form alone; the missing input is the compactness/log-volume source object. This is a local interface obstruction, not E1.

## 3. Exact declarations missing

To state and prove/refute E1 one needs, at minimum:

1. `GlobalBPS` / `FPrimeTimesMuPrimeStrip`: the global BPS F^{⊩▶×mu}-prime-strip with etale-like/value labels and gluing data.
2. `ThetaPilotZeroColumn` and `BPSGluing`: the Theta-pilot 0-column and its full poly-isomorphism gluing to the BPS.
3. `CompleteInitialThetaData` / `CompleteC`: a type binding the initial Theta-data, BPS, Theta-pilot, 0-column and target column.
4. `UniformB273Profile`: actual p=12301, e=41, b=273, qhat=pi^273v data and its E_546 specialization.
5. `E1 : Prop`: e.g. no admissible complete uniform C with b=273 (or no complete C at all), with the exact quantifiers and admissibility clauses.
6. Target/TC/arch declarations: `TargetHull`, `TC_A`..`TC_H`, `TC_S`, `U273`, `h_inf`/`archHull`, `Q_C`/`h_C`.
7. A witness/instance of `SourceNativeInitialThetaData` (or `OriginalInput`) for b=273; currently `SourceNativeInitialThetaExists` is only a Prop and no b=273 instance is constructed.

None of 1-7 exists in the frozen Lean corpus.

## 4. Consequence for E1/complete C

- **E1 cannot be proved in Lean**: there is no E1 declaration and no complete-C/BPS/0-column/target declarations to quantify over.
- **A complete C cannot be constructed in Lean**: `SourceInitialThetaData` and `OriginalInput` are structures/interfaces; no b=273 actual instance, no BPS/0-column, no target.
- The existing `literalHullInterface_impossible` is a no-go only for the literal value-monoid hull interface; it does not exclude the paper's compactness/log-volume source object and is not E1.
- The value-monoid `ThetaPilotPoint`/`sourceHolomorphicHull` layer is not the paper's global BPS/Theta-pilot target; it is a localization/carrier realization over an already-supplied `OriginalInput`.

## 5. Exact gap and next executable Lean work

The exact gap is a **declaration gap**:

    GlobalBPS + ThetaPilotZeroColumn + BPSGluing + CompleteInitialThetaData/CompleteC + UniformB273Profile + E1 + TargetHull/TC/U273/arch.

Once these are declared, E1 becomes a proposition and can be attacked by the existing local/global theorems. Until then, the only Lean-valid conclusion is the absence of the declarations, not an E1 proof or a complete-C construction.

## 6. Verdict

Independent Lean mining finds **no E1/complete-C/BPS/0-column/target declarations** and therefore no Lean proof of E1 or construction of a b=273 complete C. The exact gap is the missing global BPS/Theta-pilot/complete-C/target declaration layer; no arbitrary object is introduced.

target_accepted=false; complete C9/P6/ABC not proved; no mixed/E3 input used.
