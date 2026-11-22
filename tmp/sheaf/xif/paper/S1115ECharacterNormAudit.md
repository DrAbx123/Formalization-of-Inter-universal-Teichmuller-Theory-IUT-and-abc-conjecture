# S1115: E character / norm formula audit (S885, S892, S897, S903)

Date: 2026-10-30.  Scope: does the tree contain an **actual** proof of the E
character/norm formula, and what is the exact minimal remaining list?  No S109x
work rerun.

## Verdict

**No actual proof of the E character/norm formula exists.**  All four files are
conditional reductions; the terminal analytic object is still the factor-norm
formula / E character comparison at dQp.

## File-by-file

### S885RootStackUniformizerNormActual
- Bundles exact input `S885UniformizerData`:
  - `pi : (rootStackExtension T b)^×`
  - `pi_norm_lt_one : ‖pi‖ < 1`
  - `unit_factor_one : S885UnitFactorOne`
  - `decomposition : S885UnitDecomposition pi`
  - `uniformizer_factor : S885UniformizerFactor pi`
  - `factor_norm_pow : RootStackHaarFactorNormPow dQpFactor`
- From it constructs S878's `RootStackUniformizerNormData`.
- **Not proved**: existence of the DVR uniformizer, the unit decomposition,
  the unit-factor-one identity, the uniformizer-factor formula, and the
  factor-norm formula.  `S885RootStackCharacterNormExactGoal` is exactly
  `RootStackHaarFactorNormPow dQpFactor`.
- **Circularity warning**: the last field of `S885UniformizerData` is the
  factor-norm target itself.  S897/S903 using this data are therefore
  reductions to the target, not derivations of it.

### S892RootStackGeneralNormFormulaActual
- Actual: `rootStackNormExtensionFormula_actual` (E norm extension for units),
  `finrankL_eq_dK_mul_dLK`, and S861L `rootNormedCharacterNormComparison_actual`
  via S865.
- Conditional: `rootStackGeneralNormFormula_of_ECharacter` needs
  `RootStackCharacterNormComparisonAtDQp`.
- `RootStackGeneralNormFormulaExactGoal` is exactly that E comparison.
- So S892 reduces the general norm formula to the E character comparison; the
  E side is not proved.

### S897ECharacterNormViaUniformizerActual
- `rootStackCharacterNormComparisonAtDQp_of_factorNormPow`:
  exact factor-norm formula → E comparison.
- `rootStackCharacterNormComparisonAtDQp_of_uniformizerData`: uses the
  `factor_norm_pow` field of S885 data; again the target is an input.
- `S897ECharacterNormExactInput := S885UniformizerDataRequired`.

### S903ECharacterNormLightActual
- `S903ECharacterNormExactInput := RootStackHaarFactorNormPow dQpFactor`.
- `s903_hchar_of_exactInput` and `s903_hchar_of_uniformizerData` are the same
  conditional reduction; no new actual theorem.
- `S903EUniformizerExactDataRequired := S885UniformizerDataRequired`.

## Exact minimal remaining list (non-circular)

1. **DVR/uniformizer datum on E = rootStackExtension**
   - a uniformizer `pi` with `‖pi‖ < 1`;
   - every unit `u = eps * pi^n` with `‖eps‖ = 1`.
2. **Unit-factor identity**
   `∀ u, ‖u‖ = 1 → rootStackHaarFactor u = 1`.
   This is the norm-one invariance of the root-stack Haar factor.
3. **Uniformizer-factor identity**
   `rootStackHaarFactor pi = ofReal (‖pi‖ ^ dQpFactor)`.
   This is the actual determinant/Haar-scaling computation on the finite root
   stack (S831/S878/S887 chain); it is the core missing analytic step.
4. **Factor-norm formula**
   `RootStackHaarFactorNormPow dQpFactor`
   equivalently `RootStackCharacterNormComparisonAtDQp` (S892/S897/S903 goal).
5. **General norm formula**
   follows from 4 via S892's actual L character + norm extension; no extra
   analytic input once 4 is proved.

Equivalently, the shortest exact target is:

```text
RootStackHaarFactorNormPow (dQpFactor)
  ⇔ RootStackCharacterNormComparisonAtDQp
```

with the non-circular DVR/unit-factor/uniformizer-factor data (items 1–3) as the
route to it.

## What has not been done

- No actual construction of `pi` or the DVR decomposition.
- No actual proof of `S885UnitFactorOne`.
- No actual proof of `S885UniformizerFactor`.
- No actual proof of `RootStackHaarFactorNormPow dQpFactor`.
- No actual E comparison `RootStackCharacterNormComparisonAtDQp`.
- S885/S897/S903 do not remove the target from their hypotheses; S885 includes
  it as `factor_norm_pow`.

## Suggested next executable step

Prove `S885UnitFactorOne` and `S885UniformizerFactor` for an explicit pi in
`rootStackExtension` (likely a p-uniformizer in each finite factor), then
combine with S831/S878's finite-stack Haar scaling to obtain
`RootStackHaarFactorNormPow dQpFactor`.  Do not add `factor_norm_pow` as an
input to that route.
