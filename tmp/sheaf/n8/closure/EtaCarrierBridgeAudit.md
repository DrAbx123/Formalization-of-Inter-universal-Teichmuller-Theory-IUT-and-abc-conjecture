# EtaCarrierBridgeAudit

Date: 2026-10-24. Auditor: qside. Scope: audit only; no Lean target changed.

## 1. Carriers and their exact definitions

### NativeQCarrier (q side)

`EtaQIndependentAttempt.lean:48-49`

```lean
abbrev NativeQCarrier (X : N8NativeInput l) : Type _ :=
  Completion (nativeFPlaceOverBad X)
```

This is the completion at the native **F-place** `nativeFPlaceOverBad X`.

### F-place selected completion

`C3TensorTargetCorrection.lean:41-43`

```lean
noncomputable def nativeFPlaceAtPrime :
    FinitePlaceAtPrime X.S.arithmetic.F (nativePrime X) :=
  ⟨nativeFPlaceOverBad X, rfl⟩
```

and `CommonPrimeCompletion (nativeFPlaceAtPrime X)`.

Probe `_EtaCarrierDefEqProbe.lean` (SHA `290B18DBB58C482C02467617272412D7B4901F1BF3EFE33E96DB46FE74F2F855`)
compiled EXIT 0 and proves

```lean
example : CommonPrimeCompletion (nativeFPlaceAtPrime X) = NativeQCarrier X := rfl
```

so these two carriers are **definitionally equal** (same underlying F-place completion).

Production ring equivalence:

```lean
CommonPrimeCompletion (nativeFPlaceAtPrime X) ≃+* NativeQCarrier X
  := commonPrimeCompletionActualRingEquiv (nativeFPlaceAtPrime X)
```

is actual (`FinitePlaceCompletionPacketLogShell.lean:16-18`) and the probe
constructs it.  The production code also uses the definitional equality
directly: `C3TensorTargetCorrection.lean:56-57` casts `Completion
(nativeFPlaceOverBad X)` to `CommonPrimeCompletion (nativeFPlaceAtPrime X)`
by `rfl`.

### Fmod selected completion used by corrected S

`EtaIntegralStructureAtSelectedPlace.lean:51-66`

```lean
abbrev selectedBadPrime := (completionRationalPrime (badBasePlace X)).val
def selectedBadPlaceAtPrime : FinitePlaceAtPrime (K := Fmod) selectedBadPrime
abbrev SelectedCompletion (X) : Type := CommonPrimeCompletion (selectedBadPlaceAtPrime X)
```

This is the completion at the **Fmod base place** `badBasePlace X`, not at the
F-place `nativeFPlaceOverBad X`.  The probe confirms its definitional form:

```lean
example : SelectedCompletion X =
    CommonPrimeCompletion (selectedBadPlaceAtPrime X) := rfl
```

but **no** production ring equivalence

```lean
CommonPrimeCompletion (selectedBadPlaceAtPrime X) ≃+* NativeQCarrier X
```
is provided.  The rational primes coincide only because the F-place lies over
the Fmod base place; the fields and local degrees need not.

## 2. Consequence for qToShell

The current qToShell target (`EtaQIndependentAttempt.lean:62-69`) asks

```lean
(NativeQCarrier X)ˣ →* (NativeShell X).Units
```

where `NativeShell X = C2Native.nativeLocalShell X` is the Fmod base
completion (`C2Native.lean:73-76`).  Therefore it would require a map

F-completion units -> Fmod-completion shell units.

The production map between the completions goes the other way:
`completionMap (k := Fmod) (nativeFPlaceOverBad X)` maps the Fmod completion
into the F completion.  It is a ring hom, not a ring equivalence; no production
inverse or F-completion-to-Fmod unit map is exposed.

## 3. Actual qToShell path (selected F shell)

An actual path exists only after correcting the shell to the selected **F**
completion:

1. `CommonPrimeCompletion (nativeFPlaceAtPrime X) = NativeQCarrier X` by `rfl`;
2. production ring equivalence
   `commonPrimeCompletionActualRingEquiv (nativeFPlaceAtPrime X)`;
3. transport the native q unit through this equivalence;
4. use the production selected F shell
   `sourceLocalLogShellDatum (K := X.S.arithmetic.F) (p := nativePrime X)
     (nativeFPlaceAtPrime X)`.

The real-log value on the selected F shell is available only after the exact
integral-unit membership condition (the transported q unit is an integral unit
of the selected F shell).  That condition is the existing named gap
`NativeQSelectedUnitIntegral` style obligation; it is not supplied by the
carrier equivalence alone.

## 4. Exact obstruction for the Fmod S shell

A qToShell into `C2Native.nativeLocalShell` (Fmod shell) is not constructed:

- no ring equivalence between the Fmod selected completion and `NativeQCarrier`;
- only the partial `completionMap` Fmod -> F, with no inverse;
- the q unit lives on the F completion and is not shown integral at the Fmod
  completion;
- the corrected S `SelectedCompletion` is the Fmod base completion, so it cannot
  be substituted for `NativeQCarrier` by a definitional equality.

This is an exact obstruction, not a search failure.  The source object needed
for the original target is either

1. a production F-completion -> Fmod-completion unit transport (or Fmod shell
   at the native q's F place), or
2. a corrected qToShell/readout target on the selected F shell plus the exact
   integral-unit membership gap.

## 5. Interface replacement

- `EtaRssLogShellLine` uses the Fmod native bad shell
  (`C2Native.badPlaceAtPrime`), matching `C2Native.nativeLocalShell`; it does
  **not** match the selected F completion directly.
- `EtaRssSelectedPlaceBridge` compares volume indices between that Fmod shell
  and the corrected Fmod selected-place S; this is actual.
- A q-side bridge must use the F-completion selected shell and the production
  ring equivalence above; it cannot identify the Fmod S `SelectedCompletion`
  with `NativeQCarrier`.

## 6. Verdict

- F-place `CommonPrimeCompletion (nativeFPlaceAtPrime X)` vs `NativeQCarrier`:**definitionally equal**; production ring equivalence available.
- Fmod corrected-S `SelectedCompletion` vs `NativeQCarrier`:**not definitionally equal**; no production ring equivalence; only `completionMap` Fmod -> F.
- No arbitrary map is introduced by this audit.

Evidence hashes:

- `_EtaCarrierDefEqProbe.lean`: `290B18DBB58C482C02467617272412D7B4901F1BF3EFE33E96DB46FE74F2F855`
- `EtaQIndependentAttempt.lean`: `CF8D694FB5FC40B6317F7A9789E0EAC38505D035409187AEED0D890CFBC5FBE6`
- `EtaIntegralStructureAtSelectedPlace.lean`: `16A20BB72062DFE7749E620BB4503833939992D80FBA70B71E684DB2643B71B6`
- `EtaRssLogShellLine.lean`: `A4D7B94828CE64D50471E217C069C165CEEDE1766EB8CBAD0C9F62DA35E7C6C0`