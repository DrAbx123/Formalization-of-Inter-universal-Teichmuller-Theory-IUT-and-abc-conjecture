# S1210: KummerQuotientNontrivial for I.fLinkAt 1 0 1 1

Target (attempt):

```lean
∃ (v : V) (x : TimesMuQuotient ((I.fPrimeStripAt 1 0).Mon v)ˣ),
  (S1187.kummerIsoAt (I.fLinkAt 1 0 1 1) v).equiv x ≠ x
```

## Candidate actual q_v root/unit sources

- `PaperCompletionThetaValueActual.PaperQRootCard` / `paperQRoot`
  (`PaperCompletionThetaValueActual.lean:35-45`):
  a 2l-th root in `Completion ((nativeBadLift T).lift b)`.
  **This type is impossible**: `S342QVFamilyRootImpossibleActual` proves
  `¬ Nonempty (TwoLthRootData T b)` and `¬ Nonempty (QVFamilyTwoLRootCard ...)`
  because the qVFamily order is coprime to l.  `PaperCompletionThetaValueActual`
  itself is marked INVALID AS PAPER OBJECT for this reason.
- `S438QVFamilyKSideCandidateActual.KSideTwoLRootData`:
  root in the chosen K-completion; it is an exact missing structure
  (`KSideTwoLRootDataRequired := Nonempty ...`), not constructed.
- `ThetaFunctionLineBundleActual.ActualQThetaValueData`:
  actual values in `ℝˣ` (`value : SignedLabel → ℝˣ`, `qUnit : ℝˣ`).
  This is a real-unit theta-value family, not an element of
  `TimesMuQuotient ((FPrimeStrip.Mon v)ˣ)`, and no bridge is constructed.

## First missing witness

### Object

```text
kummerNontrivialWitness :
  Σ (v : V),
    { x : TimesMuQuotient ((I.fPrimeStripAt 1 0).Mon v)ˣ //
      (kummerIsoAt (I.fLinkAt 1 0 1 1) v).equiv x ≠ x }
```

Equivalently a unit `u : ((I.fPrimeStripAt 1 0).Mon v)ˣ` whose quotient class
`quotientMap u` is moved by the quotient equivalence.

### Quantifier

```text
there exists v : V and an actual unit x of the strip group at v
(not a torsion-different unit), with the S1187 equiv moving x.
```

### Consumer

```text
S1187.kummerIsoAt (I.fLinkAt 1 0 1 1)
  -> non-refl proof of the upperEnv Kummer iso
  -> S1195/S1200 upperEnv square
  -> iplAlgorithmicProvenanceCard.
```

## Why no Lean is written

All available actual q_v data are:

1. impossible completion 2l-roots (`S342`);
2. exact-missing K-side root structures (`S438`);
3. real-unit theta values (`ActualQThetaValueData`), with no map to the
   Hodge-theater strip monoid `FPrimeStrip.Mon v`;
4. `selfKummerLayer`/`refl` data, explicitly excluded.

None yields an actual element of `TimesMuQuotient ((Mon v)ˣ)` with a proved
nontrivial image.  Writing a `Nonempty`/Prop witness would be the weak wrapper
the task forbids.

## Exact minimum

```text
actualUnitAt : (v : V) → ((I.fPrimeStripAt 1 0).Mon v)ˣ
actualUnit_nontrivial :
  (kummerIsoAt (I.fLinkAt 1 0 1 1) v).equiv (quotientMap (actualUnitAt v))
    ≠ quotientMap (actualUnitAt v)
```

plus the source arithmetic identification of `actualUnitAt` with the q_v unit
(currently absent; S342 rules out the q_v^(1/2l) version of that identification).

Status: exact stop; no Lean file, no compile claim.
