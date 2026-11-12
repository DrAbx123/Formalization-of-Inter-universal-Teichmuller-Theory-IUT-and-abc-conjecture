# S2810 — SourceImageRealizationLogShell hdeg

Date: 2026-11-07
Goal: supply the `hdeg` field of `SourceImageRealizationLogShell` so that
`S2600LogShellRealizationActual` / `S2601LogShellPortActual` can be produced
from `OriginalInput`.  Outcome: **precise blocker, actual counterexample**;
no hdeg construction from the present source data.

## 1. Exact type

From `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHull.lean`:

```lean
structure SourceImageRealization (v : V) where
  posRealAction : Multiplicative Real →* I.ValueMonoidAt 0 0 v
  degree_of_q :
    I.logDegreeAt 0 0 v
      (posRealAction (Multiplicative.ofAdd
        (Real.log ((I.theaterAt 0 0).thetaPacket.q)))) =
      Real.log ((I.theaterAt 0 0).thetaPacket.q)
```

where

```lean
def logDegreeAt (n m : Int) (v : V) (x : I.ValueMonoidAt n m v) : Real :=
  Multiplicative.toAdd ((I.primeStripAt n m).degree v x)
```

From `tmp/sheaf/xif/paper/S2600LogShellRealizationActual.lean`:

```lean
structure SourceImageRealizationLogShell (v : V)
    extends I.SourceImageRealization v where
  hdeg : forall b : Real,
    I.logDegreeAt 0 0 v (posRealAction (Multiplicative.ofAdd b)) = b
```

So the precise missing field is:

```lean
hdeg : ∀ b : ℝ,
  I.logDegreeAt 0 0 v
    (R.posRealAction (Multiplicative.ofAdd b)) = b
```

## 2. Consumers and their actual signatures

### S2600

```lean
theorem S2600_sourceLocalLogDegree_thetaPilotPoint
    (R : SourceImageRealizationLogShell I v)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    I.sourceLocalLogDegree v
        (I.sourceThetaPilotPoint v R.toSourceImageRealization n j) =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (I.thetaValueAt (n.val : Int) 0 j)
```

Uses `R.hdeg` via the lemma
`sourceLocalLogDegree_thetaPilotPoint` in
`SourceImageHull.lean`.

### S2601

```lean
variable (R : SourceImageRealizationLogShell I v)

theorem S2601_sourceLocalLogDegree (a n c : Nat) :
    I.sourceLocalLogDegree v
      (S2597Point I R.toSourceImageRealization (T := T) (b := b) a n c) =
      Real.log ‖S2588PointMap T b a n c‖
```

Both are actual conditional theorems; neither constructs `R`.

### S2718 — not the same object

`tmp/sheaf/xif/paper/S2718LogShellInterfaceActual.lean` gives the local
completion log-shell:

```lean
theorem S2718_completionLogShell_interface
    (place : NumberField.FinitePlace K) :
    IsCompact (completionLogShell place) ∧
      IsOpen (completionLogShell place) ∧
      (CompletionIntegers place ⊆ completionLogShell place) ∧
      (∀ u : (CompletionIntegers place)ˣ,
        completionUnitLog place u ∈ completionLogShell place) ∧
      (∀ z : ℤ_[(completionRationalPrime place).val],
        x ∈ completionLogShell place →
          padicCompletionHom place z * x ∈ completionLogShell place)
```

This is a Haar/compact-open/integral-scalar interface over
`Completion place`; it has no `posRealAction`, no `ValueMonoidAt`, and
therefore does **not** supply `hdeg`.

## 3. Reusable actual parts

- `SourceImageRealization` itself is actual as a structure and is used
  throughout Cor 3.12; its `degree_of_q` field is actual data.
- `sourceHaarActualImageRealization` in
  `LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceUnitRegionHaarDataActual.lean`
  is a genuine actual `SourceImageRealization` (constant positive-real action,
  `q = 1`).
- `S1666SourceImageRealization` packages that realization for the S1487
  faithful input.
- S2600/S2601 are actual conditional consumers; their proofs need only
  `R.hdeg`.
- `Cor312GapDictionaryLayer`, `Cor312CarrierRealizationSpec`,
  `CertificateHullWiring`, `CardHullRealEdgeNormalizationReduction` all take
  `hdeg` as an explicit hypothesis; none constructs it.

## 4. Exact blocker (actual theorem)

File:

```text
tmp/sheaf/xif/paper/S2810SourceImageHdegActual.lean
```

```lean
theorem S2810_hdeg_implies_degree_of_q
    (R : I.SourceImageRealization v)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    I.logDegreeAt 0 0 v
        (R.posRealAction (Multiplicative.ofAdd
          (Real.log ((I.theaterAt 0 0).thetaPacket.q)))) =
      Real.log ((I.theaterAt 0 0).thetaPacket.q)
```

This shows `hdeg` is strictly stronger than the only degree field
`degree_of_q`: it is degree faithfulness at **every** real `b`, while
`SourceImageRealization` only records `b = log q`.

The existing actual source-Haar realization has constant action
`b ↦ 1`; therefore:

```lean
theorem S2810_sourceHaarActual_logDegree_eq_zero
    (S : SourceDefinition31Data l) (b : Real) :
    (sourceHaarActualOriginalInput S).logDegreeAt 0 0 ()
        ((sourceHaarActualImageRealization S).posRealAction
          (Multiplicative.ofAdd b)) = 0
```

and the exact blocker:

```lean
theorem S2810_sourceHaarActual_hdeg_impossible
    (S : SourceDefinition31Data l) :
    ¬ (∀ b : Real,
      (sourceHaarActualOriginalInput S).logDegreeAt 0 0 ()
        ((sourceHaarActualImageRealization S).posRealAction
          (Multiplicative.ofAdd b)) = b)
```

Proof: `hdeg 1` would give `0 = 1`.  Axioms:
`[propext, Classical.choice, Quot.sound]`.

## 5. Why hdeg is not derivable from `OriginalInput`

The blocker is structural, not a missing calculation:

1. `SourceImageRealization` contains only `degree_of_q` (one b), not a
   degree-faithful section of `logDegreeAt`.
2. The actual source-Haar value monoid has nonpositive degree on every element:
   `sourceHaarActualDegree_nonpos`.  Its actual positive-real action is the
   constant `1`.  Hence hdeg fails for `b ≠ 0`, as proved above.
3. No other actual `SourceImageRealization` constructor exists in the tree.
   The `posRealAction` is an input; `OriginalInput` does not contain a
   canonical monoid section `Multiplicative ℝ →* I.ValueMonoidAt 0 0 v`
   whose `logDegreeAt` is the identity.
4. `S2718` lives on `Completion place`, not on the value monoid, so it cannot
   be transported to hdeg without a new comparison map.

## 6. What would actually close it

One of:

- **New value monoid/action**: build a genuine positive-real degree model
  `I.ValueMonoidAt 0 0 v` containing positive-degree elements and define
  `posRealAction (ofAdd b) := degree element b`, with a proved
  `logDegreeAt (posRealAction (ofAdd b)) = b`.
- **New source object**: extend `SourceImageRealization` with a
  degree-faithful section (not just hdeg restated): a map
  `s : Multiplicative ℝ →* I.ValueMonoidAt 0 0 v` plus
  `∀ b, I.logDegreeAt 0 0 v (s (ofAdd b)) = b`.
- **Explicit source theorem**: prove the above from an actual constructed
  `s`; hdeg alone as a hypothesis is already the S2600/S2601 interface and
  cannot be manufactured by proof search.

Do **not** add `hdeg` as an axiom or a fake `posRealAction`; the counterexample
above rules out the existing constant-action model.

## 7. Status

```text
S2810SourceImageHdegActual.lean
  src 2995 B
  SHA256 ebbc3153d57a5cbd1159d68145ee882a51c25c0d980f764b1f798fbad23fdf7b
  olean 35360 B
  SHA256 39e547ea0be4c04aed3f0a8d57534e58c0705dbcde0062c84344e57ac6e60ff2
  EXIT=0
  AXIOMS [propext, Classical.choice, Quot.sound]
```

Verdict: **hdeg cannot be constructed from present actual data**; first precise
blocker is the constant source-Haar action plus the one-point `degree_of_q`
field.  S2600/S2601 remain conditional consumers.
