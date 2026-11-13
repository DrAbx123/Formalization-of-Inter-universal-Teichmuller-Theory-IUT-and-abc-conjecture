# A8-LABEL-PROBE — canonical `Bad -> SignedLabel` / theta label

Status: read-only probe (2026-11-14). No lake/lean run, no Lean source or
watchdog changes. All declarations below were checked by reading the cited
files; nothing here is compile evidence.

## 0. Verdict

- **No paper-faithful canonical map** `Bad (nativePlaceSelection T) -> SignedLabel
  l.value` (or `-> ProcessionLabel l`, or `-> ThetaLabel`) is derivable from the
  current source. The source has no bad-place label in `F_l^x` / `SignedLabel`;
  the only label attached to a bad place is its **residue characteristic**, a
  `Nat`.
- **A residue-characteristic function of the requested type does exist** and is
  canonical in the weak sense (only the residue class of the prime is used):
  see §5.1 (`SignedLabel`) and §5.2 (`ProcessionLabel`, using Clause B for
  nonvanishing). These are residue projections, **not** the paper theta-label
  identification; the tree itself says so
  (`tmp/sheaf/xif/paper/Mzk1PaperLabelProjectionActual.lean:16-18,54-56`).
- **First missing datum**: a source field
  `labelOf : Bad (nativePlaceSelection T) -> ProcessionLabel l`
  (equivalently a `SignedLabel`/`ThetaLabel` labeling). It is absent from
  `InitialThetaArithmeticData` (`LeanFormal/IUT/IUTI/InitialTheta/ArithmeticData.lean:62-81`),
  `SourceSignQuotientData` (`.../SourceDefinition31Quantifiers.lean:578-631`),
  `SourcePlaceSelection` (`.../SourcePlaceSelection.lean:31-37`), and clauses
  A-F (`.../SourceDefinition31Quantifiers.lean:889,959,1007,1106,1432,1543`).
  The only label in the formal Definition 3.1 contract is
  `SourcePlacePartition.badLabel : Bad -> Nat`
  (`.../SourceDefinition31Boundary.lean:44`), which is
  `badResidueLabel = residueCharacteristic`
  (`.../SourcePlacePartitionReduction.lean:603-604`).
- The paper's labels are **capsule positions** `S_{j+1} = {0,...,j}` with
  arbitrary permutation automorphisms
  (`tmp/sheaf/n8/closure/LabelData.lean:5-10,25-46`;
  `Iut/Concrete/ThetaRegion.lean:31-36,47-48`), not a per-bad-prime label.
  Bad places occur as a tuple `(v_l)_{l in S_{j+1}}` (label -> place); an
  inverse place -> label map is extra data.

## 1. Target types: "theta label" is ambiguous

| type | definition | card | source |
|---|---|---|---|
| `SignedLabel l.value` | `{j : Int // -(lStar) <= j ∧ j <= lStar}` | `l` | `LeanFormal/IUT/Foundations/Theta/GaussianKernel.lean:94-95`; `SignedLabelEquiv.lean:141-146` |
| `ProcessionLabel l` | `(ZMod l.value)^x` = `F_l^x` | `l-1` | `tmp/sheaf/xif/paper/ProcessionNormalizationWeightsActual.lean:78-79` |
| `ThetaLabel` / `PaperThetaLabel` | `{j : SignedLabel // 0 < j.1}` = positive `1,...,l*` | `l*` | `tmp/sheaf/xif/paper/PaperC3ThetaRootActual.lean:82`; `PaperSymbolTypesActual.lean:52-54` |
| `Fin (lStar l.value)` (paper index) | `PaperThetaLabel := Fin (lStar)` | `l*` | `tmp/sheaf/xif/paper/S694ThetaAverageNormalizationActual.lean:25` |

Existing conversions:

- `SignedLabel.equiv : SignedLabel l.value ≃ Fl l.value`
  (`SignedLabelEquiv.lean:75-82`);
  `SignedLabel.representative : Fl l.value -> SignedLabel l.value` is total
  (`SignedLabelEquiv.lean:48-62`).
- `processionSignedLabel : ProcessionLabel l -> SignedLabel l.value :=
  SignedLabel.representative l (x : Fl l.value)`
  (`tmp/sheaf/xif/paper/S640PaperRootThetaProcessionActual.lean:42-43`).
- `thetaLabelToSigned : ThetaLabel -> SignedLabel`, injective but not
  surjective (`PaperC3ThetaRootActual.lean:85-91`).
- `thetaLabelOfFin : Fin (lStar l.value) -> SignedLabel l.value`, `i |-> i`
  (`tmp/sheaf/xif/paper/MultiradialProcessionActual.lean:120-127`). Its image is
  `{0,...,l*-1}`, **not** the paper positive labels `{1,...,l*}`.
- `s1930PositiveLabel : Fin (lStar l.value) -> SignedLabel l.value`, `i |-> i+1`
  (`tmp/sheaf/xif/paper/S1930CompareA0AverageActual.lean:125-132`), with
  `s1930PositiveLabel_surjective` (lines 153-171); same convention as
  `paperThetaPositiveLabel` (`S703GlobalPaperThetaComparisonActual.lean:29-38`).

Consequences:

- `SignedLabel` has `l` elements and distinguishes `j` from `-j`. The paper's
  theta values depend on `j^2` and use the `l*` sign-identified labels.
  `PAPER_OBJECT_SPEC.md:47` explicitly forbids "all `SignedLabel` rather than
  `ThetaLabel` for theta labels"; `PaperSymbolTypesActual.lean:9-11` says the
  theta labels are the positive representatives `j=1,...,l*`, not all
  `SignedLabel`.
- Therefore a map `Bad -> SignedLabel` is **not automatically a theta label**.
  For a paper-positive label the codomain should be `ThetaLabel` (or
  `Fin (lStar)` with the `i |-> i+1` convention), and `thetaLabelOfFin` must
  not be used as the final positive-label encoding.

## 2. Source-side data attached to a bad place

- `Bad (P) := {p : FinitePlace A.Fmod // p in P.V_mod_bad}`
  (`LeanFormal/IUT/IUTI/InitialTheta/SourcePlacePartitionReduction.lean:188-189`).
- `nativePlaceSelection T` has `V_mod_bad := T.tuple.source.V_mod_bad`
  (`LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31NativeContractBridgeReduction.lean:108-114`).
- `badResidueLabel P b = residueCharacteristic b.1 : Nat`
  (`SourcePlacePartitionReduction.lean:603-604`); `badStripLabel` maps it to
  `RationalPrimePlace` (lines 633-635).
- `badRationalPrime T b =
  rationalPrimeOfFinitePlace K ((nativeBadToKPlace T b).maximalIdeal)`
  (`tmp/sheaf/xif/paper/Mzk1PaperLabelBadIndexBridgeActual.lean:34-35`).
  `nativeBadToKPlace` is a `Classical.choose` from lying-over
  (`tmp/sheaf/xif/paper/VbadPlaceIndexingActual.lean:74-77`), but its value is
  the same for every lift: it equals `residueCharacteristic b.1` (§4.1).
- The F-side lift `nativeBadToFPlace T b : FinitePlace T.arithmetic.F` has
  `comap (nativeBadToFPlace T b) = b.1`
  (`VbadPlaceIndexingActual.lean:46-55`). This is the lift used with Clause B.
- Clause B gives coprimality of the residue characteristic with `l`:
  `SourceClauseB.residue_characteristic_prime_to_l`
  (`SourceDefinition31Quantifiers.lean:970-975`).
- No field of type `Bad -> ProcessionLabel`, `Bad -> SignedLabel`, or
  `Bad -> ThetaLabel` exists anywhere in the source tree (search below).

## 3. Existing `Bad -> label` interfaces and maps (search result)

- `BadThetaLabelMap` (`Mzk1PaperLabelBadIndexBridgeActual.lean:48-51`):
  `labelOf : Bad (nativePlaceSelection T) -> PaperLabelGroup l`.
  Only the structure; **no instance/inhabitant** is constructed.
- `PaperLabelProjectionInterface`
  (`Mzk1PaperLabelProjectionActual.lean:67-72`):
  `labelOf : HeightOneSpectrum -> PaperLabelGroup l`. No instance.
- `candidateLabelOfPlace`
  (`Mzk1PaperLabelProjectionActual.lean:57-65`): from a finite place with
  nonzero rational-prime residue mod `l` to `(ZMod l)^x`. The file explicitly
  says this is a residue-prime construction, "not the paper theta-label
  identification" (lines 16-18, 54-56).
- `LabelToSignedLabelBridge.labelEquiv`
  (`tmp/sheaf/n8/closure/LabelToSignedLabelBridge.lean:28-32`): an arbitrary
  `Fintype.equivOfCardEq` from a `ProcessionLabelData` label set to
  `SignedLabel`; the header says "arbitrary equivalence, not a group
  isomorphism" (lines 4-7). Not `Bad`-indexed and not canonical.
- **No declaration of type** `Bad (nativePlaceSelection T) -> SignedLabel
  l.value`, `-> ProcessionLabel l`, or `-> ThetaLabel` was found. The many
  fields `thetaValue : Bad -> SignedLabel -> Real` (e.g.
  `GlobalThetaPilotPossibleImageGeometryActual.lean:64`) take a label as an
  argument; they are not label assignments.

## 4. Can `badRationalPrime b` be reduced mod `l` / mapped to `Fin (lStar)`?

### 4.1 Exact bridge: `badRationalPrime = residueCharacteristic b.1`

Mathlib `Ideal.ringChar_quot`
(`.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Int.lean:106-110`):

```lean
theorem _root_.Ideal.ringChar_quot {S : Type*} [CommRing S] (I : Ideal S) :
    ringChar (S ⧸ I) = absNorm (under ℤ I)
```

Since `residueCharacteristic place = ringChar (RingOfIntegers K ⧸ I)` and
`rationalPrimeOfFinitePlace K v = absNorm (v.asIdeal.under Int)`, the bridge is

```lean
theorem badRationalPrime_eq_residueCharacteristic
    (b : Bad (nativePlaceSelection T)) :
    badRationalPrime T b =
      NumberFieldFinitePlace.residueCharacteristic b.1
```

Proof ingredients: `badRationalPrime` and `rationalPrimeOfFinitePlace_eq`
(`Mzk1PaperLabelProjectionActual.lean:44-47`) for the left side;
`← Ideal.ringChar_quot` for
`residueCharacteristic (nativeBadToKPlace T b)`;
`residueCharacteristic_comap`
(`SourcePlacePartitionReduction.lean:115-117`) and
`nativeBadToKPlace_comap` (`VbadPlaceIndexingActual.lean:80-85`) to replace
the K-place by `b.1`. This lemma is **not** in the tree; it is the only
nontrivial bridge needed for the residue route, and it needs no new source
input.

### 4.2 Mod `l`: total. Unit: needs Clause B. `Fin (lStar)`: needs nonzero + ± convention

- `(badRationalPrime T b : ZMod l.value)` is total and canonical; no
  coprimality is needed.
- `((residueCharacteristic b.1 : Nat) : ZMod l.value) != 0` follows from
  Clause B:
  1. `h := T.clauseB.residue_characteristic_prime_to_l (nativeBadToFPlace T b) hp`
     with `hp` from `rw [nativeBadToFPlace_comap]; exact b.2`;
  2. rewrite `residueCharacteristic_comap` and `nativeBadToFPlace_comap` in
     `h`; get `Nat.Coprime l.value (residueCharacteristic b.1)`;
  3. `Nat.Coprime` gives `not l.value ∣ residueCharacteristic b.1`, and
     `ZMod.natCast_eq_zero_iff` gives the nonzero residue.
- `Fin (lStar)` from `x : ZMod l.value` with `x != 0`: the canonical
  ±-class representative is
  `s := min x.val (l.value - x.val) : Nat`, which lies in `{1,...,l*}`.
  Then `⟨s - 1, _⟩ : Fin (lStar l.value)`.
  Obligations: `1 <= s` and `s <= lStar l.value`, from `ZMod.val_lt`,
  `x.val != 0`, `lStar = (l-1)/2`, and `omega`. **No such definition
  exists in the tree yet.**
- No total **injective** map `ZMod l -> Fin (lStar)` exists (pigeonhole,
  `l > l*`). `x = 0` (i.e. `p = l`) has no ± class; Clause B excludes it
  for actual bad places, but a map without the nonzero proof must assign
  something to 0 (e.g. 0), which is not a theta label.
- The ±-class construction is canonical in the precise sense that it uses
  `min(val, l-val)`, not an arbitrary `Fintype.equivFinOfCardEq` /
  `labelEquiv`.

## 5. Constructions (exact Lean types and proof obligations; not compiled)

### 5.1 Total `SignedLabel` residue map (no obligations)

```lean
noncomputable def badResidueSignedLabel
    (b : Bad (nativePlaceSelection T)) : SignedLabel l.value :=
  SignedLabel.representative l
    ((NumberFieldFinitePlace.residueCharacteristic b.1 : Nat) : ZMod l.value)
```

- Type: `Bad (nativePlaceSelection T) -> SignedLabel l.value`.
- Proof obligations: none.
- Caveats: may return `0` (`p = l`) or a negative representative; retains
  the sign; it is a residue projection, not the paper theta label. It is
  choice-free (uses `b.1` directly, not `nativeBadToKPlace`).

### 5.2 Unit-valued `ProcessionLabel` map (needs Clause B)

```lean
noncomputable def badResidueLabelUnit
    (b : Bad (nativePlaceSelection T)) : ProcessionLabel l := by
  classical
  haveI : Fact (Nat.Prime l.value) := l.factPrime
  refine Units.mk0
    ((NumberFieldFinitePlace.residueCharacteristic b.1 : Nat) : ZMod l.value) ?_
  -- goal: ((residueCharacteristic b.1 : Nat) : ZMod l.value) != 0
```

Obligations:

1. `badRationalPrime_eq_residueCharacteristic` (§4.1), if the route is stated
   via `badRationalPrime`.
2. `Nat.Coprime l.value (residueCharacteristic b.1)` from
   `T.clauseB.residue_characteristic_prime_to_l` at
   `nativeBadToFPlace T b`, plus `nativeBadToFPlace_comap` and
   `residueCharacteristic_comap`.
3. `not l.value ∣ residueCharacteristic b.1`, hence the `ZMod` residue is
   nonzero (`ZMod.natCast_eq_zero_iff`).

Then

```lean
noncomputable def badResidueSignedLabelUnit
    (b : Bad (nativePlaceSelection T)) : SignedLabel l.value :=
  processionSignedLabel (l := l) (badResidueLabelUnit T b)
```

This is the strongest "canonical actual function of the literal requested type"
that the source supports. It is still the residue-characteristic map.

### 5.3 Positive `ThetaLabel` map (needs nonzero and `i |-> i+1`)

```lean
noncomputable def badResidueFinLabel
    (b : Bad (nativePlaceSelection T)) : Fin (lStar l.value) := ...
  -- let x : ZMod l.value := (residueCharacteristic b.1 : Nat)
  -- let s := min x.val (l.value - x.val)
  -- exact ⟨s - 1, _⟩

noncomputable def badResidueThetaLabel
    (b : Bad (nativePlaceSelection T)) : ThetaLabel (l := l) :=
  ⟨s1930PositiveLabel l (badResidueFinLabel T b),
    s1930PositiveLabel_pos l (badResidueFinLabel T b)⟩
```

Obligations: `x != 0` (§5.2), `1 <= s`, `s <= lStar`.
This lands in the positive labels `1,...,l*`; unlike `thetaLabelOfFin` it
does not include 0 or miss `l*`.

## 6. Why this is not the paper theta label (exact obstruction)

1. **Source absence.** No label field: see §0 and §2. The only bad label is
   `residueCharacteristic : Nat`. The paper's labels are capsule positions
   with arbitrary permutation automorphisms (`LabelData.lean:5-10,25-46`;
   `ThetaRegion.lean:31-36,47-48`), and the bad places enter as a tuple
   `(v_l)` indexed by labels. The inverse place -> label map is not part of
   the source; it is an external labeling/identification.
2. **Non-injectivity.** The residue route factors through
   `residueCharacteristic b.1 : Nat`; two bad primes with the same residue
   mod `l` get the same label. It cannot be a faithful per-place labeling.
   `S3097SourceBadLabelInjectiveActual.lean:56-93` proves injectivity only in
   a concrete two-place example (primes 5 and 2161), using the residue
   characteristics themselves; that is not a general canonical labeling.
3. **Cardinality.** `Bad` has only `[Fintype (Bad ...)]` as a hypothesis
   (e.g. `Mzk1PaperLabelBadIndexBridgeActual.lean:31`), and
   `SourcePlaceSelection` only requires nonempty. There is no source equality
   `card Bad = l` or `= l*`. A bijective `Bad -> SignedLabel` /
   `Bad -> Fin (lStar)` (an actual labeling) would force such an equality,
   which is not available and can fail.
4. **The existing interface is exactly the missing datum.** `BadThetaLabelMap`
   is the structure whose inhabitant would be the map; nothing inhabits it.
   The file comment (`Mzk1PaperLabelBadIndexBridgeActual.lean:11-14`) already
   states: "A canonical Bad -> ProcessionLabel l map is not present in
   T.arithmetic; the only available place-level route is via the chosen lift
   ... not a theta label." Nothing in this probe contradicts that.

## 7. Recommendation

- If the consumer only needs a **function** `Bad -> SignedLabel` for indexing
  or choice, use §5.1 or §5.2, name it `badResidue...`, and document that it
  is a residue-characteristic projection. Do not name it `thetaLabel`.
- If the consumer needs the **paper theta label**, do not derive it from the
  residue characteristic. Add an explicit labeling field at the interface
  level (not in `InitialThetaArithmeticData`):

  ```lean
  structure BadThetaLabelMap (l : PrimeGeFive) (T : SourceNativeInitialThetaData l) where
    labelOf : Bad (nativePlaceSelection T) -> ProcessionLabel l
  ```

  or directly `-> ThetaLabel` if sign-identified positive labels are wanted.
  This is the first missing datum.
- If a `Fin (lStar)` index is required, use §5.3 with
  `s1930PositiveLabel`; do not compose with `thetaLabelOfFin` (off by one:
  `0..l*-1` vs `1..l*`).
- Do not claim `badRationalPrime b mod l` is the paper theta label without a
  new source identification; the tree explicitly says the residue candidate is
  not that identification.

## 8. Evidence index

Source absence / label interface:
- `LeanFormal/IUT/IUTI/InitialTheta/ArithmeticData.lean:62-81` —
  `InitialThetaArithmeticData` fields.
- `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:578-631` —
  `SourceSignQuotientData` fields.
- `LeanFormal/IUT/IUTI/InitialTheta/SourcePlaceSelection.lean:31-37` —
  `SourcePlaceSelection` fields.
- `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:889,959,1007,1106,1432,1543` —
  clauses A-F.
- `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Boundary.lean:39-45` —
  formal `badLabel : Bad -> Nat`.
- `LeanFormal/IUT/IUTI/InitialTheta/SourcePlacePartitionReduction.lean:188-189,603-604,633-635,115-117` —
  `Bad`, `badResidueLabel`, `badStripLabel`, `residueCharacteristic_comap`.
- `LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31NativeContractBridgeReduction.lean:108-114` —
  `nativePlaceSelection`.

Label types and conversions:
- `LeanFormal/IUT/Foundations/Theta/GaussianKernel.lean:94-95` — `SignedLabel`.
- `LeanFormal/IUT/Foundations/Theta/SignedLabelEquiv.lean:48-62,75-82,141-146` —
  `representative`, `equiv`, `card_signedLabel`.
- `tmp/sheaf/xif/paper/ProcessionNormalizationWeightsActual.lean:78-79` —
  `ProcessionLabel`.
- `tmp/sheaf/xif/paper/PaperC3ThetaRootActual.lean:82-91` — `ThetaLabel`,
  `thetaLabelToSigned`.
- `tmp/sheaf/xif/paper/MultiradialProcessionActual.lean:120-127` —
  `thetaLabelOfFin`.
- `tmp/sheaf/xif/paper/S1930CompareA0AverageActual.lean:125-132,153-171` —
  `s1930PositiveLabel` and its surjectivity.
- `tmp/sheaf/xif/paper/S703GlobalPaperThetaComparisonActual.lean:29-38` —
  `paperThetaPositiveLabel`.
- `tmp/sheaf/xif/paper/S694ThetaAverageNormalizationActual.lean:25` —
  `PaperThetaLabel := Fin (lStar)`.

Existing maps / interfaces:
- `tmp/sheaf/xif/paper/Mzk1PaperLabelBadIndexBridgeActual.lean:11-14,34-35,48-51` —
  obstacle comment, `badRationalPrime`, `BadThetaLabelMap`.
- `tmp/sheaf/xif/paper/Mzk1PaperLabelProjectionActual.lean:16-18,44-47,52-72` —
  residue candidate and interface.
- `tmp/sheaf/xif/paper/VbadPlaceIndexingActual.lean:46-55,74-85` —
  `nativeBadToFPlace`, `nativeBadToKPlace`.
- `tmp/sheaf/xif/paper/S640PaperRootThetaProcessionActual.lean:42-43` —
  `processionSignedLabel`.
- `tmp/sheaf/n8/closure/LabelToSignedLabelBridge.lean:4-7,28-32` —
  arbitrary `labelEquiv`.
- `tmp/sheaf/n8/closure/LabelData.lean:5-10,25-46` — paper labels are capsule
  positions, arbitrary permutations.
- `Iut/Concrete/ThetaRegion.lean:31-36,47-48` — label -> place tuple.
- `tmp/sheaf/xif/paper/S3097SourceBadLabelInjectiveActual.lean:56-93` —
  concrete injectivity only.

Arithmetic bridge:
- `.lake/packages/mathlib/Mathlib/RingTheory/Ideal/Int.lean:106-110` —
  `Ideal.ringChar_quot`.
- `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:970-975` —
  Clause B coprimality.

Specification warnings:
- `tmp/sheaf/xif/paper/PAPER_OBJECT_SPEC.md:47` — forbid all `SignedLabel`
  for theta labels.
- `tmp/sheaf/xif/paper/PaperSymbolTypesActual.lean:9-11,52-54` — theta labels
  are positive `j=1,...,l*`.
- `tmp/sheaf/xif/paper/Mzk1PaperLabelProjectionActual.lean:54-56` — residue
  candidate is not the paper identification.


---

# Appendix: earlier probe text (superseded; kept for history)

## A8 canonical theta-label probe: `Bad -> SignedLabel l.value`

Status: **EXACT OBSTRUCTION** (no canonical construction found; no axiom/sorry; nothing kernel-checked in this probe).

## Question
Can the actual data give a canonical function
```lean
Bad (nativePlaceSelection T) -> SignedLabel l.value
```
using `Mzk1PaperLabelBadIndexBridgeActual.badRationalPrime` and
`MultiradialProcessionActual.thetaLabelOfFin`?

## Available actual data
- `badRationalPrime` (Mzk1PaperLabelBadIndexBridgeActual.lean:34-36):
  ```lean
  noncomputable def badRationalPrime (b : Bad (nativePlaceSelection T)) : Nat :=
    rationalPrimeOfFinitePlace (K := T.arithmetic.K) ((nativeBadToKPlace T b).maximalIdeal)
  ```
  It is a residue-prime projection; `badRationalPrime_eq` (:38-41) identifies it with
  `Ideal.absNorm (... .under Int)`.
- `badRationalPrime_function` (:43-46) only re-packages the same function.
- `BadThetaLabelMap` (:48-51) is a **structure with no inhabitant**:
  ```lean
  structure BadThetaLabelMap (l : PrimeGeFive) where
    labelOf : Bad (nativePlaceSelection T) -> PaperLabelGroup l
  ```
  `PaperLabelGroup l = ProcessionLabel l`, not `SignedLabel l.value`.
- `thetaLabelOfFin` (MultiradialProcessionActual.lean:120-127):
  ```lean
  def thetaLabelOfFin (i : Fin (lStar l.value)) : SignedLabel l.value
  ```
  It accepts only a bounded `Fin (lStar l.value)` index.
- `SignedLabel` (LeanFormal/IUT/Foundations/Theta/GaussianKernel.lean:94-96):
  ```lean
  def SignedLabel (l : Nat) :=
    {j : Int // j ∈ Set.Icc (-(lStar l : Int)) (lStar l : Int)}
  ```

## Why `badRationalPrime` does not give the map
1. **Type/index mismatch.** `badRationalPrime b : Nat` is not a `Fin (lStar l.value)`.
   There is no source field or theorem bounding `badRationalPrime b < lStar l.value`.
   Coercing `Nat -> Fin` requires a modulus/bound proof which is not in T.arithmetic.
2. **Semantics mismatch.** The paper theta label is a bounded integer label of the
   theta monoid; the residue prime of a bad place is not that label. The existing
   doc comment of Mzk1PaperLabelProjectionActual.lean:16-18 states exactly this:
   no canonical map from finite places to paper theta labels; the paper label group
   is not a residue-character group.
3. **Candidate map goes elsewhere.** The existing `candidateLabelOfPlace`
   (Mzk1PaperLabelProjectionActual.lean:52-62) maps a place with
   `(rationalPrimeOfFinitePlace K v : ZMod l.value) ≠ 0` to
   `Units (ZMod l.value) = ProcessionLabel l`, not to `SignedLabel l.value`.
   It also needs the nonzero-mod-l side condition and is explicitly not asserted
   to be the paper label identification (:65-72 `PaperLabelProjectionInterface`,
   no inhabitant).
4. **Lift dependence is removed, index dependence remains.** The green lemmas in
   Mzk1NativeBadPrimeSourceActual.lean:19-25 remove dependence on the chosen
   `nativeBadToKPlace` lift, but the resulting function is still
   `b |-> rationalPrimeOfFinitePlace(... b ...)`, hence index-dependent and
   not a theta label.

## Conditional construction (only if a bound is supplied)
If one explicitly supplies
`h : forall b, badRationalPrime T b < lStar l.value`,
then
```lean
fun b => thetaLabelOfFin (l := l) ⟨badRationalPrime T b, h b⟩
```
is a function `Bad -> SignedLabel l.value`. This is not canonical paper data:
`h` is an extra input, and the resulting label is a residue-prime reduction,
not the theta-label identification.

## Exact missing datum
A field/theorem in `InitialThetaArithmeticData` (or in `SourceSignQuotientData`)
that assigns to each bad index its theta label in `Fin (lStar l.value)` or directly
in `SignedLabel l.value`, together with the compatibility proof that this label is
the paper theta label. Neither the field nor the bound is present.

## Verdict
No canonical `Bad -> SignedLabel l.value` from the current actual source data.
The precise obstruction is the missing theta-label assignment/index, not the
residue-prime projection (which exists but is semantically different).
