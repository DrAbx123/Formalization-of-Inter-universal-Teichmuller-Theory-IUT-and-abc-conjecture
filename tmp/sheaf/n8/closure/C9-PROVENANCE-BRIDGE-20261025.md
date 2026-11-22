# C9 stage1: C9Paper / PaperP6 provenance bridge

Task ID: task-152. Owner: qside. Date: 2026-10-25.
Stage: SHEAF stage1 natural-language research only. No Lean edits, no Project edits,
no target changes. Consumer: `n8-c9-output-region-source-route`.

Status: this report specifies the exact provenance equalities needed to identify
C9Paper `QPaper.qPilotLogVolume` and `ThetaPaper.thetaLogVolume` with the actual
PaperP6 C6 quantities, and the provenance needed to build `ValuesPaper` from
source outputs. It does **not** prove those equalities; it separates what is
actual in the Lean tree from what is a donor/source gap. `target_accepted=false`.

Corrections incorporated:

- C9-TAME-LOG-DOMAIN-20261025.md §2 is **not** used as an actual theorem. The
  donor is not an image `rho(Mod)=Sp` and not a splitting; the closed actual
  donor is `H = Phi^{-1}(Sp_{2g}(Z_p))` (C9-SYMPLECTIC-SOURCE-20261025.md, C1-C2).
- The 2025 trace basis vs 2026 symplectic basis alignment is an inferred
  convention, not a quoted cross-paper theorem (C3). The trace theorem is
  `Tr_{K/K^{(d=1)}}`; it is `Tr_{K/Q_p}` only in the tame totally ramified case (C4).
- `J=m`, the lattice classification, orbit generation and volume gain are
  inferred consequences, not Kondo theorems (C5).
- Full Ind1 is the procession automorphism group, not a finite label translation.
  Equations (11)-(14) of C9-TAME §5 are not a target proof and require
  TC-A..TC-H and TC-S (C9-IND1-GLOBAL-20261025.md). A ring isomorphism alone
  does not imply `F(Hull(...)) subset H_C`.

## 1. Current actual Lean anchors

All paths below are read-only evidence; no file was modified.

| file | SHA256 | role |
|---|---|---|
| `tmp/sheaf/n8/closure/C9Paper.lean` | `481213D714798D880DD72D0440EB57C4DE8F9FC612A05F5963F29F14806CC045` | C9Paper structures and named obligations |
| `tmp/sheaf/n8/closure/PaperP6C6AlignedTarget.lean` | `6A224A5C826D864C3F32B12BF3A34D74A7B4C78CA24C5942CFFB0FC622BE0808` | strongest current P6/C6 alignment |
| `tmp/sheaf/n8/closure/PaperC6ValuesActual.lean` | `8F0A5F34AC37BDF79FA7F9CB6B4A12E8622D7690AA367B8E25DCAE3C7AE2CBFC` | every actual normalized value is a C6 normalizedLogVolume |
| `tmp/sheaf/n8/closure/PaperP6ToC9.lean` | `3C0116F9DDF7E99F402F9B8D0E4F1EFCF3425AA28E93D7896B3AF50AC0F178EE` | volume-level C9 bridge and provenance gap |
| `tmp/sheaf/n8/closure/PaperP6Final.lean` | `2F2B8884E72E25CDC9758E6D0762CAE3293C954520109448F8FA6E24838D9088` | normalized theta and finite theta |
| `tmp/sheaf/n8/closure/PaperNormalizedLogBridge.lean` | `9FF5589268F7F5EFFA857EE4686BBB1E44EFAC9A3B754F73DE5DB6D32CA25AA2` | normalizedTheta = C6 normalizedLogVolume hull |
| `tmp/sheaf/n8/closure/PaperQPilotNormalizedBridge.lean` | `1A67207560D025C74D1696CFCFF80C37D988FD988B083BED0886C75EBBFE48D6` | qLog = C6 normalizedLogVolume qPilotRegion |

Source/correction documents:

- `C9-TAME-LOG-DOMAIN-20261025.md`, SHA256
  `23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06`
  (only §§1, 3-8, with §2 superseded).
- `C9-SYMPLECTIC-SOURCE-20261025.md`, SHA256
  `3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70`
  (corrected donor; C1-C5).
- `C9-IND1-GLOBAL-20261025.md`, SHA256
  `94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8`
  (full Ind1 and TC conditions).

## 2. The actual PaperP6/C6 quantities

Fix an actual source `S : SourceInitialThetaData l`.

### 2.1 q side

```lean
PaperKf S := CommonPrimeCompletion (placeAtPrime S)
qAtPrime S : PaperKf S               -- q S at the chosen bad F-place
qUnit S : (PaperKf S)ˣ := Units.mk0 (qAtPrime S) (q S ≠ 0)
qPilotRegion S := e.symm '' (qAtPrime S • Integers (PaperKf S))
```

Actual [PaperQPilotNormalizedBridge.lean]:

```lean
qLog_eq_c6NormalizedLogVolume_qPilot :
  Real.log ‖(qUnit S : PaperKf S)‖ =
    (C6ActualIQData.actual (places S) (tuple S) rawData.mu).normalizedLogVolume
      (qPilotRegion S)
```
and `qLog_mem_normalizedValueSet` says this number belongs to the actual
normalized value set.

### 2.2 Theta side

```lean
C6.normalizedLogVolume μ T =
  (1 / D) * (Real.log (μ T).toReal - Real.log (μ unitRef).toReal)
D = Module.finrank ℚ_[pNat S] (ArithmeticTensorTupleBlock (places S) (tuple S))
```

Actual [PaperNormalizedLogBridge.lean, PaperP6AlignedTarget.lean]:

```lean
normalizedTheta S := thetaLogVolume S / (d S : ℝ)
normalizedTheta_eq_c6NormalizedLogVolume :
  normalizedTheta S = (C6ActualIQData.actual ...).normalizedLogVolume (c6Hull S)
```

where `c6Hull S` is the actual C6 IQ-interface hull and
`d S = finrank ℚ_[pNat S] (PaperKf S) = finrank ℚ_[pNat S] (Block S)`.

**Degree warning.** The raw field `C7MassFormulaZeroSorry.thetaLogVolume S` is
`Real.log ((c6UnitRefNormalizedData c6Hull).toReal)`, without the division by
`d`; it is **not** the C6 `normalizedLogVolume`. The exact relation is

```lean
thetaLogVolume S = (d S : ℝ) * normalizedTheta S.
```

`C9Paper.ThetaPaper.thetaLogVolume` is typed as a C6 `normalizedLogVolume`
(already degree-normalized). Therefore the provenance bridge must compare
`ThetaPaper.thetaLogVolume` with `normalizedTheta S`, not with the raw
`C7MassFormulaZeroSorry.thetaLogVolume S`; using the raw field without the
`d` factor would be a scalar error.

### 2.3 Actual assembled target

`PaperP6C6AlignedTarget.PaperP6C6AlignedTarget S` is the conjunction of:

1. `PaperP6NormalizedTarget S` (normalized values and qLog bounded by
   `normalizedTheta S`);
2. `normalizedTheta S = C6.normalizedLogVolume (c6Hull S)`;
3. `Real.log‖qUnit S‖ = C6.normalizedLogVolume (qPilotRegion S)`.

`paperP6C6AlignedTarget_actual` is actual zero-sorry (per the files listed
above). This is the Lean-side anchor for the C9 provenance bridge; it does not
provide any C1/C2/C3 source structure.

## 3. C9Paper target surfaces

From `C9Paper.lean`:

### 3.1 QPaper

```lean
structure QPaperScalar (C3) where
  value : Real
  value_eq : value = localSignedLog C3.q

structure QPaper (D) (C1) (C2) (C3) where
  qPilotRegion : Set (C6IQCarrier C3.tensorPlaces C3.tensorTuple)
  qPilotRegion_eq_unit : qPilotRegion = {C3.tensorUnit}
  scalar : QPaperScalar C3
  kummer : SourceLogKummerData I C1
  qPilotLogVolume : WithTop Real
  qPilotLogVolume_eq : qPilotLogVolume = (scalar.value : WithTop Real)
```

`localSignedLog (C3.q)` is the canonical-completion log norm
`Real.log ‖C3.q.q‖` (ArithmeticQPilotLogVolume). The structure contains no
equality between `qPilotLogVolume` and any C6 `normalizedLogVolume`, and no
provenance equality between `C3.tensorUnit` and the actual q-pilot region.

### 3.2 ThetaPaper

```lean
structure ThetaPaper (D) (C1) (C2) (n) (C6) where
  thetaHull : Set (I.ThetaPilotPoint D.place.v)
  thetaHull_eq : thetaHull = I.sourceHolomorphicHull D.place.v D.place.R n
  thetaHull_contains_image :
    I.possibleThetaPilotImageSet D.place.v D.place.R n ⊆ thetaHull
  thetaToC6 : Set (I.ThetaPilotPoint D.place.v) → Set (C6IQCarrier places tuple)
  thetaLogVolume : WithTop Real
  thetaLogVolume_eq :
    thetaLogVolume = (C6.normalizedLogVolume (thetaToC6 thetaHull) : WithTop Real)
  kummer : SourceLogKummerData I C1
  ind : IndActionData (I.ThetaPilotPoint D.place.v) Label
```

`thetaToC6` is an arbitrary function field; the structure does not constrain it
to a source map. `thetaHull_contains_image` is a field assumption, not a proved
source containment. `ind` is not the actual full Ind1 action.

### 3.3 ValuesPaper

```lean
structure ValuesPaper (C6) where
  provenance : Set (C6IQCarrier places tuple)

def ValuesPaper.values : Set Real := {z | ∃ S, S ⊆ provenance ∧
  z = C6.normalizedLogVolume S}
```

`provenance` is an arbitrary set, not tied to the source possible-theta image
set. `values` ranges over **all subsets** of `provenance`, so different
provenance choices change the value set.

### 3.4 Named obligations still open in C9Paper

`qPaper_in_Rleq_obligation`, `valuesPaper_bounded_obligation`,
`qPaper_approximated_obligation`, `thetaPaper_nonempty`, `valuesPaper_nonempty`
are all named-sorry obligations in `C9Paper.lean`. The easy equalities
`qPaper_scalar_eq_obligation` and `qPaperOfC3`/`qPaper_nonempty` are actual but
do not touch C6 normalized volume.

## 4. Exact provenance equalities required

Let `S : SourceInitialThetaData l` be the fixed actual paper source. The bridge
needs an actual C9 source tuple

`(I, D, C1, C2, C3, C6, Theta, Q, V)`

with the following equalities. Each is a separate proof obligation; none is
presently a hypothesis of C9Paper.

### Q1 (q source place and scalar)

```text
C3.p = pNat S,          C3.place = placeAtPrime S,
C3.q = qCandidate S
```

up to the dependent transport of `FinitePlaceAtPrime (Fmod) p`. The first
needed objects are the C1 place equivalence and the C3 place equality; without
them `C3.q` cannot be compared with `qAtPrime S`.

### Q2 (canonical vs normalized q norm)

```text
localSignedLog C3.q = Real.log ‖(qUnit S : PaperKf S)‖.
```

Since `localSignedLog C3.q = Real.log ‖C3.q.q‖` uses the canonical completion
norm and `qUnit S` uses the normalized/spectral `CommonPrimeCompletion` norm,
this is not `rfl` after `C3.q = qCandidate S`. The exact required input is the
canonical/normalized norm equality at the paper place,

```text
CanonicalNormalizedNormEquality (pF S)
  (or an equivalent equality of the two norms on qCandidate.q).
```

Only the strict inequality `‖qUnit S‖ < 1` is currently proved in the P6 tree
(via `normalizedCompletion_norm_lt_one_iff`); the equality of norms on the
actual q element is not proved. This is a real bridge gap, not a cosmetic
coercion.

### Q3 (QPaper log equals actual q log)

From Q1/Q2 and `QPaper.qPilotLogVolume_eq`:

```text
Q.qPilotLogVolume = (Real.log ‖qUnit S‖ : WithTop Real).
```

### Q4 (actual C6 q-pilot value)

```text
(Q.qPilotLogVolume : WithTop Real)
  = (C6.normalizedLogVolume (qPilotRegion S) : WithTop Real).
```

This is exactly the actual zero-sorry
`PaperQPilotNormalizedBridge.qLog_eq_c6NormalizedLogVolume_qPilot S`, after Q3.
It requires `Q.qPilotRegion` to be understood as the actual q-pilot region for
the purpose of values; QPaper itself only records the singleton
`{C3.tensorUnit}`. The equality of the scalar does not require region
identification, but any Values/approximation statement does.

### Q5 (q region provenance for Values)

If Q's tensor unit is to represent the actual q-pilot region in ValuesPaper:

```text
C3.tensorUnit = tensorLanding C3.q   (C3 field)
C3.tensorLanding qPilotRegion source = actual qPilotRegion S
```

The C3 field gives the first equality by definition of `SourcePilotRegionData`;
the second is not in C3. The actual qPilotRegion is built from
`e.symm(qAtPrime • Integers)`; `tensorUnit` is a single point. A singleton is
not the full q-pilot region. Therefore Q5 cannot be used for volume identities
without an additional actual region/tensor-landing construction. For the Q log
scalar, Q4 suffices.

### T1 (Theta hull equality)

```text
Theta.thetaHull = I.sourceHolomorphicHull D.place.v D.place.R n
```

This is the field `thetaHull_eq`, so it is definitional once the actual
`ThetaPaper` is given; the missing source content is that the actual
`SourceInitialThetaData` source provides this `I,D,n` and the source hull.

### T2 (actual theta-to-C6 map)

```text
Theta.thetaToC6 : Set (I.ThetaPilotPoint D.place.v) → Set (C6IQCarrier places tuple)
Theta.thetaToC6 (I.possibleThetaPilotImageSet D.place.v D.place.R n) ⊆ c6Hull S
Theta.thetaToC6 Theta.thetaHull = c6Hull S
```

Only the first object is a field of `ThetaPaper`; the two equalities/inclusions
are **not** present. This is the `thetaToC6` gap. It must be an actual map from
the source theta carrier to the C6 tensor block, compatible with the C7
theta/source construction, not an arbitrary function chosen after the fact.

### T3 (Theta log equals normalized C6 hull log)

```text
Theta.thetaLogVolume = (normalizedTheta S : WithTop Real)
  = (C6.normalizedLogVolume (c6Hull S) : WithTop Real).
```

This follows from T1/T2 and the actual
`PaperP6AlignedTarget.normalizedTheta_eq_c6NormalizedLogVolume S` once
`Theta.thetaToC6 Theta.thetaHull = c6Hull S` is proved. Without T2, T3 is
exactly the missing provenance equality.

**Do not** rewrite T3 as
`Theta.thetaLogVolume = (C7MassFormulaZeroSorry.thetaLogVolume S : WithTop Real)`.
That raw field omits the division by `d`; the correct scalar relation is
`thetaLogVolume S = d S * normalizedTheta S`. The C9 target is degree-normalized.

### V1 (Values provenance set)

```text
V.provenance = Theta.thetaToC6 Theta.thetaHull
```

or, for a weaker inclusion-sufficient target,

```text
V.provenance ⊆ c6Hull S   and   all actual q-pilot values are in V.values.
```

The actual C6 hull `c6Hull S` is available; the source-output set is not. A
proof that `c6Hull` is exactly the source-output image is precisely the
`thetaToC6`/full-Ind1 source gap, and cannot be replaced by taking
`provenance := c6Hull` if equality of value sets is asserted.

### V2 (Values values)

`ValuesPaper.values` is already defined by C6 `normalizedLogVolume` of subsets
of `provenance`; this matches the actual `PaperNormalizedValueBridge` values
only after:

1. `allQPilotRegions S ⊆ c6Hull S` (actual in `PaperAllQPilotRegions`);
2. the positivity/finite-mass bridge for all q-pilot regions (the current
   positivity task; see §7);
3. the q-pilot normalizedValue equality
   `normalizedValue T = C6.normalizedLogVolume T` under positive/finite mass
   (PaperNormalizedValueBridge).

Then the actual `normalizedValueSet S` is a subset of
`ValuesPaper.values` for `V.provenance = c6Hull S`; equality requires V1 plus
the converse that no extra C6 subsets occur in the source value set.

### V3 (Q approximation)

`QPaperApproximated` requires qLog to be approached from below by values in
`V.values`. The actual `qLog_mem_normalizedValueSet` and
`normalizedValueSet_bounded` supply the q-pilot representative in the P6 value
set; under V1/V2 it lies in `V.values`. The C9 approximation obligation then
reduces to choosing that actual representative, not to a new analytic limit.

## 5. C1/C2/C3 and thetaToC6 gaps

### C1 (`SourceInputBinding`)

`SourceInputBinding` contains `SourcePlaceRealization`:

```text
placeEquiv : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)
selected : V
selected_realization : I.SourceImageRealization selected
fiberMonEquiv : ... primeStripAt ... ≃* SourcePlaceValueGroup ...
```

`sourceInputBinding_nonempty` is a named sorry. Needed for the bridge:

- `placeEquiv` must send `selected` to the paper finite place `pF S` (resp. the
  chosen place underlying `placeAtPrime S`), and the actual finite/infinite
  place components must agree;
- `selected_realization` is the actual C1 source image `R` used by C3/Theta;
- `fiberMonEquiv` is the prime-strip/value-group comparison. It is not used by
  C6 normalizedLogVolume, but it is needed for Q/Theta source provenance.

Without C1, a C3 `place` is just some finite place of `Fmod`; it cannot be
identified with the paper's `placeAtPrime S`.

### C2 (`SourceLogKummerData`)

Fields include the actual per-finite-place log shell, kernel=torsion, log-shell
and pre-log-shell equalities. `sourceLogKummerData_nonempty` is a named sorry.
Needed for:

- `Q.kummer`, `Theta.kummer` (currently just `C2`);
- the actual source log branch for Q/Theta values;
- the Kummer/root-change naturality used in any comparison with C9's
  log-Kummer column.

C2 does **not** contain the actual source Kummer/root-change map, K1/K2
connection, archimedean branch, or multi-place assembly; those are named gaps
in its docstring.

### C3 (`SourcePilotRegionData`)

Fields: `p`, `place`, `q`, `thetaPacket`, `qUnit`, `roots`, `roots'`,
`kummerClass`, `rootChange`, `tensorIndex/tensorPlaces/tensorTuple`,
`tensorUnit`, `tensorLanding`, `tensorLanding_q`.
`sourcePilotRegion_nonempty` is a named sorry. Needed for Q:

- `C3.q` is the actual q completion element (not a Real);
- `C3.place` is the actual finite place;
- `C3.tensorUnit` and `C3.tensorLanding` are actual tensor data;
- `C3.tensorLanding_q` is the only currently available landing equality.

C3 does **not** prove that `C3.place` equals the paper place, that `C3.q` is
`qCandidate S`, that `tensorUnit` is the actual canonical unit reference, or
that `tensorLanding` is the C7 nonlinear landing. Those are the C3 provenance
gaps.

### `thetaToC6`

`ThetaPaper.thetaToC6` is a free function. The bridge needs an actual map

```text
thetaToC6 : Set (I.ThetaPilotPoint D.place.v) → Set (C6IQCarrier places tuple)
```

induced by the source theta-pilot object and the C6/C7 tensor construction, with
T2. No such construction is present in `C9Paper`; it is the exact `thetaToC6`
donor gap. `Theta.thetaHull_contains_image` is a field assumption, not a proof
that the possible theta images are exactly the actual source outputs.

## 6. Why the symplectic/Ind1 corrections matter for provenance

The source-output provenance for `ThetaPaper` and `ValuesPaper` cannot use the
flawed donor or a ring isomorphism. Exact consequences:

- The actual closed donor is `H = Phi^{-1}(Sp_{2g}(Z_p))`, and the actual
  construction of any `beta` uses the mapping-class/Dehn-twist `rho`; there is
  no homomorphic section and no `rho(Mod)=Sp`.
- The 2025 trace basis and 2026 symplectic basis alignment is an inferred
  convention; any orbit/volume computation conditional on it must say so.
- `J=m`, the trace formula `Tr_{K/K^{(d=1)}}`, the standard-lattice lemma, the
  orbit-generation (7) and volume gain (8) are inferred, not Kondo theorems.
- Full Ind1 is the procession automorphism group, not finite label translation;
  the target hull is subject to Ind1, Ind2, Ind3.
- Equations (11)-(14) are not target proofs. They require TC-A..TC-H and TC-S;
  in particular TC-B (target saturation or `F` an allowed target automorphism)
  and TC-C (normalized volume compatibility) are not proved. A ring isomorphism
  alone does not give `F(Hull(...)) subset H_C`.

Therefore any `ThetaPaper`/`ValuesPaper` provenance that relies on the
C9-TAME §2 construction or on (11)-(14) must be marked **withdrawn/conditional**,
not used as an actual source input.

## 7. What is actual, inferred, and missing

### Actual in Lean (read-only evidence)

1. `qUnit`, `qAtPrime`, `qPilotRegion`, `c6Hull`, C6 `normalizedLogVolume`.
2. `qLog_eq_c6NormalizedLogVolume_qPilot`.
3. `normalizedTheta_eq_c6NormalizedLogVolume` and
   `PaperP6C6AlignedTarget` (normalized target plus both C6 equalities).
4. `PaperNormalizedValueBridge.normalizedValue_eq_c6` under positive finite raw
   mass; `PaperP6Final.thetaLogVolume_lt_top`; C6 hull finiteness.
5. `PaperC6ValuesActual.normalizedValueSet_eq_c6` (every actual normalized
   q-pilot value is a C6 normalizedLogVolume).
6. C9Paper structures and easy fields (`qPaperOfC3`, scalar equality).

### Inferred / conditional

1. canonical/normalized norm equality Q2 (currently only `<1` is proved);
2. C3 `place`/`q` identification with `placeAtPrime S`/`qCandidate S`;
3. `thetaToC6` hull equality T2 and Theta log T3;
4. Values provenance V1/V2 and Q approximation V3;
5. any symplectic/Ind1 source-output construction: conditional on corrected
   `H=Phi^{-1}(Sp)`, basis alignment, trace target, low-ramification input,
   standard-lattice lemma, and TC-A..TC-H/TC-S.

### Missing (explicit gaps)

1. actual `SourceInputBinding` / C1 placeEquiv selected at `placeAtPrime S`;
2. actual `SourceLogKummerData` / C2 Kummer and log-shell source data;
3. actual `SourcePilotRegionData` / C3 q, thetaPacket, tensorLanding, and the
   `tensorUnit`/`qUnit` provenance;
4. canonical/normalized norm equality for Q2;
5. actual `thetaToC6` map and T2;
6. actual `V.provenance` equality (V1), and the positivity/finite-mass
   instantiation for all q-pilot regions (task-152 adjacent positivity task);
7. full Ind1/Ind2/Ind3 source action and TC-A..TC-H/TC-S for any target-hull
   containment; equations (11)-(14) are not available;
8. the C9Paper named obligations `qPaper_in_Rleq`, `valuesPaper_bounded`,
   `qPaper_approximated`, `thetaPaper_nonempty`, `valuesPaper_nonempty`
   remain sorry in `C9Paper.lean`.

## 8. Recommended exact bridge target (stage2 candidate, not proved here)

Only after the missing items are supplied, the C9 side should state the
following three provenance records:

```text
C9QProvenance(S, C3, Q) :=
  C3.place = placeAtPrime S ∧
  C3.q = qCandidate S ∧
  localSignedLog C3.q = Real.log ‖qUnit S‖ ∧
  Q.qPilotLogVolume = (Real.log ‖qUnit S‖ : WithTop Real) ∧
  Q.qPilotLogVolume = (C6.normalizedLogVolume (qPilotRegion S) : WithTop Real)

C9ThetaProvenance(S, Theta) :=
  Theta.thetaHull = I.sourceHolomorphicHull ... ∧
  Theta.thetaToC6 Theta.thetaHull = c6Hull S ∧
  Theta.thetaLogVolume = (normalizedTheta S : WithTop Real) ∧
  Theta.thetaLogVolume = (C6.normalizedLogVolume (c6Hull S) : WithTop Real)

C9ValuesProvenance(S, V) :=
  V.provenance = Theta.thetaToC6 Theta.thetaHull ∧
  V.values = {z | ∃ T, T ⊆ V.provenance ∧
    z = C6.normalizedLogVolume T}
```

The C9Paper target should then be the conjunction of C9QProvenance,
C9ThetaProvenance, C9ValuesProvenance and the actual P6 normalized inequality
`qLog <= normalizedTheta` (already actual in `PaperP6NormalizedValuesActual`).
Until then, `QPaper.qPilotLogVolume` and `ThetaPaper.thetaLogVolume` remain
source-relative formal readouts, not identified with the P6 C6 quantities.

## 9. Verdict

- No Lean or target file was edited by this task.
- No C9Paper Q/Theta provenance equality is proved; the exact equalities are
  Q1-Q5, T1-T3, V1-V3 above.
- The current actual P6/C6 anchors are sufficient on the C6 side (normalized
  log-volume formula, qLog/C6 equivalence, normalizedTheta/C6 hull equivalence,
  normalized values under positive finite mass).
- All source-side (C1/C2/C3, thetaToC6, full Ind1, symplectic donor) inputs
  remain missing or conditional; the flawed C9-TAME §2 and (11)-(14) route is
  not used.
- `target_accepted=false`; no global C9 inequality and no target-hull
  containment is claimed.

## 10. Citation summary

Lean (read-only):

- `tmp/sheaf/n8/closure/C9Paper.lean` SHA
  `481213D714798D880DD72D0440EB57C4DE8F9FC612A05F5963F29F14806CC045`.
- `tmp/sheaf/n8/closure/PaperP6C6AlignedTarget.lean` SHA
  `6A224A5C826D864C3F32B12BF3A34D74A7B4C78CA24C5942CFFB0FC622BE0808`.
- `tmp/sheaf/n8/closure/PaperC6ValuesActual.lean` SHA
  `8F0A5F34AC37BDF79FA7F9CB6B4A12E8622D7690AA367B8E25DCAE3C7AE2CBFC`.
- `tmp/sheaf/n8/closure/PaperP6ToC9.lean` SHA
  `3C0116F9DDF7E99F402F9B8D0E4F1EFCF3425AA28E93D7896B3AF50AC0F178EE`.
- `tmp/sheaf/n8/closure/PaperP6Final.lean` SHA
  `2F2B8884E72E25CDC9758E6D0762CAE3293C954520109448F8FA6E24838D9088`.
- `tmp/sheaf/n8/closure/PaperNormalizedLogBridge.lean` SHA
  `9FF5589268F7F5EFFA857EE4686BBB1E44EFAC9A3B754F73DE5DB6D32CA25AA2`.
- `tmp/sheaf/n8/closure/PaperQPilotNormalizedBridge.lean` SHA
  `1A67207560D025C74D1696CFCFF80C37D988FD988B083BED0886C75EBBFE48D6`.

Stage1 sources:

- `C9-TAME-LOG-DOMAIN-20261025.md` SHA
  `23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06`
  (§2 corrected/withdrawn; §§1, 3-8 used only as stage1 research).
- `C9-SYMPLECTIC-SOURCE-20261025.md` SHA
  `3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70`
  (corrected donor, C1-C5).
- `C9-IND1-GLOBAL-20261025.md` SHA
  `94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8`
  (full Ind1 and TC-A..TC-H/TC-S).

End of C9-PROVENANCE-BRIDGE-20261025.