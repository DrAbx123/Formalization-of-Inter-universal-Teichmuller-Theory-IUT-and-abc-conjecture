# A7 bad-moduli verdict: `NativeBadModuliFixedPrime`

Date: 2026-11-14 (Asia/Shanghai). Mode: **read-only source analysis** at `D:\lean`
(Lean 4.32.2 / Mathlib, Route C). No `lake`/`lean` invocation, no Lean-source or
watchdog edit. **Nothing below is kernel-checked in this pass**; every statement is an
inspection of the cited declaration (file:line) plus paper-level proof sketches. No
axiom/sorry status is claimed for anything here.

## 0. Verdict (one paragraph)

`NativeBadModuliFixedPrime` is **not TRUE and not FALSE as stated: it is an exact
obstruction**. (i) It is not a proposition but a `p`-indexed predicate on `T`, so the only
well-posed global readings are `∀ T p, NativeBadModuliFixedPrime T p` (false, and made false
already by its own `p`-dependence) and `∀ T, ∃ p, NativeBadModuliFixedPrime T p` ("one
rational prime for all Bad indices"). (ii) The second is **equivalent to constancy of
`b ↦ (completionRationalPrime b.1).val` on `Bad (nativePlaceSelection T)`** — a cross-index
universal equality. (iii) **No field of the source determines that constancy**: the bad set is
a free field `V_mod_bad`, constrained only *per place* (odd residue characteristic, nonempty,
and Clause (b) conditions at F-places above it). (iv) The source type **admits bad sets with
several distinct rational primes**, and the tree contains already-formalized instances
(`S1729Selection l` = `{3,5,7}`, `S1730Selection l` = `{3,5,7}` minus the place of residue
characteristic `l`); for those sets `∃ p` is false. Hence the honest status is: **an extra
paper input, which the project's own concrete admissible bad set refutes**; the correct
replacement is per-prime grouping (prime fibers), or the already `p`-free product route (§5).

---

## 1. Exact statement and location

**Definition** — `tmp/sheaf/xif/paper/Mzk1NativeBadPrimeSourceActual.lean:27-29`:

```lean
/-- Exact source condition: all Bad moduli places have fixed rational prime p. -/
def NativeBadModuliFixedPrime (p : ℕ) : Prop :=
  ∀ b : Bad (nativePlaceSelection T), (completionRationalPrime b.1).val = p
```

- Full name: `LeanFormal.IUT.XiFPaper.Mzk1NativeBadPrimeSourceActual.NativeBadModuliFixedPrime`
  (namespace line 14). Section variables (lines 15-17):
  `{l : PrimeGeFive}`, `(T : SourceNativeInitialThetaData l)`,
  `[Fintype (Bad (nativePlaceSelection T))]` (the body uses only `T` and `p`).
- `Bad P := {p : NumberField.FinitePlace A.Fmod // p ∈ P.V_mod_bad}` —
  `LeanFormal/IUT/IUTI/InitialTheta/SourcePlacePartitionReduction.lean:187-189`.
- `completionRationalPrime (place : FinitePlace K) : Nat.Primes :=
  Rat.HeightOneSpectrum.primesEquiv (comap (k := ℚ) place).maximalIdeal` —
  `LeanFormal/IUT/ABCBridge/Geometry/FinitePlacePadicScalarStructure.lean:24-26`.
  The predicate tests `.val`, so the `p` it can ever accept is a rational prime.

**Companion declarations (same file / next file)**

| declaration | location | content |
|---|---|---|
| `NativeBadPrimeData (p) := ∀ b, (completionRationalPrime (nativeBadToKPlace T b)).val = p` | `Mzk1NativeBadPrimeActual.lean:21-24` | the K-place form |
| `nativeBadToKPlace_completionRationalPrime : completionRationalPrime (nativeBadToKPlace T b) = completionRationalPrime b.1` | `Mzk1NativeBadPrimeSourceActual.lean:19-25` | **lift-independence** of the prime |
| `nativeBadPrimeData_of_moduliFixed : NativeBadModuliFixedPrime T p → NativeBadPrimeData T p` | `:31-38` | one direction |
| `nativeBadPrimeData_iff_moduliFixed : NativeBadPrimeData T p ↔ NativeBadModuliFixedPrime T p` | `Mzk1NativeBadPrimeIffActual.lean:18-24` | **the two forms are equivalent** |

Consequences of the equivalence: no reformulation through a chosen lift can be weaker, and
`nativeBadToKPlace` being an arbitrary `Classical.choose` (`VbadPlaceIndexingActual.lean:71-85`)
cannot help — `nativeBadToKPlace_completionRationalPrime` kills exactly the lift dependence and
leaves the `b` dependence intact.

Status rows only (no proofs): `Mzk1NativeBadModuliFixedPrimeAttemptActual.lean:6-11`,
`Mzk1NativeBadPrimeDataSourceActual.lean:7-10`, `Mzk1NativeBadPrimeSourceRowsActual.lean:7-9`,
`Mzk1NativeBadPrimeInputActual.lean:7-9`, `Mzk1UnitMassRowsActual.lean:11` — all record
"GAP: paper fixed-p moduli input".

## 2. Does `T.arithmetic` determine a single rational prime for all Bad indices?

**No — and not only `T.arithmetic`; the whole native datum does not.** Four independent facts:

**(2.1) The bad set is not arithmetic data at all.**
`InitialThetaArithmeticData` has exactly `Fmod, F, K`, their instances, `tower`, `curve`
— `LeanFormal/IUT/IUTI/InitialTheta/ArithmeticData.lean:62-81`. There is no `V_mod_bad`.
The bad set lives in the tuple: `SourceSignQuotientData` field `V_mod_bad`
(`SourceCompletion.lean:73-86`, copied at `:248-251`), re-exported by the tuple
(`SourceDefinition31Quantifiers.lean:1624-1625`) and by `nativePlaceSelection`
(`SourceDefinition31NativeContractBridgeReduction.lean:108-119`, with
`@[simp] nativePlaceSelection_V_mod_bad : (nativePlaceSelection T).V_mod_bad = T.tuple.source.V_mod_bad`).
`N8Closure.nativePlaceSelection` is a definitional alias (`NativeSourceReductionActual.lean:48-52`).
So

```
Bad (nativePlaceSelection T)  =  {q : FinitePlace T.arithmetic.Fmod // q ∈ T.tuple.source.V_mod_bad}
```

up to delta, i.e. the predicate **depends only on the source field `V_mod_bad`** — never on
`K`, `F`, the curve, the tower, or any clause.

**(2.2) The only source constraints are per place.** `SourcePlaceSelection`
(`SourcePlaceSelection.lean:31-37`) has exactly three fields: `V_mod_bad`,
`V_mod_bad_odd_residue_characteristic : ∀ p ∈ V_mod_bad, Odd (residueCharacteristic p)`,
`V_mod_bad_nonempty`. Clause (b) adds, *for each F-place over a bad place*,
multiplicative reduction, a q-comparison witness, and `Nat.Coprime l.value (residueCharacteristic …)`
(`SourceDefinition31Quantifiers.lean:959-975`). Oddness, nonemptiness, coprimality to `l`, and
per-place reduction are all **per-index** conditions; none is an equality between two indices.

**(2.3) Uniqueness holds; existence does not.** `Bad` is nonempty
(`SourcePlaceSelection.lean:37`, a field of the record; concrete instance at
`S1730BadSetWithoutLActual.lean:159-161`).
Hence if `NativeBadModuliFixedPrime T p` and `NativeBadModuliFixedPrime T p'` then `p = p'`
(apply both at one `b`). Also, if `¬ p.Prime` then the predicate is false (the RHS is always
a prime). So the data determines **at most one** prime, never **at least one**: there is no
choice to make, only a constancy to prove.

**(2.4) The exact equivalent form (the obstruction).** With `f b := (completionRationalPrime b.1).val`:

```lean
-- paper-level sketch, one line each way
theorem exists_iff_const :
    (∃ p, NativeBadModuliFixedPrime (T := T) p) ↔ ∀ b b', f b = f b'
```

- (→) `⟨p, hp⟩ ↦ fun b b' => (hp b).trans (hp b').symm`;
- (←) pick `b₀` from `(nativePlaceSelection T).V_mod_bad_nonempty` and set `p := f b₀`;
  constancy gives `f b = f b₀`.
This is the exact content of "a single rational prime for all Bad indices", and it is the
only thing `NativeBadModuliFixedPrime` (equivalently `NativeBadPrimeData`) adds to the source.

## 3. Truth value: the obstruction with concrete source-legal witnesses

### 3.1 Not TRUE: source-legal bad sets with several distinct rational primes

The project's concrete admissible curve is the S1667 curve; its full bad moduli set is
**{3, 5, 7}** as three actual rational places
(`S1729FullBadPlaceActual.lean:703-706`), with
`S1729Selection l : SourcePlaceSelection (S1724InitialThetaArithmeticData l)`
(`:782-788`), and `Fmod = ℚ` for that arithmetic
(`S1720SourceArithmeticActual.lean:326-336`; the unconditional assembly is
`S1724PaperArithmeticActual.lean:21-23`).

- The three places are pairwise distinct, proved through their residue characteristics
  `3, 5, 7`: `S1729Three_ne_five`/`S1729Three_ne_seven`/`S1729Five_ne_seven`
  (`S1729FullBadPlaceActual.lean:731-751`), using
  `concreteThreePlace_residueCharacteristic : = 3` (`:151-153`),
  `S1712ConcreteFivePlace_residueCharacteristic : = 5` (`S1712OddResidueActual.lean:15-21`),
  `concreteSevenPlace_residueCharacteristic : = 7` (`S1717PlaceSevenD5Actual.lean:138-140`).
- `S1730Selection l` removes the place of residue characteristic `l`, so for **every**
  `l ≥ 5` its bad set still has ≥ 2 distinct primes: `{3,7}` (l = 5), `{3,5}` (l = 7),
  `{3,5,7}` (l ≥ 11) — `S1730BadSetWithoutLActual.lean:65-70`, `:170-179`,
  `:203-219` (three distinct places), `:225-232` (the selection), `:240-246`
  (`Fintype (Bad (S1730Selection l))`).
- Therefore, **for every `l : PrimeGeFive`**, there is a `SourcePlaceSelection` over actual
  arithmetic data whose bad set violates the constancy of (2.4):

```lean
-- sketch: the refutation at the selection layer
theorem not_exists_fixed_prime_S1730 (l : PrimeGeFive) :
    ¬ ∃ p, ∀ b : Bad (S1730Selection l),
        (completionRationalPrime b.1).val = p
```

  Proof shape: `concreteThreePlace` is always in the set (`l ≥ 5`, so 3 is never removed) and
  one of `concreteSevenPlace` (l ≠ 7) / `concreteFivePlace` (l = 7) is in the set; apply the
  hypothesis at both and derive `3 = 7` / `3 = 5` after computing
  `(completionRationalPrime concreteThreePlace).val = 3`, `… = 7`, `… = 5`.

### 3.2 Not FALSE either: legal singleton bad sets

`SourcePlaceSelection.singleton A p hodd` (`SourcePlaceSelection.lean:39-54`) is a legal
selection with `V_mod_bad = {p}` for any place of odd residue characteristic. Any `T` whose
source bad set is a singleton satisfies `NativeBadModuliFixedPrime T p` at `p =` that prime
(and only there). So there is no "always false" statement either; the truth value is a
property of the chosen `V_mod_bad`.

### 3.3 Transport to the T-level predicate, and the exact logical status

Since `Bad (nativePlaceSelection T)` is definitionally determined by
`T.tuple.source.V_mod_bad` (§2.1), **for any `T` with
`T.tuple.source.V_mod_bad = S1730VModBad l` the predicate fails for every `p`**. Such a `T`
is not constructed in the tree: the tuple copies `V_mod_bad` from the sign-quotient record
(`SourceDefinition31Quantifiers.lean:1612-1628`; `SourceClauseConstructors.lean:1105-1127`
with `sourceData_tuple_V_mod_bad` at `:1159-1162`), and the only constructors of a native
tuple consume a fully supplied `SourceCompletion` / `SourceClauseConstructionWitness`
(`SourceCompletion.lean:601-609`; `SourceClauseConstructors.lean:1088-1098`). The universal
gate is an unproved Prop by design (`SourceDefinition31Quantifiers.lean:1765-1775`
"No constructor is claimed here"; `SourceNativeInitialThetaExists` at `:1726-1733`).

Status therefore, precisely:

- `∀ T p, NativeBadModuliFixedPrime T p` — **not a theorem**; false as soon as a `T` packs a
  multi-prime bad set, and its `p` cannot be free anyway.
- `∀ T, ∃ p, NativeBadModuliFixedPrime T p` — **not derivable** from the source type; it is the
  constancy (2.4), which §3.1 refutes at the selection layer.
- `NativeBadModuliFixedPrime T p → Bot` for concrete `T` — **not available**, because no `T`
  is constructed (`SourceNativeInitialThetaExists` has no proof; both directions of
  `sourceNativeInitialThetaExists_iff_packaged`, `:1746-1748`, are packaging only).
- Hence: an **interface/extra input**, not a source consequence, and one that the paper's own
  concrete bad set contradicts.

### 3.4 The two small glue lemmas a *formal* refutation still needs

The tree proves the residue characteristics (3, 5, 7) but not the corresponding
`completionRationalPrime` values for the rational places. A formal refutation needs one of:

```lean
theorem completionRationalPrime_rationalFinitePlace (p : ℕ) [Fact p.Prime] :
    completionRationalPrime (rationalFinitePlace p) = ⟨p, Fact.out⟩
-- rationalFinitePlace := FinitePlace.mk ((primesEquiv).symm ⟨p, Fact.out⟩)
--   (FinitePlaceFullPrimePacket.lean:19-22), same shape as concreteThreePlace
--   (S1729FullBadPlaceActual.lean:92-102) and concreteSevenPlace
--   (S1717PlaceSevenD5Actual.lean:79-89); prove by unfolding, comap = id on 𝓞 ℚ,
--   and Equiv.apply_symm_apply — the computation already used for natGenerator at
--   S1729:113-117 and FreyTateAnalyticInput.lean:910-911.
```

or the general bridge `(completionRationalPrime place).val = residueCharacteristic place`
(no such lemma exists in `LeanFormal` today: the only `completionRationalPrime` lemmas are the
definition and `completionRationalPrime_comap`/`completionRationalPrime_eq_of_comap_eq`,
`FinitePlaceRelativeCommonPrime.lean:18-21`, `FinitePlaceCommonPrimeCompletion.lean:69-75`).
This is a formalization gap only; it does not affect the verdict.

## 4. Why the existing files only give a residue-prime projection

The only index-invariant of a bad place that the data *always* provides is its rational prime
under the place, and that is a **function**, not a constant:

- `badRationalPrime : Bad (nativePlaceSelection T) → Nat`
  := `rationalPrimeOfFinitePlace (K := T.arithmetic.K) ((nativeBadToKPlace T b).maximalIdeal)`
  (`Mzk1PaperLabelBadIndexBridgeActual.lean:33-35`), with the definitional form
  `= Ideal.absNorm (…under Int)` (`:37-40`).
  The file's own docstring says it: "**this is a residue-prime projection, not the paper
  theta-label map**; a canonical `Bad → ProcessionLabel l` map is not present in
  `T.arithmetic`" (`:5-15`), and its `BadThetaLabelMap` interface (`:48-51`) has no
  inhabitant.
- The general projection layer is `rationalPrimeOfFinitePlace` /
  `candidateLabelOfPlace` in `Mzk1PaperLabelProjectionActual.lean:32-65`, with the
  docstring: "no canonical map from finite places to paper theta labels in
  `T.arithmetic`; the paper label group is not a residue-character group" (`:16-18`), and
  again an uninhabited interface `PaperLabelProjectionInterface` (`:67-72`).
- Structurally: `completionRationalPrime` is a `def` **of the place**
  (`FinitePlacePadicScalarStructure.lean:24-26`), so the projection `b ↦ f b` is always
  available and always index-dependent. Index-*independence* is a new universal equality
  over the index type, which no per-place construction can produce.
- The two genuine reductions that *are* green do not touch that:
  (a) `nativeBadToKPlace_completionRationalPrime` removes the dependence on the arbitrary
  lift `Classical.choose (comap_surjective …)` (`Mzk1NativeBadPrimeSourceActual.lean:19-25`,
  `VbadPlaceIndexingActual.lean:71-85`); (b) `badRationalPrime_function`
  (`Mzk1PaperLabelBadIndexBridgeActual.lean:42-46`) only exhibits a function. And
  `nativeBadPrimeData_iff_moduliFixed` (`Mzk1NativeBadPrimeIffActual.lean:18-24`) proves the
  two available formulations are *the same* condition, so no weaker phrasing exists inside
  the current interfaces.

## 5. Consequence for #10 and exact repairs

Everything conditional in #10 hangs on exactly this predicate:
`nativeBadToKPlaceAtPrime` (`Mzk1NativeBadPrimeActual.lean:26-30`),
`badPlaceCommonPrimeUnitMassProduct_eq_one` (`:32-40`),
`NativeFinitePlaceDictionaryData.p` + `primeData`
(`Mzk1NativeFinitePlaceDictionaryActual.lean:24-42`), and `nativeCarrierFamily`
(`Mzk1P1LocalUnitProductTActual.lean:24-29`).
So as long as `NativeBadPrimeData` is the interface, #10 is conditional on an input the
source refutes.

But the fixed prime is **not needed for the unit-mass identity**:

- `localUnitMassProduct (K : ι → Type*) := ∏ i, (normalizedHaar (unitBall)).toReal` and
  `localUnitMassProduct_eq_one` are stated for an *arbitrary* family of local fields
  (`Mzk1LocalUnitMassProductActual.lean:12-30`) — no common base field, no common `p`.
- The Bad-indexed version is already `p`-free and unconditional in the family:
  `badPlaceUnitMassProduct_eq_one (K : Bad … → Type u)` with only per-index
  `NormedField/IsUltrametricDist/ProperSpace/MeasurableSpace/BorelSpace` instances
  (`Mzk1BadPlaceUnitMassProductActual.lean:19-33`).
- The single `p` enters only through the chosen carrier
  `CommonPrimeCompletion = NormalizedCompletion place.val` with
  `place : FinitePlaceAtPrime K p` (`FinitePlaceCommonPrimeCompletion.lean:17-20`), used in
  `Mzk1NativeBadPrimeActual.lean:27-40`. That is a carrier choice, not a mathematical
  requirement of the product.

Repairs, in order of preference:

1. **Drop the common prime for #10**: instantiate `badPlaceUnitMassProduct` with
   `fun b => NormalizedCompletion (nativeBadToKPlace T b)`
   (`FinitePlaceNormalizedCompletion.lean:25-59` supplies `NormedField` via
   `NontriviallyNormedField`, `IsUltrametricDist`, `ProperSpace` per place). Remaining
   instance work: `MeasurableSpace`/`BorelSpace` on `Completion` (the same hypotheses the
   current common-prime version also assumes explicitly, `Mzk1NativeBadPrimeActual.lean:36-37`).
2. **If a common `ℚ_p` is genuinely required downstream**, replace the fixed prime by the
   prime **fibers**: `∏ p, ∏_{b : (completionRationalPrime b.1).val = p}`. This is the route
   already recorded as R7 ("必要时构造 prime fibers",
   `coord/P7-SIX-GAPS-ROUTES-20261114.md:556`) and the A7 note
   (`coord/P7-GATE-REVIEW.md:402`: "所有 Bad 模位固定同一 p 未必成立；若为假，则 #10 的 unitMass
   归一化必须改用按 prime 分组或逐 prime product").
3. **Do not add "fixed `p`" as a source field.** `S1730Selection l` satisfies the current
   `SourcePlaceSelection` fields yet has bad set `{3,7}`/`{3,5}`/`{3,5,7}`; a fixed-prime
   field would make that already-formalized source selection unconstructible. The paper's
   `V^bad_mod` is a set of places of bad reduction, not a fiber over one prime.

## 6. Evidence table

| # | fact | file:line |
|---|---|---|
| 1 | definition of `NativeBadModuliFixedPrime` | `tmp/sheaf/xif/paper/Mzk1NativeBadPrimeSourceActual.lean:27-29` |
| 2 | `NativeBadPrimeData` (K-place form) | `tmp/sheaf/xif/paper/Mzk1NativeBadPrimeActual.lean:21-24` |
| 3 | iff of the two forms | `tmp/sheaf/xif/paper/Mzk1NativeBadPrimeIffActual.lean:18-24` |
| 4 | prime invariant under lift choice | `tmp/sheaf/xif/paper/Mzk1NativeBadPrimeSourceActual.lean:19-25` |
| 5 | `Bad` = subtype of `V_mod_bad` | `LeanFormal/IUT/IUTI/InitialTheta/SourcePlacePartitionReduction.lean:187-189` |
| 6 | `SourcePlaceSelection`'s three fields (odd + nonempty only) | `LeanFormal/IUT/IUTI/InitialTheta/SourcePlaceSelection.lean:31-37` |
| 7 | singleton legal selection | `LeanFormal/IUT/IUTI/InitialTheta/SourcePlaceSelection.lean:39-54` |
| 8 | `V_mod_bad` is a `SourceSignQuotientData` field | `LeanFormal/IUT/IUTI/InitialTheta/SourceCompletion.lean:73-86`, `:248-251` |
| 9 | tuple copies `V_mod_bad` | `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1624-1625` |
| 10 | `nativePlaceSelection` is that projection | `LeanFormal/IUT/IUTI/HodgeTheater/SourceDefinition31NativeContractBridgeReduction.lean:108-119` |
| 11 | `N8Closure.nativePlaceSelection` alias | `tmp/sheaf/n8/closure/NativeSourceReductionActual.lean:48-52` |
| 12 | `NativeBadLift` (explicit lying-over, absent from tuple) | `tmp/sheaf/n8/closure/NativeSourceReductionActual.lean:64-71` |
| 13 | arithmetic data has no `V_mod_bad` | `LeanFormal/IUT/IUTI/InitialTheta/ArithmeticData.lean:62-81` |
| 14 | Clause (b) constraints are per F-place | `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:959-975` |
| 15 | no native-tuple constructor; A2 gate unproved | `LeanFormal/IUT/IUTI/InitialTheta/SourceDefinition31Quantifiers.lean:1726-1733`, `:1765-1775` |
| 16 | bad set `{3,5,7}` as actual places | `tmp/sheaf/xif/paper/S1729FullBadPlaceActual.lean:703-706` |
| 17 | `S1729Selection` = legal selection with that set | `tmp/sheaf/xif/paper/S1729FullBadPlaceActual.lean:782-788` |
| 18 | pairwise distinctness via residue char 3/5/7 | `tmp/sheaf/xif/paper/S1729FullBadPlaceActual.lean:731-751`; `S1712OddResidueActual.lean:15-21`; `S1717PlaceSevenD5Actual.lean:138-140` |
| 19 | `S1730Selection l` with `{3,5,7} \ {l}`, always ≥2 primes | `tmp/sheaf/xif/paper/S1730BadSetWithoutLActual.lean:65-70`, `:170-179`, `:203-219`, `:225-232` |
| 20 | `Fintype (Bad (S1730Selection l))` | `tmp/sheaf/xif/paper/S1730BadSetWithoutLActual.lean:240-246` |
| 21 | `Fmod = ℚ` for that arithmetic | `tmp/sheaf/xif/paper/S1720SourceArithmeticActual.lean:326-336` |
| 22 | residue-prime projection (function only) | `tmp/sheaf/xif/paper/Mzk1PaperLabelBadIndexBridgeActual.lean:5-15`, `:33-46`, `:48-51` |
| 23 | label projection gap | `tmp/sheaf/xif/paper/Mzk1PaperLabelProjectionActual.lean:16-18`, `:32-72` |
| 24 | `p`-free product identity | `tmp/sheaf/xif/paper/Mzk1LocalUnitMassProductActual.lean:12-30`; `Mzk1BadPlaceUnitMassProductActual.lean:19-33` |
| 25 | common-prime carrier choice | `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceCommonPrimeCompletion.lean:17-20`; `FinitePlaceNormalizedCompletion.lean:25-59` |
| 26 | recorded A7 note / R7 route | `coord/P7-GATE-REVIEW.md:402`; `coord/P7-SIX-GAPS-ROUTES-20261114.md:556` |

## 7. Caveats and next step

- This pass ran **no build and no `#check`**; it is source inspection. Nothing above is
  presented as kernel-checked, and no axiom/sorry claim is made for any declaration.
- §3.1's refutation is fully formal at the `residueCharacteristic` level (3, 5, 7 are proved
  constants and the places are proved distinct). Its transfer to `completionRationalPrime`
  needs the one small lemma of §3.4, which is **not** in the tree.
- The T-level statement is *conditional*: no `SourceNativeInitialThetaData` inhabitant is
  constructed in the tree,
  so "some `T` violates it" cannot be exhibited today; what is proved is that the source type
  does not entail it and that a source-legal bad set refutes it.
- Next step (one package): prove `completionRationalPrime_rationalFinitePlace` (§3.4), then
  `not_exists_fixed_prime_S1730` (§3.1), and in parallel switch #10 to repair (1): the
  `p`-free `badPlaceUnitMassProduct` over `fun b => NormalizedCompletion (nativeBadToKPlace T b)`,
  resolving the `MeasurableSpace`/`BorelSpace` instances. Record the result as
  "fixed prime = refuted source input; #10 restored without it".
