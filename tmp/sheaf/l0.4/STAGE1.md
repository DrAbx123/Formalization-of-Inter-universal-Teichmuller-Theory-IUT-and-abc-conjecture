# L0.4 - actual log square / unscaled image / same-prime scaling / unit target (stage 1)

- Node: `L0.4`
- Stage: 1 only (this record). No production file edited; no Lean compiled in this session.
- Version anchor: git HEAD `9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee`; project Lean `v4.32.2`,
  Mathlib `v4.32.2` (SETUP.md).
- Actual consumer: `L1-F5` SourceLogKummer, i.e. the frozen identification card
  `SourceFrobeniusLogKummerIdentificationCard l LogKummerMap.logKummerData`.
- Method: SHEAF node-local stages, consumer first. This file freezes the L0.4 target, the donors
  actually available at the pinned sources, the exact gaps, and one smallest next statement.
- Date: 2026-10-22.
- Read this session: `logs/coordination/l04-implementation-playbook-20261021.md`, `tmp/sheaf/l1-f5/STAGE1.md`,
  and the modules cited in section 4. No whole-repo audit.

## 1. The actual consumer declaration (L1-F5 SourceLogKummer)

Definition: `Example36LogKummerMap.lean:339-363`. Alias: `Example36SourceLogKummerIdentification.lean:206-207`:

```lean
abbrev SourceLogKummerIdentificationCard (l : PrimeGeFive) :=
  SourceFrobeniusLogKummerIdentificationCard l LogKummerMap.logKummerData
```

Ten fields, and which side must supply them:

| # | field | type | supplier |
|---|---|---|---|
| 1 | `SourcePrincipalUnits` | `Type` | L1-F5: `sourcePrincipalUnits l` (`Example36SourceLogKummerIdentification.lean:100`) |
| 2 | `sourceFrobenius` | `SourcePrincipalUnits → SourcePrincipalUnits` | L1-F5: `sourceFrobenius l` (:105-108) |
| 3 | `SourceLogShell` | `Type` | L1-F5: `sourceLogShell l` (:110-111) |
| 4 | `sourceLogKummer` | `SourcePrincipalUnits → SourceLogShell` | L1-F5: `sourceLogKummerShell l` (:113-114) |
| 5 | `sourcePScaling` | `SourceLogShell → SourceLogShell` | L1-F5: `sourcePScaling l` (:123-128) |
| 6 | `carrierEquiv` | `SourcePrincipalUnits ≃ data.H` | **L0.4** (unit target, S4) |
| 7 | `shellEquiv` | `SourceLogShell ≃ data.logShell` | **L0.4** (image target, S2/S4) |
| 8 | `frobenius_intertwines` | `∀ h, carrierEquiv (sourceFrobenius h) = data.frobenius (carrierEquiv h)` | **L0.4** (unit/power square) |
| 9 | `logKummer_intertwines` | `∀ h, shellEquiv (sourceLogKummer h) = data.logKummer (carrierEquiv h)` | **L0.4** (log square, S1/S4) |
| 10 | `pScaling_intertwines` | `∀ x, shellEquiv (sourcePScaling x) = data.pScaling (shellEquiv x)` | **L0.4** (scaling square, S3) |

Checked status facts (grep over `LeanFormal` this session):

- The card name occurs only at its definition (`Example36LogKummerMap.lean:339`), at the alias
  (`Example36SourceLogKummerIdentification.lean:206-207`), and in docstrings. **No inhabitant exists and no
  theorem consumes one.**
- `example36LogKummerMap_summary` (`Example36LogKummerMap.lean:376-393`) proves
  `∀ l, Nonempty (SourceFrobeniusLogKummerCard l)` - the *structural* card at
  `Example36LogShellFrobeniusAction.lean:235-250`. That is a different obligation; it neither inhabits nor
  consumes the identification card.
- `Project.lean:518-519` imports both definition files. The card type is in the production import closure;
  the identification obligation is not discharged there.

Two target-design facts that the consumer card does not encode:

1. The card admits a trivial self-inhabitant (`SourcePrincipalUnits := data.H`, all maps `:=` the `data`
   maps, all equivalences `Equiv.refl`). This is not a source identification and is excluded by SHEAF
   section 4 and section 13. The L0.4 deliverables must therefore be stated about the actual `ℚ_[l]`
   carriers; a bare `Nonempty card` is not the target and cannot be reported as one.
2. `carrierEquiv` and `shellEquiv` are bare `Equiv`s; the card enforces neither additivity, multiplicativity,
   nor log compatibility of the source maps. Those are exactly S1-S4 below and must be recorded as theorems.

## 2. Frozen objects (exact terms; do not redefine)

| object | term | location |
|---|---|---|
| source field | `sourceLocalField l := ℚ_[l.value]` | `Example36SourceLogKummerIdentification.lean:99` |
| source principal units | `sourcePrincipalUnits l := principalUnits (K := sourceLocalField l)` | :100 |
| source log-Kummer | `sourceLogKummer l u := principalUnitLog (K := sourceLocalField l) u` | :102-103 |
| source Frobenius | `sourceFrobenius l u := <(u : (Integers _)) ^ l.value, _>` | :105-108 |
| source log-shell | `sourceLogShell l := principalUnitLogImage (K := sourceLocalField l) l.value` | :110-111 |
| source shell map | `sourceLogKummerShell l u := <sourceLogKummer l u, _>` | :113-114 |
| source l-scaling | `sourcePScaling l x := <(l.value : sourceLocalField l) * x, _>` | :123-128 |
| concrete field | `concreteLogShellField := NormalizedCompletion concretePlace` | `Example36LogShellLattice.lean:94` |
| normalization alias | `NormalizedCompletion place := Completion place` | `ABCBridge/Geometry/FinitePlaceNormalizedCompletion.lean:25` |
| concrete H | `data.H = principalUnits (K := concreteLogShellField)` | `Example36LogKummerMap.lean:232`, :240-242 |
| concrete shell | `principalUnitLogShell` = range over `principalUnits` of `unitLog` | `Example36LogShellLattice.lean:115-132`, :136-141 |
| concrete log-Kummer | `logKummer u = <unitLog (u : (Integers _)), _>` | `Example36LogKummerMap.lean:70-75` |
| concrete Frobenius | `principalUnitFrobenius u := u ^ concreteRationalPrime` | `Example36LogShellFrobeniusAction.lean:68-71` |
| concrete p-scaling | `principalUnitLogShellFrobenius x := <(concreteRationalPrime : _) * x, _>` | :114-137 |
| rational prime | `concreteRationalPrime := (completionRationalPrime concretePlace).val` | `Example36LogShellLattice.lean:97` |
| prime value | `concretePlace_rationalPrime_eq_five : concreteRationalPrime = 5` | `Example36SourceLogKummerIdentification.lean:218-225` |
| source label | `fivePrimeLabel : PrimeGeFive`, `value = 5` | `Example36SourceEtaleThetaTheory.lean:101` |

Model conditions forced by the source (SHEAF section 7 requires them to appear):

- **M1 (same prime).** Source shell/scaling are indexed by `l.value` (:110-111, :123-128); target
  shell/scaling by `concreteRationalPrime` (`Example36LogShellLattice.lean:97`,
  `Example36LogShellFrobeniusAction.lean:114-137`). At the consumer `l.value = concreteRationalPrime = 5`.
  No theorem turns `l.value`-scaling into `p`-scaling for `l.value ≠ p`, and none can be additive:
  additivity already gives `n`-scaling by the *same* `n` (playbook section 3).
- **M2 (model).** The target place is the concrete Gaussian place over 5. `sourceComparison_obstruction`
  (:196-204) records `concreteLogShellField = concreteHeightOneSpectrum.adicCompletion GaussianField` and
  `localCarrier.parameter.q = (l.value : ℚ_[l.value])`; `Example36SourceLogLinkCompatibility.lean:51-62`
  states that no continuous ring map `ℚ_[l] →+* concreteLogShellField` is constructed for general `l`.
  A statement quantified over all `l : PrimeGeFive` against this fixed target is therefore not the target.
- **M3 (e is constructed).** The comparison `e : B →+* C` must come from actual data:
  `sourceTheaterScalarMap` (`Example36SourceLogLinkCompatibility.lean:258`),
  `concretePlace_qFiveComparisonRingEquiv` (`Example36SourceLogKummerIdentification.lean:263`),
  `rationalCompletionPadicEquiv` (`ABCBridge/Geometry/FinitePlacePadicScalarStructure.lean:35`),
  `normalizedCompletionRingEquiv` (`FinitePlaceNormalizedCompletion.lean:62`). It may not be a card field.

## 3. The exact L0.4 targets

Notation: `B`, `C` are complete nonarchimedean normed fields over the *same* `ℚ_[p]`, with `CharZero`,
`IsUltrametricDist`, `ProperSpace`; `e : B →+* C`; `he : Isometry e`; `u : (Integers B)`.
The four statements are the object-level content of playbook section 14 package B.

### S1 - the log square for every unit

```lean
-- generic form: green donor (IntegralUnitLogarithmFunctoriality.lean:62)
theorem unitLog_map (e : K →+* L) (he : Isometry e) (u : (Integers K)) :
    e (unitLog u) = unitLog (integralUnitMap e he u)
```

Note: `e` need only be a ring hom plus an `Isometry`; it need NOT be an equivalence. The type-class
hypotheses are `NormedField`, `IsUltrametricDist`, `CharZero`, `CompleteSpace`, `ProperSpace` on both
sides, `[Fact p.Prime]`, and `NormedAlgebra ℚ_[p]` on both sides. **Consumer instance: OPEN** (section 8).

### S2 - the unscaled image `e_L`

Target carrier: `L_B := Set.range (unitLog (K := B))`, equivalently the `ℤ_[p]`-submodule
`unitLogLattice` (`UnscaledUnitLogLattice.lean:45`, carrier equality `coe_unitLogLattice_eq_range` :66).

```lean
noncomputable def l04_logImageEquiv (e : B ≃+* C) (he : Isometry e) :
    (unscaledLogImage (p := p) (K := B)) ≃ (unscaledLogImage (p := p) (K := C))
theorem l04_logImageEquiv_val (x : unscaledLogImage (p := p) (K := B)) :
    (l04_logImageEquiv e he x : C) = e (x : B)
theorem l04_logImageEquiv_unitLog (u : (Integers B)ˣ) :
    l04_logImageEquiv e he ⟨unitLog u, _⟩ =
      ⟨unitLog (integralUnitMap e.toRingHom he u), _⟩
```

Status: green generically as `LogUnscaledImageConsumer.unscaledLogImageEquiv` (:47), `_val` (:71),
`_unitLog` (:77); additive form on the *scaled* shell is `integralLogShellAddEquivOfRingEquiv`
(`IntegralLogShellIndexArithmetic.lean:181`); additive form on the unscaled `ℤ_[p]`-lattice is
`unitLogLatticeAddEquiv` (`LogCarrierNaturality.lean:132`). **Consumer instance: OPEN** (no cross-field
instance at `(ℚ_[5], concreteLogShellField)`; the available instances are the identity pair, see 4b).

### S3 - the same-prime scaling square

Target: for the lattice form, `∀ n x, e_L (n • x) = n • e_L x` (free from additivity); for the
consumer functions, with `sourcePScaling x = (l.value) * x` and `data.pScaling x = (concreteRationalPrime) * x`:

```lean
theorem l04_pScaling_square (x : sourceLogShell l) :
    e_L (sourcePScaling l x) = data.pScaling (e_L x)
```

Status: generic `n`-scaling is `map_nsmul` for an `AddEquiv`; the function-level square is
`map_mul` + `map_natCast`, with `l.value = concreteRationalPrime = 5` (M1). **Consumer instance: OPEN**
only because `e_L` itself is missing (G1/G3), not because of new analysis.

### S4 - principal-unit restriction and the unit carrier

Both shells are `unitLog` images of principal units:

- source: `principalUnitLogImage (K := ℚ_[l]) l.value = unitLog '' principalUnits` by
  `principalUnitLogImage_eq_unitLog_image` (`Example36LogDomainActual.lean:265-276`);
- target: `principalUnitLogShell = Set.range (fun u : principalUnits => unitLog u)` by definition
  (`Example36LogShellLattice.lean:115-132`), membership `principalUnitLogShell_mem_iff` (:136-141).

`integralUnitMap_mem_principalUnits` (`IntegralUnitLogarithmFunctoriality.lean:43-48`) keeps the transported
unit principal, so an isometry ring hom restricts to a map of shells; the generator square is `Subtype.ext`
of S1. The unit target `carrierEquiv` is the multiplicative equivalence `principalUnits B ≃* principalUnits C`,
built from `integralUnitMap` and its inverse; it needs `e` to be an equivalence.
Status: constituents green; pair-level construction **OPEN**.

## 4. Green donors

All `.olean`s below exist under `.lake/build/lib/lean/...` and are not older than their sources
(checked this session). No donor file contains `sorry`, `admit`, or `axiom` (grep). This is historical
build evidence, not a fresh compile (section 7).

| # | declaration | location | use | olean |
|---|---|---|---|---|
| 1 | `unitLog_map` | `IntegralUnitLogarithmFunctoriality.lean:62` | S1 generic | Y |
| 2 | `integralRingMap`, `integralUnitMap`, `integralUnitMap_val` | :28-34, :37-38, :40-41 | unit transport | Y |
| 3 | `integralUnitMap_mem_principalUnits` | :43-48 | S4 membership | Y |
| 4 | `map_mem_integralLogShell` | :82-89 | scaled-shell forward | Y |
| 5 | `unitLog_eq_log1p` | `IntegralUnitLogarithm.lean:125-128` | principal log = full log | Y |
| 6 | `principalUnitLog_pow`, `unitLog_mul/pow/one`, `unitLog_eq_withExponent` | :44-53, :118-122, :135-140 | power law | Y |
| 7 | `unitLogLattice`, `coe_unitLogLattice_eq_range`, `mem_unitLogLattice_iff` | `UnscaledUnitLogLattice.lean:45, :66, :86` | `L_B` carrier | Y |
| 8 | `integralLogShellAddEquivOfRingEquiv` | `IntegralLogShellIndexArithmetic.lean:181` | scaled-shell equivalence | Y |
| 9 | `logShellIntegerQuotientAddEquivOfRingEquiv`, `logShellIntegerIndex_eq_of_isometry_ringEquiv` | :226, :238 | quotient/index | Y |
| 10 | `isometry_ringEquiv_symm`, `unscaledLogImage`, `unscaledLogImageEquiv`, `_val`, `_unitLog` | `LogUnscaledImageConsumer.lean:21, :37, :47, :71, :77` | S2 generic | Y |
| 11 | `unitLog_naturality`, `unitLogLatticeAddEquiv` | `LogCarrierNaturality.lean:61, :132` | S1/S2 at identity pair only (4b) | Y |
| 12 | `principalUnitMap`, `principalUnitLog_naturality` | `LogKummerK1K2.lean:43, :54` | S1/S4 at identity pair only (4b) | Y |
| 13 | `principalUnitLog`, `principalUnitLogImage` | `Example36LogDomainActual.lean:70, :118` | source log/shell | Y |
| 14 | `principalUnitLogImage_eq_unitLog_image` | :265-276 | S4 carrier bridge | Y |
| 15 | `principalUnitLogImage_subset_unitLogLattice` | :305-313 | `L` into unscaled lattice | Y |
| 16 | `principalUnitLogShell`, `_mem_iff`, `unitLog_principalUnit_eq_log1p` | `Example36LogShellLattice.lean:115, :136, :145` | target shell | Y |
| 17 | `logKummer`, `logKummer_surjective`, `logKummerData`, simp lemmas | `Example36LogKummerMap.lean:70, :86, :231, :240-258` | consumer data | Y |
| 18 | `principalUnitFrobenius`, `unitLog_principalUnitFrobenius_log`, `principalUnitLogShellFrobenius` (+`_apply`, `_p_mul_mem`, `_mk`) | `Example36LogShellFrobeniusAction.lean:68, :99, :114, :133, :140, :147` | S3 target side | Y |
| 19 | `principalUnitLog_pow`, `sourceLogKummer_frobenius`, `sourcePScaling`, `sourceLogKummer_square`, `sourcePScaling_nontrivial` | target file `:81, :116, :123, :130, :145` | S3 source side | Y |
| 20 | `independentSourceFrobeniusLogKummerCard` | target file :182-190 | structural card only | Y |
| 21 | `concretePlace_rationalPrime_eq_five` | target file :218-225 | M1/M2 | Y |
| 22 | `concretePlace_completion_finrank_eq_one` | target file :232-235 | G1 input (relative) | Y |
| 23 | `concretePlace_qFiveComparisonRingEquiv`, `_norm`, `_norm_symm` | target file :263, :313, :319 | actual Q5 comparison + isometry | Y |
| 24 | `concretePlace_integersRingEquiv`, `_unitsEquiv`, `_principalUnitsEquiv` | target file :327, :335, :347 | Q5 carrier transports | Y |
| 25 | `sourceTheaterScalarMap`, `_eq_padicCompletionHom`, `_continuous`, `_norm`, `_mem_integers`, `_mem_principalUnits` | `Example36SourceLogLinkCompatibility.lean:258, :264, :269, :274, :282, :289` | actual `B → C` map | Y |
| 26 | `sourceTheater_unitLog_square`, `_scaledLog_square`, `_logShell_transport`, `sourceTheaterLogShellMap`, `_injective` | :300, :311, :324, :334, :359 | square at the actual map (continuous form) | Y |
| 27 | `unitLog_map_of_continuous`, `map_mem_integralLogShell_of_continuous`, `scaled_unitLog_map_of_continuous`, `integralLogShellTransport` | :123, :151, :181, :193 | form used at the source map | Y |
| 28 | `commonPrimeCompletionRingEquiv`, `isometry_commonPrimeCompletionRingEquiv` | `FinitePlaceCommonPrimeCompletion.lean:62, :66` | identity pair (4b) | Y |
| 29 | `normalizedCompletionRingEquiv` | `FinitePlaceNormalizedCompletion.lean:62` | normalization type synonym | Y |
| 30 | `normalizedCompletion_norm_le_one_iff`, `_lt_one_iff` | `FinitePlaceNormalizedIntegers.lean:58, :76` | G2 evidence | Y |
| 31 | `finrank_completion_rat`, `finrank_normalizedCompletion_rat`, `finrank_commonPrimeCompletion_rat_of_prime` | `RationalCommonPrimeFinrank.lean:42, :102, :110` | G1 | Y |
| 32 | `finrank_relativeNormalizedCompletion`, `finrank_commonPrimeCompletion_tower` | `FinitePlaceRelativePadicDegrees.lean:25, :42` | G1 | Y |
| 33 | `concreteGaussianFivePlace_relativeCompletionDegree_eq_one`, `_completion_finrank_eq_one` | `Example36GaussianSplitPlaceArithmetic.lean:1242, :1259` | G1 | Y |

### 4b. Identity-pair donors (green, but not cross-field)

`CommonPrimeCompletion place := NormalizedCompletion place.val` (`FinitePlaceCommonPrimeCompletion.lean:20`)
and `commonPrimeCompletionRingEquiv = RingEquiv.refl _` (:62). Hence `SourceCompletion place` and
`TargetCompletion place` (`LogCarrierNaturality.lean:40-41`) are the **same type**, and
`completionIsometryEquiv` is `refl`. Consequences:

- `LogCarrierNaturality.unitLog_naturality` (:61), `LogKummerK1K2.principalUnitLog_naturality` (:54) and
  `LogUnscaledImageConsumer.actualUnscaledLogImageEquiv` (:128) are identity squares at one type. They are
  green but are NOT an actual completion comparison; do not cite them as L0.4 cross-field naturality.
- `LogKummerK1K2.principalUnitMap` (:43) is `integralUnitMap refl`.

### 4c. Q_l candidates without olean (NOT green)

`SourceQlCarrierMap.lean`, `SourceQlEmbeddingConsumer.lean`, `SourceQlEmbeddingShellImage.lean`,
`SourceQlEmbeddingIntegralUnits.lean`, `SourceQlEmbeddingUnitFrobenius.lean`, `SourceQlUnitTransport.lean`,
`SourceQlEmbeddingShellQuotientComparison.lean` have no `.olean`, and `Project.lean` does not import them.
They are the general-place embedding design; their own headers state that whole-image equality is
equivalent to surjectivity (`SourceQlEmbeddingShellImage.lean` header). Not usable as evidence.

## 5. Precise gaps

**G1 - no actual `e` at the consumer pair.** No `Isometry` and no `Surjective` theorem for
`sourceTheaterScalarMap`; no `Module.finrank (PadicScalarField concretePlace) (NormalizedCompletion
concretePlace) = 1`; the only finrank fact is relative, over `Completion (comap concretePlace)`
(target file :232-235). Chain to close it: `finrank_commonPrimeCompletion_tower` +
`finrank_commonPrimeCompletion_rat_of_prime` + `concreteGaussianFivePlace_relativeCompletionDegree_eq_one`
give finrank 1; then `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` with the green injectivity
(:359) gives surjectivity, hence `RingEquiv`. Risk (unverified): the `FinitePlaceAtPrime` proof component
indexes the algebra instances (`FinitePlaceCommonPrimeCompletion.lean:17-18, :34-38`), so instance
restatement may be required.

**G2 - norm instances.** `concreteLogShellField` carries the spectral normalized norm
(`FinitePlaceNormalizedCompletion.lean:40-46`), while `concretePlace_norm_qFiveComparisonRingEquiv`
(target file :313) is an isometry for the *raw* `Completion` norm. Only unit-ball agreement is proved
(`normalizedCompletion_norm_le_one_iff` / `_lt_one_iff`). Exact missing statement if that route is taken:
norm equality across the two instances, or restatement on the raw `Completion` type. This gap is
**avoidable**: `sourceTheaterScalarMap_norm` (:274) already gives `‖e x‖ = ‖x‖` for the algebraMap
`PadicScalarField concretePlace → NormalizedCompletion concretePlace`, so S1 at that map does not need G2.

**G3 - no principal-image equivalence.** No `≃`/`≃+` between `principalUnitLogImage` carriers. Existing:
additive embeddings `sourceQlEmbeddingLogShellMap` (`SourceQlEmbeddingConsumer.lean:158`, no olean) and
`sourceQlLogShellMap` (`SourceQlCarrierMap.lean:123`, no olean); `sourceTheaterLogShellMap`
(`SourceLogLinkCompatibility.lean:334`, green) into the *scaled* `integralLogShell` (different carrier);
`concretePlace_principalUnitsEquiv` (target file :347, green) on the Q5 `Completion` pair only. No
composition exists.

**G4 - no principal-unit carrier equivalence at the actual pair.** Only the identity-pair
`principalUnitMap` and the Q5 `concretePlace_principalUnitsEquiv` exist.

**G5 - no named `e_L` / scaling square at the actual pair.** `unscaledLogImageEquiv` is an `Equiv`
(no additivity); `unitLogLatticeAddEquiv` is `≃+` but has no generator-formula theorem and is stated at the
identity pair; the cross-field generator formula for `integralLogShellAddEquivOfRingEquiv` is also absent.

**G6 - scaled/unscaled is not this consumer.** The card is against `logKummerData` (unscaled:
`principalUnitLogShell`, `principalUnitLogShellFrobenius = p * x`, `Example36LogKummerMap.lean:231-238`).
`treeSourceFrobeniusLogKummerCard` is a different package (`scaledPrincipalUnitLog =
(logShellScale p)^-1 * unitLog`, `integralLogShell`, `integralLogShellPScaling`: :279-292, :317-330).
No bridge theorem exists and none is needed here. Do not merge F5-c into L0.4.

**G7 - general `l`.** No continuous ring map `ℚ_[l] →+* concreteLogShellField` for `l.value ≠ 5`;
`∀ l, Nonempty card` is not obtainable at the fixed Gaussian target. The general form needs a variable
target place (the unbuilt SourceQl* design), where the embedding is not onto, so the card's equivalences
would have to be stated against that place's image.

**G8 - card-only evidence is insufficient.** The card's types are unconstrained (section 1). L1-F5 must
record S1-S4 with the actual `ℚ_[l]` objects, not merely a `Nonempty`.

**G9 - prime-term mismatch.** `sourceLocalField l = ℚ_[l.value]` (target file :99) vs the actual
transport's domain `PadicScalarField concretePlace = ℚ_[(completionRationalPrime concretePlace).val]`
(`FinitePlacePadicScalarStructure.lean:31-32`). At `l.value = 5` both are `ℚ_[5]` but with different index
terms; the transport is `concretePlace_rationalPrime_eq_five` (:218) plus rewriting. Mechanical, but it must
appear in the statement (use `fivePrimeLabel` or a hypothesis `h5 : l.value = 5`).

## 6. Child nodes and order (fractal, per `coord/FRACTAL-STAGES.md`)

| child | stage | deliverable | blocker |
|---|---|---|---|
| `l0.4-unit` | 2 candidate | S1 principal-unit square at the actual map (section 8) | none |
| `l0.4-equiv` | 2 candidate | finrank 1, `Isometry`, surjectivity, `RingEquiv` (G1, G9) | G1 instance alignment |
| `l0.4-image` | 2 candidate | principal-image map, generator formula, inverse (G3, G5) | `l0.4-equiv` |
| `l0.4-card` | 2/3 | inhabit `SourceLogKummerIdentificationCard fivePrimeLabel` | l0.4-unit, -equiv, -image |
| `l0.4-general` | 1 open | variable-place form; target shell is that place's image | G7; needs a real consumer for general `l` |

Parent `L0.4` stays open. `l0.4-card` at `fivePrimeLabel` is not `target_accepted`: the card is an
interface, and G8 applies.

## 7. Stage status and file evidence

- `statement_compiles`: **not run**. No Lean file was created or compiled in this session; section 8 is a
  proposed statement, not a compiled one.
- `proof_body_checked`: **not run this session**. The donor files have `.olean`s newer than their sources
  and contain no `sorry`/`admit`/`axiom` (grep); this is historical build evidence, not a fresh check.
- `kernel_closed`: **no**.
- `target_accepted`: **no**.
- Production files changed: **none**. This record only created `tmp/sheaf/l0.4/STAGE1.md`; `tmp/` is
  gitignored (`.gitignore:2`), so it is not visible in `git status`. At HEAD `9399e9f...` the working tree is
  widely untracked (e.g. `LeanFormal/IUT/Foundations/AlgebraicGeometry/` is one untracked directory, and the
  four `Example36` log modules cited here are `??`); that is pre-existing repository state, not a change made
  by this record.

File evidence (SHA256 computed this session; `olean` column = `.olean` exists and is not older than source):

| file | lines | SHA256 | olean |
|---|---|---|---|
| Example36SourceLogKummerIdentification.lean | 373 | `C50F19A6E88C1068AC25383A23BF30625DEBC8F394E0EC3F9C31F174C3E236A6` | Y |
| Example36LogKummerMap.lean | 452 | `F3A4FA46EACFB54035EE46E6DA36A7D03153347A653CFFC6C15884E9B48F030B` | Y |
| Example36LogShellFrobeniusAction.lean | 352 | `0FEC5413CCB66B01E7F0C8C01052BCB3E13F0DC0A4D47B6437F5258000029C00` | Y |
| Example36LogShellLattice.lean | 551 | `C5096EEB7090223D5C274F46FAB016A1B28EF49649374C2EA4544F544118AD8B` | Y |
| Example36LogDomainActual.lean | 469 | `4006DD585C967831A4ADFDBE0894AAE0EBC79E4162117292081CABED48F4C08D` | Y |
| IntegralUnitLogarithm.lean | 217 | `BC15C180BC7FAE00D56257B0C58882153A398210FBC9CD9B33424F81FCDF7410` | Y |
| IntegralUnitLogarithmFunctoriality.lean | 95 | `74E7C6DF3CE6FCA1C71CBF8812AFB5F0FFAE8101C9D40436CEAD422581B3FA71` | Y |
| UnscaledUnitLogLattice.lean | 127 | `C1894E58B7E9B3D438379F0F42F53EBDEA74A0CA335BE790B9F1AAD9206F2EC1` | Y |
| IntegralLogShellIndexArithmetic.lean | 284 | `2B02F5C94FF877AABCEF7415C88CA0BDDA81F3FD385C22A3230334059681D35E` | Y |
| LogUnscaledImageConsumer.lean | 154 | `C16F56A94FBEA8DFD8F8385E77014BCAC828400D899EC1A4BEB8EB8B5FECB1C1` | Y |
| LogCarrierNaturality.lean | 166 | `52FB27EA3C627080EB2D170E43AE77A22D19CF59436944B85666FDBD1D4DAA0B` | Y |
| LogKummerK1K2.lean | 101 | `A713070447502573F0A3B37D4C891A5EBDB55D94CCFF5D50F04304037C0D4C48` | Y |
| Example36SourceLogLinkCompatibility.lean | 370 | `2FB63C6FB4F7867B307376356A9C8EC9518D3B0D580C872E10B34D823D95445B` | Y |
| FinitePlaceCommonPrimeCompletion.lean | 79 | `72DF2A633B4AD089284F2017C522B69C0DD479225B0CD911B3EEE6841B6014F7` | Y |
| FinitePlaceNormalizedCompletion.lean | 82 | `B506BCD3446A07C9E9849A04B54C123C0A0103796AC070A6B5534772410398D2` | Y |
| FinitePlaceNormalizedIntegers.lean | 116 | `B71E71D5C170BBB9C21E0A2166DDB7C887745F725156DEB453E6302E28A4C2AF` | Y |
| FinitePlacePadicScalarStructure.lean | 89 | `2EFE6E972E6BE67556D06846ECAC4188B70F14F8897D1F2FC8E594B5E314EFEF` | Y |
| FinitePlaceRelativePadicDegrees.lean | 115 | `C20600BF8407B20393E40D023A4CA9620B70AF008A8ED20F99B920FB20C2A3B0` | Y |
| RationalCommonPrimeFinrank.lean | 125 | `E2361FC29AC473FA41BC30BC30BDAE889B13983C04B6791CB0394B98B755FE14` | Y |
| Example36GaussianSplitPlaceArithmetic.lean | 1395 | `3FABEE4B5758035B0BE37BC984A2CA8B1E66F380AB053FD5CDB74187D32D7F2E` | Y |
| PrimeLabels.lean | 50 | `B9DC606EE1F6529BFFB9B916DDBD28038BE5E6B3A99A1DA890E258F50262DC9A` | Y |
| Example36SourceEtaleThetaTheory.lean | 383 | `E4E85FB7337B5B802501AF4A6BC4499BBB0B7FB4B81BDEB13C2645812A3E67F4` | Y |
| SourceQlEmbeddingConsumer.lean | 241 | `BEE32551A7908F26DB18CD8AAAE9DCC1F64B697DCC0F55ADC65D0D5075EFB294` | **N** |
| SourceQlCarrierMap.lean | 163 | `36FE5EF95276EB77D44E304BAF5FFDC43B4A46E1CAC553FF8431ACA73C4D3517` | **N** |
| SourceQlEmbeddingShellImage.lean | 249 | `1ABF69F51B73A60122A47F76387DF53A43B516616E03053F1C466C254DE88425` | **N** |
| SourceQlUnitTransport.lean | 104 | `CE2F15A0BDE7CD065153CEF4CC8D407CB9377716C0D78B7528696E4DA6C23205` | **N** |

Tracked/untracked status is not provenance evidence at this HEAD, because most of the cited tree is
untracked (see the bullet above). The `.olean` timestamps and the SHA256s are the version anchors.

This record: `tmp/sheaf/l0.4/STAGE1.md`, 395 lines; SHA256 is reported in the handoff message.

## 8. Smallest next statement

Statement (Lean form; the production names are exact):

```lean
-- proposed trial file: tmp/sheaf/l0.4/L04PrincipalUnitSquare.lean, namespace isolated,
-- not imported by Project.lean; statement only
theorem sourceTheater_principalUnitLog_square
    (u : principalUnits (K := PadicScalarField concretePlace)) :
    sourceTheaterScalarMap (K := GaussianField)
        (principalUnitLog (K := PadicScalarField concretePlace) u) =
      principalUnitLog (K := concreteLogShellField)
        ⟨integralUnitMapOfMapsIntegers (sourceTheaterScalarMap (K := GaussianField))
            (fun _ hx => sourceTheaterScalarMap_mem_integers hx)
            (u : (Integers (PadicScalarField concretePlace))ˣ),
          sourceTheaterScalarMap_mem_principalUnits
            (u : (Integers (PadicScalarField concretePlace))ˣ) u.property⟩
```

Why this one:

- It is the S1 content of the card's `logKummer_intertwines` at the *actual* map of the actual consumer,
  restricted to principal units (the card's carriers are principal units, not all units).
- It is provable from green donors only: rewrite both `principalUnitLog` terms to `unitLog` with
  `unitLog_eq_log1p` (`IntegralUnitLogarithm.lean:125`), then apply `sourceTheater_unitLog_square`
  (`Example36SourceLogLinkCompatibility.lean:300`). Expected 4-6 lines; no new analysis, no new instances
  (the `Subtype` proof component is irrelevant).
- It removes the first real gap: after it, S4's forward shell map is `Subtype.ext` of this square, and S3 is
  `map_mul` + `map_natCast` at the same `e`.

What it does NOT do: it is not an equivalence, so it gives neither `carrierEquiv` nor `shellEquiv`.
The immediate follow-up statement is G1's missing input:

```lean
theorem concretePlace_finrank_padicScalarField_eq_one :
    Module.finrank (PadicScalarField concretePlace) (NormalizedCompletion concretePlace) = 1
```

Route: instantiate `finrank_commonPrimeCompletion_tower (k := ℚ) (p := 5)` at
`place := <concretePlace, concretePlace_rationalPrime_eq_five>`, evaluate the lower factor by
`finrank_commonPrimeCompletion_rat_of_prime 5` and the relative factor by
`concreteGaussianFivePlace_relativeCompletionDegree_eq_one`; conclude. Then
`sourceTheaterScalarMap_surjective`, `sourceTheaterScalarEquiv : PadicScalarField concretePlace ≃+*
concreteLogShellField`, and S1-S4 at that `e`.

Validation order: (1) compile the S1 statement (`statement_compiles` only); (2) build the finrank statement;
(3) only then attempt the card. `target_accepted` requires a comparator on a locked statement and is not
available now.

