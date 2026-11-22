# Exact Ind1 beta source gap (2026-11-14, stepxi)

Status: all surrounding interfaces and probes are GREEN with only `[propext, Classical.choice, Quot.sound]`. The remaining source input is exactly an actual Ind1/Ind2 unit action. No fake `≃*`/`Nonempty` is included.

## Green interfaces

- `Mzk1Ind1ActualSourceUnitLayerActual` (DONE 04:05:14Z):
  - `ActualSourceUnitLayer K = (Integers K)ˣ / torsion` (actual, finite-generated);
  - `actualSourceUnitLayer_self : SourceUnitQuotientIdentification (ActualSourceUnitLayer K) K` (identity actual inhabitant);
  - `ActualInd1UnitAction K` with fields:
    `algAction : (AlgebraicClosure K)ˣ ≃* (AlgebraicClosure K)ˣ`,
    `beta : ActualSourceUnitLayer K ≃* ActualSourceUnitLayer K`,
    `compatible : ∀ u, ∃ v, beta (mk u) = mk v ∧ integersUnitsToAlgClosure v = algAction (integersUnitsToAlgClosure u)`;
  - `ActualInd1UnitActionRequired K := Nonempty (ActualInd1UnitAction K)`.
- `Mzk1Ind1IntegrationActionActual` (DONE 04:09:20Z):
  - `IntegralUnitStableAlgebraicAction K` with `algAction`, `mapsIntegers`, `mapsIntegers_symm`;
  - `IntegralUnitStableAlgebraicActionRequired K := Nonempty ...`.
- `Mzk1Ind1SourceUnitBridgeActual` (DONE 01:30:31Z):
  - `SourceUnitQuotientIdentification`, `sourceUnitLogRangeEquiv`.
- `Mzk1Ind1IntegralUnitMapActual`, `Mzk1Ind1LocalMonActual` (both DONE, probes three axioms).

## The single remaining source node

Construct an actual inhabitant of either

```lean
IntegralUnitStableAlgebraicAction K
-- or
ActualInd1UnitAction K
```

from the actual Ind1/Ind2 procession action. Concretely one must prove:
1. the actual algebraic-closure unit action `algAction` comes from the source procession action;
2. it preserves the integral-unit image in both directions;
3. the induced quotient map `beta` exists and satisfies `compatible`.

## Why existing donors do not close it

- `FPrimeStripEquiv.isoMon` acts on `F.Mon v = (AlgebraicClosure ℚ_[v.1])ˣ`, not on `(Integers K)ˣ`.
- `IntegralUnitLogarithm*` gives unit log maps, not an algebra-closure unit action on the integral-unit quotient.
- Kummer finite layer gives only an injection (`kummerMap`, kernel = n-th powers); H¹ surjectivity/compatibility missing.
- Inertia/local reciprocity donor is absent; no unconditional `I_F -> G_F^ab` image map was found.
- The natural map `(Integers K)ˣ -> (AlgebraicClosure K)ˣ` is injective but not surjective, and the torsion quotients differ; there is no canonical `≃*`.

## Non-fake rule

Do NOT fill `Required` with `Nonempty` via an arbitrary `MulEquiv.refl`/toy equivalence. The identity action is a legitimate special case, but it is not evidence for the general source action. The source node stays open until the actual procession action is constructed/identified.

## Candidate: local Galois action `localGaloisUnitsAction` (2026-11-14)

The concrete algebraic-closure action is available:

```lean
def localGaloisUnitsAction (p) :
    LocalAbsoluteGalois p →* MulAut (AlgebraicClosure ℚ_[p])ˣ :=
  fun σ => Units.mapEquiv σ.toRingEquiv.toMulEquiv
```

To turn this into `IntegralUnitStableAlgebraicAction ℚ_[p]` one must prove the missing stability lemma:

```text
localGaloisUnitsAction_preserves_integers :
  forall σ and u : (Integers ℚ_[p])ˣ,
    exists v : (Integers ℚ_[p])ˣ,
      integersUnitsToAlgClosure v =
        localGaloisUnitsAction p σ (integersUnitsToAlgClosure u)
```

and the same for σ.symm. Equivalently, one must prove that every ℚ_[p]-algebra automorphism of
the algebraic closure is isometric / preserves the integral closure of ℤ_[p].

No such theorem was found in the tree. Mathlib has normed-field facts but no local-field
Galois-isometry lemma for the algebraic closure. This stability lemma is therefore the exact
remaining source/analysis node. It cannot be replaced by an arbitrary MulEquiv, and no
`Nonempty`/`refl` filler is used.

## Status update: beta closed for the K-automorphism class (2026-11-14)

GREEN files and probes (all without sorryAx, three axioms):
- `Mzk1Ind1GaloisIntegralActionActual` (DONE 04:43:30Z): base `ℚ_[p]`;
  `localGaloisUnitsAction_fixes_integralUnits`,
  `localGaloisStableAlgebraicAction σ : IntegralUnitStableAlgebraicAction ℚ_[p]`,
  `localGaloisActualInd1UnitAction σ : ActualInd1UnitAction ℚ_[p]`.
- `Mzk1Ind1GaloisIntegralGeneralActual` (DONE 04:52:18Z): arbitrary local field `K`;
  `localUnitsAction σ` for `σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`,
  `localUnitsAction_fixes_integralUnits`,
  `localStableAlgebraicAction σ : IntegralUnitStableAlgebraicAction K`,
  `localActualInd1UnitAction σ : ActualInd1UnitAction K`.

### Exact mathematical content

`σ` fixes `K` pointwise; embedded integral units are in the image of `K`; hence
`σ` fixes them. The quotient action on `(Integers K)ˣ/tors` is therefore the identity,
and `beta = MulEquiv.refl` is the actual action, not a fake equivalence.

### Exact scope / what is NOT closed

- Closed: beta source for the class of actual `K`-algebra automorphisms of the algebraic closure.
- Not closed: arbitrary Ind1/Ind2 procession arrows that are not induced by a `K`-automorphism of the algebraic closure. Those still require actual source action data; no claim is made that every abstract arrow factors through this class.
- No unconditional fixed-point/descent statement for arbitrary source W/unit layer is claimed.
- No `Nonempty`/`refl` filler; the identity action is a theorem, not an axiom.

### Remaining source node

For non-automorphism (or non-field) Ind1/Ind2 arrows: construct the actual action and its compatibility with the integral-unit quotient. The existing green interfaces (`ActualInd1UnitAction`, `IntegralUnitStableAlgebraicAction`, `SourceUnitQuotientIdentification`, `sourceUnitLogRangeEquiv`) are the consumer edges; no fake inhabitant is supplied.

## IMPORTANT audit correction: K-automorphism inhabitants are NOT source-arrow closure (2026-11-14)

The inhabitants `localActualInd1UnitAction σ` / `localStableAlgebraicAction σ` are locally constructed from a `K`-algebra automorphism of the algebraic closure. They are NOT evidence that the actual Ind1/Ind2 procession source arrow exists:

- `σ = 1` is allowed, so `ActualInd1UnitActionRequired K` / `IntegralUnitStableAlgebraicActionRequired K` are trivially nonempty once these local constructors exist;
- neither `IntegralUnitStableAlgebraicAction` nor `ActualInd1UnitAction` carries a field relating `algAction`/`beta` to the actual source procession arrow (the only substantive field is `compatible`, which ties `beta` to `algAction`, not to the source action);
- therefore these structures do NOT close the actual Ind1/Ind2 procession source arrow.

Correct status wording:
> The beta source is constructed only for the **K-automorphism class** (a local nonempty construction). The actual Ind1/Ind2 procession source arrow remains an open source node. Do not claim global beta-source closure.

To actually close the source arrow one must add a substantive provenance field, e.g. equality of `algAction`/`beta` with the actual action induced by a specified source procession arrow (or a source action object), not a bare `Prop`.

## Source-arrow donor check (2026-11-14)

Searched the tree for actual Ind1/Ind2 procession action donors. The relevant found items are:

- `LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceSHETransportConjugation.lean:271-299`
  - `sourceAction := TimesMuKummer.actionConj (Units.mapEquiv (sigma.isoMon v)) ...`.
  - It acts on `TimesMuQuotient (F.Mon v)`, where `F.Mon v = (AlgebraicClosure ℚ_[p])ˣ`;
  - it is NOT an action on `(Integers K)ˣ/tors`.
- `LeanFormal/IUT/IUTIII/Theorem311/SourceMultiradialTwoActionEquivalence.lean:156-223`
  - `processionAction : G →* Equiv.Perm Output` and `ind1Action`;
  - acts on an abstract `Output`/presentation, not on the local integral-unit layer.
- `LeanFormal/IUT/IUTII/Kummer/SourceLogShellActionCompatibility.lean:90-94`
  - `sourceAction : (i : ι) → G →* ((D i).K ≃ₗ[ℚ] (D i).K)` is a STRUCTURE FIELD, not an actual inhabitant;
  - its log-shell preservation hypothesis is also a field, not proved globally.
- `LeanFormal/IUT/IUTII/Frobenioid/LocalPrimeStrip.lean:41`
  - `localFPrimeStrip.Mon v = (AlgebraicClosure ℚ_[v.1])ˣ`; no integral-unit quotient action.

Conclusion: no existing unconditional donor gives the actual Ind1/Ind2 action on `(Integers K)ˣ/tors`.
The found actions live on the algebraic-closure unit quotient or on abstract `Output`; they do not supply
the provenance required by `ActualInd1UnitAction`. The source arrow node remains open. No fake inhabitant is added.

### Additional donor check: SourceActionComponent family

- `LeanFormal/IUT/Foundations/SourceAnabelioidBridge.lean:56-63` uses `Iut.SourceActionComponent G S` / fibers;
- `Iut/Foundations/SourceTemperoidComponentFamily.lean` and `SourceTemperoidRestrictionComponentFamily.lean` contain source-action component families;
- these are anabelioid/temperoid action components, not an action on the local integral-unit quotient `(Integers K)ˣ/tors`;
- no theorem maps a source-action component to `ActualInd1UnitAction` or `IntegralUnitStableAlgebraicAction`.

Therefore no additional source-arrow donor was found; the provenance gap remains exact and open.

### TimesMu inspection (2026-11-14)

- `TimesMuQuotient.action` / `unitsAction` (Kummer/TimesMuQuotient.lean:56,99) act on `TimesMuQuotient U` where `U` is an abstract CommGroup; for `localFPrimeStrip`, `U = (AlgebraicClosure ℚ_[p])ˣ`.
- `TimesMuKummer.actionConj` (SourceSHETransportConjugation.lean:113) conjugates such an action by a `MulEquiv`; it is generic, not an integral-unit action.
- `SourceSHETransportConjugation` `sourceAction` fields are structure fields; no unconditional inhabitant on `(Integers K)ˣ/tors`.

Thus TimesMu gives an actual action on the algebraic-closure unit quotient, but NOT the `beta`/`algAction` provenance needed by `ActualInd1UnitAction`. No fake conversion is added.
