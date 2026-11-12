# D6 M1 concrete-witness plan (2026-11-06)

Status: M-A closed the identity case; general D6 cover case is NOT closed. This note lists the minimal changes needed to expose X.finiteEtale.baseChange as S2512/S2514 concrete witness, and why the current API cannot do it.

## 1. Current D6 cover data

File: Iut/Foundations/Orbicurve.lean

| Structure | Fields | Relevance |
|---|---|---|
| EtaleStackRepresentableMorphismProperty | baseChange: for all testScheme point, presentation; hasProperty: for all ..., property (baseChange ...).projection.left | pointwise only; no global representability of map |
| EtaleStackFiniteEtaleMorphism | abbreviation of the above with IsFinite and Etale | D6 cover map type |
| OrbicurveFiniteEtaleCover X | source: EtaleStackOverField; map: source.Hom X.stack; finiteEtale: EtaleStackFiniteEtaleMorphism map | D6 cover object |
| OrbicurveFiniteEtaleCoverMap A B | map: A.source.Hom B.source; commutes: Iso (map ; B.map) A.map | D6 cover morphism |

Missing for M1:

    cancelRight : RightCancellation map
    cancelWitness : M1RightCancellationWitness map

These are global right-cancellation/faithfulness data, not pointwise base-change data.

## 2. Why S2512/S2514 do not fill it

| Source | File | Why not applicable |
|---|---|---|
| S2512Witness | S2512StackOpenImmersionUB.lean | Requires both base legs to be scheme morphisms (S1742HomOfStrongTrans); D6 m and ptY are stack morphisms. Also fixed field UB. |
| S2514IdWitness | S2514IdentityFiniteEtaleActual.lean | Only identity-point square; fixed field S2480QiActual.F. |
| S2622IsoWitness | S2622M1ConcreteWitnessActual.lean | Gives 2-iso invariance of a TwoPullbackWitness in the two base legs, not creation of the witness. |

Additional type-level mismatch: S2512 is over UB, S2514 over S2480QiActual.F, while M1RightCancellationWitness (S2620) is fixed at S1726K.

## 3. Minimal-change options

### Option A (recommended): paper-level wrapper, no foundation change

New file S2625D6CoverCancellationData.lean:

    structure D6CoverWithCancellation
        {F} [Field F] {X : HyperbolicOrbicurve F}
        (cover : OrbicurveFiniteEtaleCover X) where
      cancelRight : RightCancellation cover.map
      cancelWitness : M1RightCancellationWitness cover.map

Consumers:

    S2621.fieldWithHypothesesOfCancellation
    S2623.d6FiniteEtale

Risk: low (no change to Iut foundation; new assumptions explicit).

### Option B: add fields to EtaleStackFiniteEtaleMorphism

Change Iut/Foundations/Orbicurve.lean EtaleStackRepresentableMorphismProperty or introduce a new property structure carrying cancelRight and cancelWitness.

Risk: high. It creates an import cycle (Iut foundation cannot import paper S2619/S2620), and changes every consumer of finite-etale morphisms (S2092, D6, open-immersion variants).

### Option C: global representability/faithfulness field

Add to OrbicurveFiniteEtaleCover:

    isFaithful : RightCancellation cover.map

or a stronger RepresentableByScheme field. Still needs an import-cycle-safe interface; recommend paper wrapper.

## 4. Field list and consumers

| New field | Exact type | Consumer |
|---|---|---|
| cancelRight | RightCancellation map (S2619) | cancellationOf; fieldWithHypothesesOfCancellation (S2621) |
| cancelWitness | M1RightCancellationWitness map (S2620) | m1CancellationWitnessOf; fieldWithHypothesesOfCancellation (S2621) |
| D6CoverWithCancellation | cover + the two fields | S2623 downstream morphismOfFiniteEtaleStacks / d6FiniteEtale |

## 5. Minimal change order

    1. Add S2625D6CoverCancellationData wrapper (paper layer).
    2. Add an adapter from the wrapper to RightCancellation/M1RightCancellationWitness family (identity fields).
    3. Feed S2621.fieldWithHypothesesOfCancellation.
    4. Feed S2623.d6FiniteEtale; S2086BaseChangePullback remains separate.

## 6. Identity-case actual (from M-A)

S2622M1ConcreteWitnessActual.lean (EXIT=0, SHA 9158CCF701816062B3E42FC09AA169611517829654725859F5076FB28B9B9367) provides:

    m1RightCancellationWitnessId : (Y) -> M1RightCancellationWitness (StrongTrans.id Y.fiber)
    rightCancellationId : (Y) -> RightCancellation (StrongTrans.id Y.fiber)
    presentationOfId : consumer for y = id

General y = S1742StrongTransOfHom s is NOT obtained; it needs a genuine right-cancellation theorem.

## 7. Honest boundary

- No sorry, admit, custom axiom, or fake witness.
- S2512/S2514 cannot be fed directly into S1726K M1 types (field mismatch).
- General D6 cover case requires the two global fields above; pointwise finiteEtale.baseChange is insufficient.
