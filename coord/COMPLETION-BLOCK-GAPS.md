# COMPLETION-BLOCK-GAPS — CompletionRootBlock → C3 donors (A934)

Status: **STOP / GAP** (no `CompletionRootBlock` inhabitant constructed).
Route/stage: C3 L-source pilot, A934; date 2026-11-12; lane hull.

## 1. What was checked

- `CompletionRootBlock` (root tree `tmp/sheaf/xif/paper/S1391C3LSourcePilotActual.lean:146`):
  fields `roots roots' : NatRootSystem C.qUnit`,
  `kummerClass rootChange : CyclotomicTower (CommonPrimeCompletion ...)`,
  `rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots'`.
- `NatRootSystem` (`LeanFormal/IUT/IUTII/Kummer/NatRootSystem.lean:17`):
  fields `root : Nat → Mˣ`, `root_one : root 1 = value`,
  `compat : root (n*k)^k = root n`.
- Generic constructor `AlgebraicClosureRootSystem.rootSystemOfAlgClosed`
  (`NatRootSystem.lean:75`) exists **only for `[Field K] [IsAlgClosed K]`**.
- `CyclotomicTower` (`LeanFormal/IUT/IUTII/Kummer/KummerClass.lean:18`) and
  `KummerClass.rootSystemDiff` (`:106`) are constructors; trivial tower
  `CyclotomicTower.one` is available.
- S1391 `completionRootBlock_nonempty_iff` (`:221`):
  `Nonempty (CompletionRootBlock C) ↔ Nonempty (NatRootSystem C.qUnit)`;
  the block's three derived fields are filled from the first root system.
- S1391 `actualCompletionRootBlock_nonempty_iff` (`:480`):
  the actual block is nonempty iff `completionFirstFieldObstruction`,
  defined (`:469`) as `Nonempty (NatRootSystem (concreteQUnit ...))`.

## 2. Why construction fails

1. `C.qUnit : (CommonPrimeCompletion (K := Fmod) place)ˣ` is a unit of a
   p-adic completion; the completion is NOT algebraically closed.
2. `NatRootSystem` requires an **all-n** compatible root family in that
   completion's units.  The only green constructor is for algebraically
   closed fields (`rootSystemOfAlgClosed`); it cannot be instantiated at
   `CommonPrimeCompletion`.
3. The L replacement does have roots, but over a different carrier:
   `SourcePilotRegionDataL.roots : NatRootSystem (concreteQUnitAlgebraicClosure ...)`
   (`S1391:259`), built from `concreteRootsAlgebraicClosure` over
   `ConcreteQAlgebraicClosure`.  This does not produce a
   `NatRootSystem concreteQUnit` on the completion.
4. S1408 `sourcePilotRegionDonorsOfLBlock` (`S1408C3LSourcePilotConsumerActual.lean:116`)
   takes the old block `B : CompletionRootBlock` as an explicit input and
   states the exact mismatch (`sourcePilotOldCompletionBlock_nonempty_iff`,
   `actualSourcePilotOldCompletionBlock_nonempty_iff`).  No such B exists.

## 3. Consequences

- No green `CompletionRootBlock` instance; no C3 donor via
  `sourcePilotRegionDonorsOfLBlock`; C3 remains blocked at the completion
  first field.
- L-side data `actualSourcePilotRegionDataL` is green but cannot be turned
  into the old completion-valued `SourcePilotRegionData` without B.
- The exact remaining obligations:
  (a) construct `NatRootSystem (concreteQUnit ...)` in the completion units
      (or prove `completionFirstFieldObstruction` false),
  (b) then B's `kummerClass/rootChange` towers and `rootChange_eq` follow
      from `completionRootBlock_nonempty_iff`'s rfl construction,
  (c) feed B to S1408 donor consumer.

## 4. Next step / stop

- STOP for A934: no completion root system constructed.
- If pursued: decide whether the old completion carrier is mathematically
  the right one (likely the completion q unit has no all-n root system unless
  it is a root of unity with order prime to p); otherwise the L carrier
  (`SourcePilotRegionDataL`) is the correct replacement and the old
  completion-valued consumer must be retired, not filled.

## 5. A935 negative criterion (Lean, green)

File: `tmp/sheaf/xif/paper/Mzk1CompletionNoRootActual.lean`
(EXIT=0, olean fresh, trio; queued).

- `no_natRootSystem_of_no_sqrt {M} [CommMonoid M] {u : Mˣ}`:
  `(¬ ∃ w : Mˣ, w^2 = u) → ¬ Nonempty (NatRootSystem u)` — PROVED.
  Proof: `NatRootSystem.compat 1 2` gives `r.root 2 ^ 2 = r.root 1 = u`,
  contradicting no square root.
- `completionFirstFieldObstruction_false_of_no_sqrt`:
  for concrete `I, place`, if `concreteQUnit` has no square root in the
  completion units, then `¬ completionFirstFieldObstruction` — PROVED.

### Exact remaining dependency

To make the negative theorem unconditional we need:
1. `concreteQUnit` is a unit of a p-adic completion (finite extension of Q_p);
2. a Mathlib/Mathlib-adjacent fact: in a finite extension of Q_p, the unit group
   has no divisible element except 1 (equivalently: an element with n-th roots
   for all n is 1); or directly `¬ ∃ w, w^2 = concreteQUnit` via residue/valuation.
   The repo/Mathlib does not currently provide this p-adic divisibility lemma
   in the form needed; `padicValRat`/`Valued` API exists but the 'all n roots'
   argument (p-adic logarithm / pro-p decomposition) is not formalized.
3. Alternatively, prove `concreteQUnit ≠ 1` and use the finite torsion of
   p-adic units; finite roots of unity in p-adic fields also needs Mathlib work.

Thus: negative theorem is **conditionally green**; unconditional obstruction
negation is NOT formalized.  The gap is exactly the p-adic unit divisibility
lemma, not the completion block construction.

## 6. Model status of SourcePilotRegionData (A935)

- `SourcePilotRegionData` (old completion-valued schema) is **model-unconstructible**
  from current repo data: its first root field needs `NatRootSystem` on
  `concreteQUnit`, which the completion does not supply.
- The L carrier `SourcePilotRegionDataL` is the intended replacement: it has
  roots over `ConcreteQAlgebraicClosure` and actual Kummer/rootChange towers
  (`S1391:329 actualSourcePilotRegionDataL`).
- Consumers that require the old `SourcePilotRegionData` remain conditional on
  the completion block (S1408) and should be migrated to the L carrier or
  treated as a model/legacy interface, not as a constructible C3 input.

## 7. A938 unconditional attempt — not green

Target: `¬ Nonempty (NatRootSystem (candidateUnits place q))` unconditionally via
`q.exponent > 0` and the completion valuation exponent.

Status: **NOT formalized**.  Blockers found:
1. `CommonPrimeCompletion place` is a `def`/abbrev of `NormalizedCompletion place.val`
   (`FinitePlaceCommonPrimeCompletion.lean:20`; `NormalizedCompletion` is a `def`
   of `Completion place`).  The `Valued (CommonPrimeCompletion place) (WithZero
   (Multiplicative ℤ))` instance is not synthesized by typeclass search in this
   context, so `Valued.v` cannot be applied at that type without an explicit
   instance bridge (`inferInstanceAs`/unfolding).  This is a typeclass/reducibility
   gap, not a mathematical one.
2. Needed power lemma: for `u : Kˣ`, `v : K → WithZero (Multiplicative ℤ)`,
   a root `w` with `w^n = u` gives additive exponents `n * valExp w = valExp u`.
   `Valued.v` is multiplicative and `map_pow`, `WithZero`/`Multiplicative.toAdd`
   lemmas exist, but the compound lemma is not present in the repo and needs a
   short proof.
3. Needed instance/API: `FinitePlaceQCandidate.exponent` relation
   `unitValExp (candidateUnits place q) = q.exponent` (definitional but requires
   the instance bridge above).

With these, the argument is: root for n = exponent+1 gives
`(e+1) * k = e`, impossible for `e > 0`; hence no root system.

Current green negative result remains the **conditional** theorem
`no_natRootSystem_of_no_sqrt` /
`completionFirstFieldObstruction_false_of_no_sqrt` in
`Mzk1CompletionNoRootActual.lean`.

Lemma checklist for A938:
- `Valued` instance bridge from `Completion place` to `CommonPrimeCompletion place`;
- `valExp` of a nonzero element and `unitValExp`;
- `unitValExp_mul`, `unitValExp_pow` (additive exponents);
- `unitValExp_candidateUnits = q.exponent`;
- integer arithmetic contradiction `(e+1)*k = e` with `e > 0`.

## 8. A939/A940 unconditional negative theorem — GREEN

File: `tmp/sheaf/xif/paper/Mzk1CompletionUnconditionalActual.lean`
EXIT=0; fresh olean; axioms all `[propext, Classical.choice, Quot.sound]`.

Instance bridge used (explicit, definitional):
`commonPrimeCompletionValued : Valued (CommonPrimeCompletion place)
  (WithZero (Multiplicative ℤ)) := inferInstanceAs (Valued (Completion place.val) ...)`.

Proved:
- `valExpVal` on the value group, `unitValExp` on units;
- `valExpVal_mul`, `unitValExp_mul`, `unitValExp_pow`;
- `unitValExp_candidateUnits = q.exponent`;
- `no_natRootSystem_of_valExp_pos`: `0 < unitValExp u ⇒ ¬ Nonempty (NatRootSystem u)`
  (proof: root n ^ n = u, exponent equation `(n) * k = e`, choose n=e+1,
  contradiction);
- `completionFirstFieldObstruction_empty` (unconditional for actual place/q);
- `actualCompletionRootBlock_empty`: `¬ Nonempty (CompletionRootBlock (actual core))`;
- `oldSourcePilotWithActualCore_empty`: no old record with the actual core.

Command: `lake env lean -R . -o ...olean ...lean` (EXIT=0).
File SHA256: `9ABB87A3D663ACC37FC8581C51196A5DEEBBBB62AA38DAF52910C5CD58146A4D`.
Olean SHA256: `440DCA48EE09F61FD62897951EA782EA91B37D8F70E60B73E253D0409DC5A887`.
