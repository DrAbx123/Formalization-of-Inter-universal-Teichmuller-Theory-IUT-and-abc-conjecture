# S2828 — Fin-2/Q_p witness donor audit

Date: 2026-11-07
Result: **exact schema blocker: no actual donor**, not just missing product formula.
No fake root system, no fake witness.

## 1. The tensor fields are writable

Given an `OriginalInput`, `SourcePilotRegionData` allows:

```lean
tensorIndex := Fin 2
tensorPlaceIndex := fun _ => Unit
tensorPlaces := constant actual finite place
tensorTuple := constant ()
tensorUnit := 1 (or actual unit)
tensorLanding := constant 1
```

So `Fin 2` itself is not the blocker.

## 2. Upstream blocker: q and NatRootSystem

Before the tensor fields, `SourcePilotRegionData` requires:

```lean
q : FinitePlaceQCandidate place.val
roots : NatRootSystem qUnit
roots' : NatRootSystem qUnit
```

with

```lean
qUnit : (CommonPrimeCompletion ... place)ˣ
qUnit_eq : qUnit = candidateUnits ... q
```

A concrete `Fin 2` donor therefore needs:

1. an actual finite place `place` and a nontrivial completion q;
2. an actual `NatRootSystem qUnit` in the completion monoid;
3. a second one `roots'`.

### Existing actual evidence

`tmp/sheaf/xif/paper/ConcreteC3DonorAssemblyActual.lean` records exactly:

```lean
def rootsCompletionObstruction : Prop :=
  Nonempty (NatRootSystem (concreteQUnit (I := I) place))

def rootsPrimeCompletionObstruction : Prop :=
  Nonempty (NatRootSystem (concreteQUnit (I := I) place))

structure ConcreteC3DonorMissingFields ... where
  roots : NatRootSystem A.qUnit
  roots' : NatRootSystem A.qUnit
  kummerClass : CyclotomicTower ...
```

These are declarations, not proofs.  `actualConcreteC3DonorAssembly` supplies
`q`, `qUnit`, tensor fields, and algebraic-closure roots, but **not**
`NatRootSystem (concreteQUnit ...)` in the completion.

`ConcreteC3RootCompletionActual.lean` has roots for

```lean
concreteQUnitAlgebraicClosure (I := I) place
```

i.e. in an algebraic closure, not for the completion unit
`concreteQUnit (I := I) place`.  The schema requires the latter (`qUnit` is
the completion unit).

`S342QVFamilyRootImpossibleActual.natRootSystem_impossible` proves, for the
qVFamily completion unit, that no `NatRootSystem (qVUnit T b)` exists (order /
2l-root obstruction).  That is a specific family, not a general proof about
`concreteQUnit`.

## 3. Existing tensor index is not Fin 2

`ConcreteC3DonorAssemblyActual` uses:

```lean
tensorIndex := ConcreteTensorIndex = FinitePrimePlace 2 7
```

not `Fin 2`.  A Fin-2 donor requires a new `SourcePilotRegionDonors` /
`SourcePilotRegionData` record with the fields above, not the existing
concrete assembly.

## 4. Exact first blocker

The first field that cannot be filled from existing actual data is:

```lean
roots : NatRootSystem (candidateUnits ... q)
```

equivalently:

```lean
Nonempty (NatRootSystem (concreteQUnit (I := I) place))
```

which is exactly `rootsCompletionObstruction` of
`ConcreteC3DonorAssemblyActual`, unproved.  Every later tensor field (and the
`e1⊗e2`, `e2⊗e1` witness) is downstream of this field.

Secondary blocker: the selected completion must have dimension >= 2 (or
otherwise supply independent local elements); this requires an actual number
field `Fmod` with a non-rational finite place and actual place/tuple data.
`SourcePilotRegionData` does not provide such a choice.

## 5. What was delivered (actual)

`tmp/sheaf/xif/paper/S2829SG3bExplicitWitnessBlockerActual.lean`

```text
src 2837 B
SHA256 ce3a8c6fcdb49f66845865bcf3d7e7e4a2e269fa90b5b3f150ebe04cf123ba61
olean 202440 B
SHA256 fc03a9dea9b52b5cd78054b616204b92cb5e2b4207bd38e45ae6a2ffea782b0f
EXIT=0
AXIOMS [propext, Classical.choice, Quot.sound]
QUEUED
```

Contains actual:

```lean
S2829_localFiber_eq_completion :
  C3LogShellFiber C3 i = CommonPrimeCompletion (c3LogShellPlace C3 i)

S2829_localPlace_eq :
  c3LogShellPlace C3 i = C3.tensorPlaces i (C3.tensorTuple i)

S2829_localFiber_finiteDimensional
S2829_region_eq_tensorIntegralRegion
```

and the exact donor requirement structure `S2829TwoFactorWitnessData`.

## 6. Status

```text
Fin 2 tensor fields writable                    YES
concrete completion qUnit + NatRootSystem      BLOCKED (rootsCompletionObstruction)
roots only in algebraic closure                ACTUAL but wrong monoid
ConcreteTensorIndex = FinitePrimePlace 2 7     NOT Fin 2
explicit C3 Fin-2/Q_p donor                    NO ACTUAL DONOR
non-additivity witness                         MISSING
```

No fake q, no fake NatRootSystem, no fake witness, no axiom beyond the
permitted trio.

## 5. Refinement 2026-11-07 — exact blocker chain (kummer)

First unfillable field: `roots : NatRootSystem (candidateUnits ... q)`,
equivalently `Nonempty (NatRootSystem (concreteQUnit ...))`.

Relevant actual/partial facts:

- `ConcreteC3DonorAssemblyActual.rootsCompletionObstruction :=
  `Nonempty (NatRootSystem (concreteQUnit ... place))` is recorded, unproved.
- `ConcreteC3RootCompletionActual` only gives
  `NatRootSystem (concreteQUnitAlgebraicClosure ...)` (algebraic closure roots),
  NOT a Completion-based `qUnit`.
- `S342` proves impossibility of `NatRootSystem (qVUnit T b)` for the qVFamily
  (order/2l-root obstruction), but this is not a general impossibility proof for
  arbitrary `concreteQUnit`.
- `ConcreteTensorIndex = FinitePrimePlace 2 7`, not `Fin 2`.
- Next blocker after roots: an actual nontrivial `Fmod` completion of dimension
  at least 2 plus a selected place; tensor fields and the `e1 ⊗ e2` witness are
  downstream.

`S2829SG3bExplicitWitnessBlockerActual.lean` is ACTUAL (src 2837 B,
SHA CE3A8C6FCDB49F66845865BCF3D7E7E4A2E269FA90B5B3F150EBE04CF123BA61;
olean 202440 B, SHA FC03A9DEA9B52B5CD78054B616204B92CB5E2B4207BD38E45AE6A2FFEA782B0F;
axioms trio): `S2829_localFiber_eq_completion`, `S2829_localPlace_eq`,
`S2829_localFiber_finiteDimensional`, `S2829_region_eq_tensorIntegralRegion`,
and the `S2829TwoFactorWitnessData` record (exact donor requirements, no existence
assertion). No fake q/root/witness.
## 6. Update 2026-11-07 — exact-uniformizer q has NO NatRootSystem (S2836 ACTUAL)

`S2836UniformizerNoRootSystemActual.lean` is ACTUAL:

```text
src 2634 B SHA 2CE0FC4A450BC96D30908F079CC4957118AED354721677DFD89229498203621C
olean 85376 B SHA 1EBF5B69C00317BF86FE1659714A0BD17786071A2B85896733E9182D5C827CF2
axioms trio
```

Actual:

```lean
S2836QUnit w := Units.mk0 (S2806Candidate w).q ...
S2836QUnit_valuation : Valued.v (S2836QUnit w) = WithZero.exp (-1)
S2836_no_square_root_exp_neg_one : (x^2 = exp(-1)) -> False
S2836_no_NatRootSystem : not Nonempty (NatRootSystem (S2836QUnit w))
```

Consequence: the S2806 exact uniformizer (valuation exponent 1) qUnit cannot be
the q of a NatRootSystem / Fin-2 donor. This turns the opaque
`concreteQCandidate` blocker into an impossibility **for the exact uniformizer q**.
A Fin-2 donor would need a different actual q with `v q < 1` and enough roots,
or different completion/root data.