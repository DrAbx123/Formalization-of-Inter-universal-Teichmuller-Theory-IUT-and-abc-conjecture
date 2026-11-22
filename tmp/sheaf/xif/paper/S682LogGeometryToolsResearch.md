# S682: log geometry / Kummer log etale / root stack / perfectoid tools audit

Date: 2026-10-30. Scope: reusable formal objects for the O^▷ 2l-root and mu_2l orbit, and whether they close the S680 exact gap. No claim that this proves IUT.

## 1. Mathlib inventory (checked in D:\lean\.lake\packages\mathlib\Mathlib)

### Present

| Tool | Mathlib path | What it gives | Usable for O^▷? |
|---|---|---|---|
| Kummer extension / Kummer polynomial | Mathlib/Algebra/Polynomial/Kummer.lean? and Mathlib/FieldTheory/KummerExtension.lean | abstract Kummer extensions and polynomials | only abstract field roots; no log structure |
| Adic completion | Mathlib/Topology/Algebra/AdicCompletion.lean and RingTheory/AdicCompletion/* | adic completion, complete rings | ambient completion only |
| Perfectoid / Fontaine theta | Mathlib/RingTheory/Perfectoid/Untilt.lean, FontaineTheta.lean, BDeRham.lean | perfectoid rings, tilting, theta | not a root stack or Kummer log cover |
| p-adic fields / algebraic closure | Mathlib/NumberTheory/Padics/PadicNumbers.lean; Mathlib/FieldTheory/... | algebraic closure and roots | gives abstract roots in an alg. closed field |
| Group torsion / quotients | Mathlib/GroupTheory/Torsion.lean | torsion subgroup and quotient | exactly the algebraic model of mu-torsion quotient |

### Absent (grep counts 0 in Mathlib)

- `LogStructure`, `logStructure`, `MonoidLog`
- `LogScheme`
- `RootStack` / `rootStack`
- Kummer log etale / log etale site
- log structures on schemes / fs log schemes / Kummer covers as log schemes

Mathlib has adic spaces only as an open draft PR (not in this checkout):
- https://github.com/leanprover-community/mathlib4/pull/30978

Mathlib has adic completion, not adic spaces:
- https://github.com/leanprover-community/mathlib4/pull/31295

Conclusion: Mathlib cannot directly formalize a log scheme, Kummer log etale cover, root stack, or its mu_2l action. The perfectoid/adic-completion tools are ambient arithmetic topology, not the O^▷ root object.

## 2. Repo inventory (LeanFormal current, not vendor snapshots)

### Actual Kummer/root objects that are reusable

| Object | File | Content |
|---|---|---|
| `NatRootSystem` | LeanFormal/IUT/IUTII/Kummer/NatRootSystem.lean | `root : Nat -> M^x`, `root_one`, compatibility `root (n*k)^k = root n`, `pow_self` |
| `AlgebraicClosureRootSystem.chainRoot` | same | actual n-th roots in an algebraically closed field |
| `CompatibleRootSystem` | IUTII/Kummer/CompatibleRoots.lean | rational roots `roots : Q ->+ Additive M` and compatibility |
| `AdjoinRootEmbedding` | IUTII/Kummer/RootRealization.lean | formal Kummer root realization into a field |
| `KummerClass` / `CyclotomicTower` | IUTII/Kummer/KummerClass.lean | Galois/Kummer cocycle layer, torsion tower |
| `TimesMuQuotient` | IUTII/Kummer/TimesMuQuotient.lean | `U / torsion(U)`, descended actions, kernel/surjectivity; algebraic model of `O^xmu` |
| `TimesMuKummer.Isomorphism` | IUTII/Kummer/TimesMuIsm.lean | Ism-orbit/representative structure for Kummer isomorphisms |
| `LocalGaloisKummerAction` | IUTII/Kummer/LocalGaloisKummerAction.lean | local absolute Galois action on algebraic-closure units, stabilizer openness |
| `KummerRootRatioData` | IUTII/Kummer/KummerRootRatio.lean | root ratio unit contract |
| `SourceKappaOrbitUnitsActionSupply` | IUTII/Frobenioid/SourceKappaOrbitUnitsActionSupply.lean | source note: `O^triangleright = O^perp / mu_2l`, orbit/action supply |

### Root stack

- Current `LeanFormal` has **no** `RootStack` / root-stack object (grep 0).
- `vendor/promachina/snapshots/...` contains historical `ThetaRootStackRealization` / `badLocalThetaRootStacks`, but these are old snapshots and are not current LeanFormal modules.
- Therefore the current repo does not provide a root stack whose generic point carries the 2l-root and whose inertia is mu_2l.

### log-shell / positivity

- `OtriangleLogVolumeObjectActual`, S150, S104 provide:
  - `integralLogShell : Set (CommonPrimeCompletion place)`
  - `unitLog : (Integers ...)^x -> CommonPrimeCompletion place`
  - `formalBoundaryLog`
  - `quotientNormalizedLog`
  - `normalizedUnitLogMap`
  - symbolic canonical `logPi = (0,1)`
- These are *analytic/log-volume* data on a completion. They do not define a log structure in the sense of log geometry, and there is no map from O^times(A) to the completion units.

## 3. What can be reused for O^▷ 2l-root and mu_2l orbit

### Reusable without new geometry

1. **Abstract 2l-root existence**
   - `AlgebraicClosureRootSystem.exists_pow_root` and `chainRoot`
   - `AdjoinRootEmbedding` for the formal root.
   These give an actual root of a unit in an algebraically closed field, but not in `O^triangleright`.

2. **mu_2l action on roots**
   - `CyclotomicTower` gives torsion components `component n ^ n = 1`.
   - `TimesMuQuotient` gives the quotient by all torsion and descended `MulAut`.
   - `TimesMuKummer.Isomorphism` gives orbit/representative behavior.
   These model the mu_2l orbit algebraically, provided the ambient group and its 2l-root system are supplied.

3. **q/root sections at abstract group level**
   - `NatRootSystem.pow_self` and `CompatibleRootSystem` give the section equation `root^(2l)=q`.
   - `KummerRootRatioData` gives the Galois root ratio contract.
   These can populate an abstract `OtriUnitsSections`-like object if the q/root units and the 2l-root system already live in the same commutative group.

### Not reusable for the geometric O^▷ object

- No log structure, no Kummer log etale cover, no log scheme.
- No root stack / inertia stack.
- No current construction of `O^triangleright` itself or of an isomorphism
  `O^triangleright ~ O^perp / mu_2l` with the geometric monoid.
- No map from `Units (LinearBaseIdentityEndomorphism A)` to a local completion unit group. This is the S680 exact gap.

## 4. Direct answer for S680 exact gap

S680's minimal data are:

```lean
OtriFromLogShellSections S :=
  sections : OtriUnitsSections S    -- q/root units in Units(End A), root^(2l)=q
  splitting : Prop
  structuralSheafCondition + proof
  qSection_reflects_qVFamily : Prop
```

The research tools can supply:

- the **abstract** equation `root^(2l)=q` (`NatRootSystem.pow_self`);
- an **abstract** mu_2l/torsion orbit (`CyclotomicTower`, `TimesMuQuotient`);
- **abstract** roots in an algebraic closure (`AlgebraicClosureRootSystem`).

They **cannot** supply:

1. the actual q/root units inside `Units(LinearBaseIdentityEndomorphism A)`;
2. a map from the log-shell completion units to those endomorphism units;
3. the root stack/log structure that would make the 2l-root canonical.

Therefore the S680 exact gap is **not closed** by current Mathlib or current LeanFormal tools. A direct abstract construction can only be made after supplying the missing geometric map/carrier. The minimal honest object remains S680's `OtriFromLogShellSections` plus explicit q/root units and their power relation.

## 5. Recommended next formalization steps

1. **Do not** import perfectoid/adic spaces for O^▷; they formalize a different topology.
2. Reuse `NatRootSystem` / `CompatibleRootSystem` only for the abstract root equation.
3. Reuse `TimesMuQuotient` / `TimesMuKummer.Isomorphism` for the mu_2l orbit if an ambient commutative group is fixed.
4. To close S680, first build the missing bridge:
   - a carrier map from `Units(LinearBaseIdentityEndomorphism A)` to `(Integers completion)^x` or to a root stack unit group;
   - then define the positivity/log-shell submonoid as the preimage of the integral log shell;
   - then transport the 2l-root and mu_2l action along that map.
5. If a genuine root-stack formalization is desired, it requires new algebraic-geometry infrastructure (log schemes, Kummer covers, root stacks) not currently available in Mathlib; this is a multi-file project, not a one-file bridge.

## Sources checked

- Mathlib search in `D:\lean\.lake\packages\mathlib\Mathlib` (grep counts above).
- Mathlib adic spaces draft: https://github.com/leanprover-community/mathlib4/pull/30978
- Mathlib AdicCompletion API: https://github.com/leanprover-community/mathlib4/pull/31295
- Current LeanFormal Kummer modules listed in section 2.
