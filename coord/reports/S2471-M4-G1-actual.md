# S2471: M4/G1 actual action aggregation + exact missing

Date: 2026-11-03. Layer O (S2046 M4/G1). Serial build only.

## Deliverable

`tmp/sheaf/xif/paper/S2471M4G1Actual.lean`

```text
EXIT=0
lines=62
source SHA256=88D70151AE5B851637E7CBD736FB0FD5A798326C1EC8378FE313BADF6EE1D1E0
olean SHA256=D7737346CA7E948689CA9CCFB28A80BC863410F02B53BEEC8DF2591B67E6AC7D
olean bytes=160992
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2471M4G1Actual.olean
axioms:
  S2471MuHatAction -> propext, Classical.choice, Quot.sound
  S2471G1TopologicalModuleOf -> trio
  S2471G1EquivarianceRequired -> trio
```

## G1 actual

`S2442MuHatAction : Gv p →* MulAut (muHatZ p)` is actual from the actual
muQZ action S2442/S2432. S2471 re-exports it:

```text
S2471MuHatAction : Gv p →* MulAut (muHatZ p)
```

This is the algebraic `muHatAction` actual part. Conditional module data:

```text
S2471G1TopologicalModuleOf
  (h : muHatComparison p)
  (heq : S2471G1EquivarianceRequired p h) :
  S2046G1TopologicalModuleData p
```

where the exact equivariance missing is:

```text
S2471G1EquivarianceRequired h
  = ∀ g x,
      S2046G1ModuleEquivOfComparison p h (S2471MuHatAction p g x)
        = S2046G1PsiCnsAction p g
            (S2046G1ModuleEquivOfComparison p h x)
```

Thus G1 is actual except:

1. `muHatComparison p` (S2017, exact missing);
2. `S2471G1EquivarianceRequired p h` (no inhabitant).

### Topology / continuity

Exact missing:

```text
S2471MuHatTopologyRequired := TopologicalSpace (muHatZ p)

S2471MuHatContinuousActionRequired
  top : TopologicalSpace (muHatZ p)
  continuous_action :
    Continuous (fun q : Gv p × muHatZ p =>
      S2471MuHatAction p q.1 q.2)
```

No topology on `muHatZ` and no continuity theorem exists in the tree; this is
an explicit missing structure, not assumed.

## M4 actual / missing

Actual witnesses exist for the Kummer map and Kummer image; H2/Br comparisons
are actual. The normalization itself remains exact:

```text
S2471M4NormalizationRequired := PsiCnsKummerNormalization p
S2471M4NormalizationData := S2136M4NormalizationData p
```

No norm map `PsiCnsCohomology p →* Multiplicative Zhat` is constructed. The
H2/Br equivalences do not supply the H^1/cup-product normalization; exact first
missing remains `S2136M4NormalizationData p`.

## Status

- G1 algebraic action: actual.
- G1 module data: conditional on `muHatComparison` + equivariance.
- G1 topology/continuity: exact missing.
- M4 normalization: exact missing (`S2136M4NormalizationData`).
- No fake trivial action, no assumed comparison, no terminal/point substitution.

## Next executable subgoal

G1:
1. construct/prove `muHatComparison p` (S2017);
2. prove `S2471G1EquivarianceRequired` by comparing the actual muQZ action
   with the S2046 PsiCns action through the cyclotome comparison;
3. declare a topology on `muHatZ` and prove joint continuity (S2159 has the
   discrete topology on muQZ only).

M4:
1. construct the cup-product normalization map;
2. prove surjectivity, Kummer image, and kernel-units identities.

## Evidence

- S2442MuQZFinalActual.lean (actual muQZ/muHat action), olean exists.
- S2046G1CyclotomeActual.lean, S2136M4KummerNormalizationActual.lean,
  S2017VerlagerungActual.lean: existing oleans and prior axiom probes.
