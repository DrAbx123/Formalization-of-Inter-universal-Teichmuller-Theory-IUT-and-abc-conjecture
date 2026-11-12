# S2473: M4/G1 exact interfaces after S2471

Date: 2026-11-03. Layer O (S2046 M4/G1). Serial `lake env lean -j1` only.

## Deliverable

`tmp/sheaf/xif/paper/S2473M4G1Interfaces.lean`

```text
EXIT=0
lines=50
source SHA256=A02835D5F6C89D15A3900395CD2BD753BEE35E540B5A2C025A227DE1671578F7
olean SHA256=02A2AE49BDBE7737FFC11F6C7649BC5A3D68A15A42937AA63D8DD04DFB155AF9
olean bytes=138952
olean path=.lake/build/lib/lean/tmp/sheaf/xif/paper/S2473M4G1Interfaces.olean
axioms:
  S2473G1TopologicalModuleOf -> propext, Classical.choice, Quot.sound
  S2473G1EquivariantComparisonRequired -> trio
```

## G1 actual / exact missing

Actual from S2442/S2471:

```text
S2471MuHatAction : Gv p →* MulAut (muHatZ p)
```

The only remaining G1 inputs are:

```text
S2473G1EquivariantComparisonRequired p
  comparison : muHatComparison p
  equivariance : S2471G1EquivarianceRequired p comparison

S2471G1EquivarianceRequired h
  = ∀ g x,
      S2046G1ModuleEquivOfComparison p h (S2471MuHatAction p g x)
        = S2046G1PsiCnsAction p g
            (S2046G1ModuleEquivOfComparison p h x)
```

Conditional actual G1 data:

```text
S2473G1TopologicalModuleOf
  (E : S2473G1EquivariantComparisonRequired p) :
  S2046G1TopologicalModuleData p
```

Exact topology/continuity missing:

```text
S2473G1ContinuousActionRequired p
  top : TopologicalSpace (muHatZ p)
  continuous_action :
    Continuous (fun q : Gv p × muHatZ p =>
      S2471MuHatAction p q.1 q.2)
```

### Why `muHatComparison` alone does not give equivariance

`muHatComparison p` is only:

```text
Nonempty (muHatZ p ≃* PsiCnsTorsionCyclotome p)
```

It contains no naturality/action compatibility, and
`S2046G1ModuleEquivOfComparison` chooses an equivalence by
`Classical.choice`. An arbitrary chosen equivalence need not intertwine the
two actions. Hence equivariance is a genuine additional exact input, not a
consequence of the existing comparison.

No comparison/equivariance inhabitant is fabricated.

## M4 exact missing

```text
S2473M4NormalizationRequired p := S2136M4NormalizationData p
S2473M4NormalizationProp p := PsiCnsKummerNormalization p
```

Actual H2/Br comparisons and Kummer map/image do not define
`norm : PsiCnsCohomology p →* Multiplicative Zhat`; the cup-product
normalization API is absent. Exact first missing remains
`S2136M4NormalizationData p` with fields:

```text
norm, surjective, kummer_image, kernel_units
```

## Status

- G1 algebraic action: actual.
- G1 equivariant comparison: exact interface, no inhabitant.
- G1 topology/joint continuity: exact structure, no inhabitant.
- M4 normalization: exact missing.
- No fake action, no assumed comparison, no terminal/point substitution.

## Next executable subgoal

G1: prove `S2471G1EquivarianceRequired p h` for a *chosen natural*
comparison `h`, or construct the comparison together with naturality.
M4: construct the cup-product norm and prove the four fields.
