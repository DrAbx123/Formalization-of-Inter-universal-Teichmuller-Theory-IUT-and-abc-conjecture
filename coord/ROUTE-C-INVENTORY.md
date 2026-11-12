# ROUTE-C-INVENTORY — FLT port tree / C-route components

Snapshot: `tmp/external/ported/flt` (FLT port tree + local Definitions).

| tree | source `.lean` | compiled olean |
|---|---|---|
| `FLT/` | 131 | **14** |
| `Definitions/` | 19 | **19** |
| `manual_compile/` | 0 (14 `.log`) | - |
| **total** | **150** | **33** |

Live count differs from the task brief (131 FLT files is correct for the `FLT/` subtree; total tree is 150 including Definitions).

## 1. FLT subtree by theme

| theme | files | compiled | content |
|---|---|---|---|
| Basic | 1 | 1 | basic lemmas |
| FreyCurve | 2 | 1 | Frey package (compiled), Basic (not compiled) |
| Deformations | 8 | 3 | representation theory/continuous reps; Lemmas, Frobenius, IntegralClosure compiled |
| GaloisRepresentation | 3 | 0 | automorphic/hardly-ramified definitions |
| AutomorphicForm | 7 | 0 | quaternion algebra/Hecke operators (abstract) |
| EllipticCurve | 1 | 0 | torsion |
| DedekindDomain | 9 | 0 | adic valuation/adele ring/completion |
| NumberField | 7 | 0 | adele ring/infinite places/padics |
| HaarMeasure | 8 | 0 | Haar char/padic measures |
| DivisionAlgebra | 1 | 0 | finiteness |
| QuaternionAlgebra | 1 | 0 | number field quaternion algebra |
| Assumptions | 1 | 0 | known-in-1980s assumptions |
| Hacks | 1 | 0 | right-action instances |
| Mathlib | 81 | 9 | Mathlib shims: Algebra/FieldTheory/GroupTheory/LinearAlgebra/MeasureTheory/NumberTheory/Topology |
| **total** | **131** | **14** | |

## 2. Definitions subtree (19/19 compiled)

- `Def_AlgebraicCurve_*` (11): adelic index, canonical divisor, Cech sections, divisor class group, curve over, local residue, regular differentials, repartitions, Riemann–Roch rows, Serre pairing, Weil of Kähler.
- `Def_AlgebraicGeometry_*` (6): coherent base change, **Néron model property bundle carrier**, smooth proper curve base, finite map data, two affine open cover, two-chart Cech.
- `Def_ModularCurve_*` (2): canonical divisor, canonical divisor uniformizer.

## 3. C-route component matrix

| component | present? | compiled? | evidence | needed port |
|---|---|---|---|---|
| Modular forms / newforms | **NO** | - | no `ModularForm`, `Newform`, `Weight`, `Cusp` files; only abstract `AutomorphicForm/` (7, 0 compiled) | full modular-form/newform port (weight/Hecke eigenforms, q-expansions) |
| Shimura curves | **NO** | - | no `Shimura` file | full Shimura-curve theory / quaternionic modular curves |
| Modular parameterization degree δ | **NO** | - | no `Parametrization`/`Delta`/`degree` file; only curve divisor definitions | `X_0(N) -> E` parameterization and degree bound δ |
| Néron periods | **PARTIAL** | one definition compiled | `Definitions/Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier` only | Néron model/period lattice, period bounds |
| Petersson norm | **NO** | - | no `Petersson` file | Petersson inner product/norm estimates |
| Frey curve skeleton | partial | 1 of 2 | `FreyCurve/FreyPackage` compiled; `FreyCurve/Basic` not | complete Frey model/discriminant/conductor lemmas |
| Galois representations/deformations | partial | 3 of 8 Deformations compiled | `Deformations/Lemmas`, `Frobenius`, `IntegralClosure`; `GaloisRepresentation/` 0/3 | residual modularity/deformation theory |
| Adelic/completion/Haar infrastructure | NO (in FLT) | 0 | DedekindDomain 9, NumberField 7, HaarMeasure 8 all uncompiled | port/completion of adelic + Haar layer |
| Mathlib shims | partial | 9 of 81 | `Mathlib/...` 9 compiled | rest of shims as needed |

## 4. Verdict

- The FLT port currently supplies a **Frey/Galois/deformation skeleton** plus curve/divisor/Néron-carrier definitions; it does **not** supply the analytic/automorphic side of route C.
- **Modular forms/newforms, Shimura curves, parameterization degree δ, Néron periods and Petersson norm are MISSING** (Néron only a carrier definition). Route C cannot reach the δ/Néron/Petersson comparison without substantial new ports.
- Immediate reusable greens: `Definitions/` (19), `FLT/Mathlib` shims (9), `FLT/Deformations` (3), `FLT/FreyCurve/FreyPackage` (1), `FLT/Basic/Lemmas` (1).
- Recommended next ports: (i) modular forms/newforms + Hecke; (ii) Shimura curves/quaternionic automorphic forms; (iii) parameterization degree; (iv) Néron periods/lattices; (v) Petersson norm.


## 6. C-route resource inventory v2 (Mathlib + vendor + LeanFormal)

### 6.1 Class A — greens we already have (vendor / LeanFormal / Definitions)

| asset | files (green) | key declarations / role |
|---|---|---|
| Mathlib modular forms | 19 source files, green oleans present | `ModularForm`, `CuspForm`, `SlashInvariantForm` (`ModularForms/Basic.lean`); `qExpansion`/`cuspFunction` (`QExpansion.lean`); `ModularForm.discriminant` (`Discriminant.lean`); `petersson` (`Petersson.lean`); congruence subgroups, cusps, level one, Valence formula |
| Mathlib Hecke ring | `NumberTheory/HeckeRing/Defs.lean` green | `IsHeckeTriple`, `HeckeCoset` (abstract Hecke pair, not classical Hecke operators on modular forms) |
| vendor `Heights` | 55/64 compiled | `ModularJ`, `ModularJFibers`, `PeriodPairScaling`, `LatticeWeierstrass`, `LatticeEisenstein`, `ArchimedeanAlgebraicRealization`, `Curve/{CondHeight,DivisorHeight,TupleHeight,Conductor,ModelChange}`, `Absolute/Northcott`, `Different/Conductor` — complex period/height scaffolding |
| vendor `EllipticCurves` | 25/480 compiled | `Torsion/*` (division polynomials, torsion structure); **no** `Basic`/`Reduction/NeronOggShafarevich` olean |
| vendor `CurvesJacobian`, `WeilCurves` | 0 compiled of 590/49 | sources exist, no green oleans |
| `Definitions/` | 19/19 green | algebraic curve/divisor/Serre/Riemann–Roch definitions; `NeronModelPropertyBundleCarrier`; modular curve canonical divisor |
| `FLT/` | 14/131 green | `FreyCurve/FreyPackage`, `Deformations/{Lemmas,Frobenius,IntegralClosure}`, `Basic/Lemmas`, Mathlib shims — Frey/Galois/deformation skeleton only |
| `LeanFormal` | no Faltings/Néron-period/Shimura asset | only textual Hodge–Arakelov references (`IUTII/...`), no construction |

### 6.2 Class B — exist in Mathlib (green) but not specialized enough for route C

- **Modular forms / cusp forms**: Mathlib has full basic theory, q-expansions, discriminant, Eisenstein series, congruence subgroups, valence formula.
- **Petersson**: Mathlib `Petersson.lean` defines the `petersson` integrand; **no** norm/estimate theorems for newforms.
- **Hecke algebra**: Mathlib `HeckeRing/Defs.lean` gives abstract Hecke triples/cosets; **no** classical Hecke operators/Hecke eigenforms on modular forms.
- **Weierstrass period lattice** (complex): vendor `Heights` has period-lattice/quotient theory; this is *analytic complex* period theory, not p-adic/global **Néron period**.
- **Height scaffolding**: vendor `Heights` has formula-defined Silverman height and curve/divisor heights; `SilvermanHeight.lean` is **not compiled** and explicitly says it does not prove the Arakelov/Faltings height equality.

### 6.3 Class C — completely absent / must be newly ported

| component | status | needed |
|---|---|---|
| Newforms / newform subspace / Hecke eigenforms | **ABSENT** | newform theory, Atkin–Lehner, eigenform q-expansions |
| Shimura curves / quaternionic automorphic forms | **ABSENT** | Shimura curve construction, Jacquet–Langlands, Hecke modules |
| Modular parameterization degree δ | **ABSENT** | `X_0(N) -> E` parameterization and degree bound |
| Faltings height (Arakelov) | **ABSENT** | Arakelov metric/period integration and Faltings height comparison; vendor `SilvermanHeight` explicitly does NOT prove it |
| Néron periods / period lattice of Néron model | **ABSENT** | Néron model + period pairing; vendor period lattice is complex-analytic only |
| Petersson norm (estimates) | **ABSENT** | norm/inner-product estimates for newforms; Mathlib only defines the integrand |
| Modularity / deformation theory for C | **PARTIAL** | FLT Deformations 3 green; GaloisRepresentation 0; residual modularity absent |

### 6.4 Verdict

- **Mathlib + vendor give the modular-forms/period-lattice *language*, but not the C-route comparison objects.**
- We have green: Definitions 19, FLT 14, Heights 55, EllipticCurves 25 (torsion only), Mathlib ModularForms.
- Completely absent: **newforms, Shimura curves, δ, Faltings height, Néron periods, Petersson norm estimates**. These are the blocking assets for route C.
