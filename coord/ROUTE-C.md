# ROUTE C — Frey / modularity / height route (inventory + precise roadmap)

Status: 2026-11-12.  Source: `tmp/external/ported/flt` (ported ImperialCollegeLondon/FLT,
commit f6c6a2f).  This document is an **inventory + gap statement**, not a proof.

## 0. Tree inventory (raw numbers)

* 150 `.lean` files under `tmp/external/ported/flt` (not 131 at this commit);
* only **33 `.olean`** compiled: the 19 `Definitions/Def_*` files, `FLT/Basic/Lemmas`,
  `FLT/Deformations/Lemmas`, `FLT/Deformations/RepresentationTheory/{Frobenius,IntegralClosure}`,
  `FLT/FreyCurve/FreyPackage`, and 13 `FLT/Mathlib/*` shims;
* **18 occurrences of `sorry`** (in `KnownIn1980s`, `GaloisRep`, `EllipticCurve/Torsion`,
  `Automorphic`, `HardlyRamified/Frey`) and **16 occurrences of `knownin1980s`**
  (the FLT repo's `axiom knownin1980s {P : Prop} : P`, used as a tactic).
  Both are disallowed as evidence in our project; they mark proof obligations, not green.

Key modules and their state:

| module | declarations | state |
|---|---|---|
| `FLT/FreyCurve/FreyPackage.lean` | `structure FreyPackage` (a,b,c,p, a^p+b^p=c^p, gcd, mod-4/2 conditions; `of_not_FermatLastTheoremFor_p_ge_5`) | **compiled**; FLT-only, no ABC-triple constructor |
| `FLT/FreyCurve/Basic.lean` | Frey curve `Y^2=X(X-a^p)(X+b^p)`, `freyCurve`, `galoisRep` | NOT compiled |
| `FLT/Deformations/RepresentationTheory/GaloisRep.lean` | `GaloisRep`, `.det`, `.baseChange`, `.toLocal`, `.charFrob`, `HasFlatProlongationAt`, `IsIrreducible` | NOT compiled; contains `sorry` |
| `FLT/Deformations/RepresentationTheory/GaloisRepFamily.lean` | `GaloisRepFamily`, `.isCompatible` | NOT compiled |
| `FLT/GaloisRepresentation/Automorphic.lean` | `GaloisRep.IsAutomorphicOfLevel` (quaternion algebra + Hecke eigenform), `cyclic_base_change` | NOT compiled; contains `sorry`/`knownin1980s` |
| `FLT/GaloisRepresentation/HardlyRamified/{Defs,Frey}.lean` | `IsHardlyRamified`; `FreyCurve.torsion_isHardlyRamified`, `torsion_not_isIrreducible` | NOT compiled; both theorems are `sorry` |
| `FLT/AutomorphicForm/QuaternionAlgebra/**` | quaternion algebra basic/finite-dim, Hecke operators abstract/concrete/local | NOT compiled; no classical modular forms, no Shimura curves, no newforms |
| `FLT/Deformations/**` (beyond Lemmas/Frobenius/IntegralClosure) | deformation theory skeleton | NOT compiled |

**Ribet–Takahashi ratio, δ, Shimura curves, newforms, Faltings height, Petersson norm,
Szpiro/ABC: no hits in the ported tree.**  The only “Ribet” text is a docstring in
`FreyPackage.lean` (lines 68-75).  So route C starts from a FLT-specific skeleton only.

## 1. Route C target (precise, to be formalized)

Given an ABC triple `(a,b,c)` with `a+b=c`, `gcd(a,b)=1`, set `N = rad(a*b*c)` and let
`E_{a,b,c} : Y^2 = X(X-a)(X+b)` be the Frey curve (note: the tree's `FreyPackage` uses
`a^p+b^p=c^p`, not ABC; an ABC-triple constructor is PENDING).

* **C0 (δ definition, PENDING).**  Let `f` be the newform associated to `E` (weight 2,
  level `N_f`).  Define the **Ribet–Takahashi ratio**
  `δ(E,f) := N_E / N_f`  (the level-lowering quotient; an integer in the expected cases).
  Formal target:
  `def RibetTakahashiDelta (E : FreyCurve) (f : Newform) : ℚ := N_E / N_f`
  with integrality/positivity lemmas.  The tree has neither `Newform` nor `N_E/N_f`.
* **C1 (modularity, PENDING).**  Wiles–Taylor: every semistable elliptic curve over ℚ is
  modular; equivalently `GaloisRep.IsAutomorphicOfLevel` for the `p`-torsion with a
  weight-2 newform of level `N_E`.  The tree has the *definition* `IsAutomorphicOfLevel`
  and `cyclic_base_change` (Langlands, pre-1990, via `knownin1980s`/`sorry`), but no
  modularity theorem and no Taylor–Wiles patching argument.
* **C2 (Ribet level lowering, PENDING).**  Ribet: if `E` is modular and `\bar\rho_{E,p}`
  is irreducible and arises from a newform of level `N_f | N_E` with `N_f < N_E`
  (after lowering), then a contradiction with the Frey package conditions.  Tree:
  `FreyCurve.torsion_not_isIrreducible` is exactly the needed conclusion but is `sorry`;
  no Ribet theorem, no multiplicity-one/level-lowering machinery.
* **C3 (height formula, PENDING).**  Faltings height vs Petersson norm:
  `h(E) = (1/2)·log δ(E,f) − log ‖f‖ + O(1)`,
  where `‖f‖` is the Petersson norm and the `O(1)` is uniform in the family.  Required
  ingredients: Faltings height `h(E)`, modular parametrization degree, Petersson inner
  product on `S_2(Γ_0(N))`, and the comparison formula.  None are in the tree.
* **C4 (bridge δ bound ⇒ Szpiro6, PENDING).**  If `log δ ≤ (1+ε)(log d + log f)+C`
  (or the equivalent discriminant/radical bound) and `h(E) = ½log δ − log‖f‖+O(1)`, then
  `log q ≤ 6(1+ε)(log d + log f)+C'` for the ABC triple (Szpiro-6 shape).  Formal target:
  `theorem szpiro6_of_delta_height_bound (hδ : ...) (hheight : ...) :
     Szpiro6Shape logq logdf C'`; pure arithmetic + the two analytic inputs.
* **C5 (ABC assembly).**  `Frey + modularity + level lowering + δ bound` ⇒ contradiction
  for hypothetical ABC triples, or directly `ABCConjecture` via Szpiro-6.  PENDING.

Every C-step is independent of the IUT/Step-XI route; the two routes share only
`ABCConjecture`/`Szpiro6Shape` shapes (`Mzk1FinalBoundarySzpiroActual`).

## 2. Shimura curves / modular forms / newforms in the FLT tree

* **Present (not compiled):** `FLT/AutomorphicForm/QuaternionAlgebra/` (Basic, FiniteDimensional,
  HeckeOperators/Abstract, Concrete, Local) gives a quaternion-algebra Hecke algebra and
  automorphic forms on `D^×`; `Automorphic.lean` defines `IsAutomorphicOfLevel` in exactly
  that language (totally definite D, level U_1(S), weight 2, Hecke eigenform π).
* **Absent:** classical modular curves `X_0(N)`, Shimura curves attached to indefinite
  quaternion algebras, q-expansions, spaces `S_k(Γ_0(N))`, newform/oldform theory,
  Atkin–Lehner, Petersson inner product, Hecke eigenvalues normalized as `a_p`,
  Faltings height, modular degree/parametrization.  None of these names occur in the tree.
* Consequence: the C route needs a **new Shimura-curve/newform layer** (or a serious
  Mathlib extension) before C0/C3/C4 can even be stated in the tree's vocabulary.
  `IsAutomorphicOfLevel` is a quaternion-algebra representation-theoretic substitute; it
  does not give a newform `f`, its level `N_f`, or `‖f‖`.

## 3. Missing components (precise)

1. **ABC-triple Frey constructor** (tree only has FLT `FreyPackage`, `a^p+b^p=c^p`).
2. **Modularity theorem** (Wiles–Taylor) for semistable E/ℚ, with patching; tree has only
   the target definition `IsAutomorphicOfLevel` and `cyclic_base_change` (pre-1990 axiom).
3. **Ribet level lowering** and multiplicity-one; tree's needed conclusion
   (`torsion_not_isIrreducible`) is `sorry`.
4. **Classical modular curves/Shimura curves/newforms**: `X_0(N)`, `S_2(Γ_0(N))`, Hecke
   eigenforms, old/new theory, Petersson norm; absent.
5. **Faltings height and modular parametrization degree**, and the height formula
   `h(E) = ½ log δ − log‖f‖ + O(1)`; absent.
6. **δ-bound ⇒ Szpiro6 arithmetic bridge** (can be stated now abstractly; not proved).
7. **Remove `sorry` (18) and `knownin1980s` (16)** from the ported tree before any of it
   can be cited as green; currently only 33 files compile, and the modularity-relevant
   ones (`GaloisRep`, `GaloisRepFamily`, `Automorphic`, `HardlyRamified/Frey`, `FreyCurve/Basic`)
   do not.

## 4. What is genuinely usable today

* `FLT/FreyCurve/FreyPackage.lean` (compiled): the FLT-specific 4-tuple structure and its
  basic lemmas (`hgcdac`, `hgcdbc`, `of_not_FermatLastTheoremFor_p_ge_5`); useful only as
  a template for an ABC-triple package.
* `FLT/Basic/Lemmas`, `FLT/Deformations/Lemmas`, `RepresentationTheory/{Frobenius,IntegralClosure}`
  compiled: local algebra/representation-theory lemmas, not modularity.
* `Definitions/Def_*` (19 compiled) and Mathlib shims: infrastructure, no arithmetic content.

Everything else on route C — modularity, level lowering, Shimura curves/newforms, Faltings
height, δ bound — is **PENDING** and must be built, not recovered from the current tree.


## 12.2 Mestre–Oesterlé input (C route, A845)

### Literature statement (to cite)
J.-F. Mestre and J. Oesterlé, *Courbes de Weil semi-stables de discriminant une
puissance m-ième*, J. Reine Angew. Math. **400** (1989), 173–184.

Precise arithmetic form used by the C route:
- let E/ℚ be an elliptic curve with prime conductor `N = p`;
- let `e_p := ord_p(Δ_E)` be the exponent of `p` in a minimal discriminant;
- if `p > 37` then `e_p ≤ 2` (equivalently `|Δ_E| = p` or `p²`);
- exceptional prime conductors: `p ∈ {11, 17, 19, 37}`.

Exception exponents are curve-dependent; the extremal classical curves have
small exponents (typically `e_p ∈ {2,3,4,5}`), so for the C-route margin one must
either cite the exact exception table or use the uniform safe bound `e_p ≤ 5`.
Exact exception table: **PENDING source-level verification** (network-restricted session).

Status: statement recorded; **not** a Lean theorem, **not** green evidence.
This replaces the earlier memory-only wording in `ROUTES-FINAL-GAP.md:379`.

### T(l) finite-l Szpiro bound (for shehdd arithmetic margin)
Paper finite-l constant:
`T(l) = 6*l*(l+5) / ((l+4)*(l-3))`.
The required discriminant-exponent bound is
`e_p ≤ T(l)*(1 - 1/l) = 6*(l+5)*(l-1) / ((l+4)*(l-3))`.

Numerical table for odd primes `l = 11..101` (T(l), threshold):

| l | T(l) | T(l)(1−1/l) |
|---:|---:|---:|
| 11 | 8.800000 | 8.000000 |
| 13 | 8.258824 | 7.623529 |
| 17 | 7.632653 | 7.183673 |
| 19 | 7.434783 | 7.043478 |
| 23 | 7.155556 | 6.844444 |
| 29 | 6.895105 | 6.657343 |
| 31 | 6.832653 | 6.612245 |
| 37 | 6.688666 | 6.507891 |
| 41 | 6.617544 | 6.456140 |
| 43 | 6.587234 | 6.434043 |
| 47 | 6.534759 | 6.395722 |
| 53 | 6.471579 | 6.349474 |
| 59 | 6.421769 | 6.312925 |
| 61 | 6.407427 | 6.302387 |
| 67 | 6.369718 | 6.274648 |
| 71 | 6.348235 | 6.258824 |
| 73 | 6.338404 | 6.251577 |
| 79 | 6.311985 | 6.232086 |
| 83 | 6.296552 | 6.220690 |
| 89 | 6.276069 | 6.205551 |
| 97 | 6.252791 | 6.188329 |
| 101 | 6.242566 | 6.180758 |

Check: all entries are `> 6.18`; hence **any uniform bound `e_p ≤ 5` suffices**
for this table, while the Mestre–Oesterlé bound `e_p ≤ 2` for `p > 37` suffices
outside the four exceptional primes. The four exceptions need the explicit
curve-by-curve exponent check (PENDING); no Lean numeric certificate yet.

### C-route status after A845
- FLT port stopped (tree has 18 `sorry` + 16 `knownin1980s`; cannot be green evidence).
- `IntegralClosure.lean` port was fixed separately but the 131-file tree is not claimed.
- No Lean theorem in this section; this is a literature/numeric checkpoint.

## 5. §12.2 implementation (A845, `Mzk1PrimeConductorRouteActual.lean`, EXIT=0, olean=True)

* `structure PrimeConductorCurve` (p, hp : p.Prime, e = ord_p(Δ_min));
* `def MestreOesterleBound : Prop := ∀ C, C.e ≤ 5 ∧ (37 < C.p → C.e ≤ 2)`;
  explicit external hypothesis parameter (not sorry/axiom); exceptions p=11,17,19,37 are ≤5;
* `T l = 6*l*(l+5)/((l+4)*(l-3))`;
* **proved**: `five_le_T_one_sub_inv : 5 ≤ T l * (1 - 1/l)` for `l ≥ 11`
  (l=11: 8; limit 6); hence `e ≤ 5 → e ≤ T l*(1-1/l)`;
* **proved**: `paperGap_of_primeConductor_arith`: Mestre–Oesterlé + `D_exact ≥ (1-1/l)log p`
  + `l ≥ 11` ⇒ `e·log p ≤ T l·D_exact`;
* **proved**: `ssIneqExplicit_of_paperGap`: that inequality ⇔
  `SSIneqExplicit (sL l) (e·log p) l (((l+5)/4)·D_exact)`;
* **proved**: `paperGap_of_primeConductor (hMO) ... : SSIneqExplicit ...` (external hMO parameter).

Remaining inputs (not in this file): L1–L7 `D_exact ≥ (1-1/l)log p`; the external theorem
list (modularity Wiles/Taylor–Wiles/BCDT, Ribet level lowering, Mazur, Mestre–Oesterlé)
and the Θ-data legality checks (l∤e_p for e_p≤5<11; semistable ρ̄ surjective for l≥11).
The FLT ported tree is NOT used (18 sorry + 16 knownin1980s; only 33/150 compiled).


## 6. A863 latest greens (2026-11-12 02:0x)

All seven files below have matching oleans (`olean=True`). They are **interfaces/arithmetic shells**, not proofs of the open mathematical content unless stated.

| file | green content | status |
|---|---|---|
| `Mzk1CRouteAssemblyActual` | `CRouteAssemblyInput`, `abcConjecture_of_cRouteAssembly`, `abcConjecture_of_routeC` | GREEN assembly shell; `E7_radicalBound`/`hE7` are explicit ABC-strength hypotheses; ABC gate NOT passed |
| `Mzk1E7ReductionActual` | `E7Data`, `E7Statement`, `jointPackage`, `e7_equiv_chain`, `frey_dictionary_logq/logdf`, `RTProductBound` | GREEN logical equivalence chain; four component Props are fields, not proved |
| `Mzk1DExactLowerActual` | `L1ShellVolume`–`L6Assembly`, `DExactLowerTarget`, `l6Reduced_of_dExactLower`, `ssIneqExplicit_of_dExactLower`, exception table | GREEN L1–L6 arithmetic/defs + L7 **target defined**; L7 lower bound still open; exception e_p values external (`none`) |
| `Mzk1OptimalQuotientActual` | `OptimalQuotient`, `GeometricModularDegree`, `IsOptimal`, `pi_surjective'` | GREEN definition/interface only; existence/degree relation not proved |
| `Mzk1NeronPeriodBridgeActual` | `NeronPeriodData`, `DegreePeterssonRelation`, `FaltingsHeightVolumeRelation`, definitional equivalences | GREEN interface; relations are structure fields, not proved |
| `Mzk1FreyABCInvariantsActual` | `freyB2/B4/B6`, `freyC4_eq`, `freyC6_eq`, `freyDelta_eq_sixteen_mul_sq`, `log_freyDelta_eq`, `FreyConductorRadical` | GREEN invariants/identities; conductor-radical relation is a structure, local proof GAP |
| `Mzk1FreyConductorFinalActual` | `freyDeltaNat_eq`, `c4_poly_not_dvd`, `LocalMultiplicativeData`, `ConductorExponentOne`, `OggSaitoData` | GREEN p∤6 c4 divisibility; Delta/c4 valuations are fields; p=2,3 external Ogg–Saito data |

### Remaining gap table

| gap | green now | still missing |
|---|---|---|
| **L7** `D_exact >= (1-1/l) log p` | `DExactLowerTarget` defined; L1–L6 arithmetic | geometric lower bound L7 not proved |
| **E7 four components** | `e7_equiv_chain` logical wiring; `NeronPeriodData`/`OptimalQuotient`/`FaltingsHeightData`/Petersson interfaces | Faltings bound, Petersson identity/asymptotic, Neron lower bound, optimal-quotient existence/degree relation |
| **Frey dictionary two equations** | `FreyLogDictionary` def; `frey_dictionary_logq`, `frey_dictionary_logdf` re-exports | prove `logq=2logdelta`, `logdf=logN` from the actual geometry |
| **Frey conductor rad** | `FreyConductorRadical`; `c4_poly_not_dvd`; `freyDeltaNat_eq` | prove `N=rad(abc)` and `ord_p(N)=1` at multiplicative p∤6; p=2,3 external |
| **Frey valuations** | `LocalMultiplicativeData` fields; `c4_poly_not_dvd` | arithmetic bridge to `padicValNat`/Weierstrass invariants; v2/v3 Ogg–Saito input |

Conclusion: the latest greens close only the **wiring/arithmetic interfaces**; the five rows above are the live C-route gaps. No unconditional ABC, no unconditional Szpiro, and no removal of the explicit E7_radicalBound hypothesis.

## 6. Interface alignment (A878): L7 ↔ abc `SSIneqExplicit`

| interface | file | shape |
|---|---|---|
| `DExactLowerTarget C l D_exact` | `Mzk1DExactLowerActual` | `(1 - 1/l)·log p ≤ D_exact` (named target; L7) |
| `DExactExplicit e_F f l δ_l C₀` | `Mzk1L7DefinitionalActual` | `(1 - 1/(e_F·l))·log f + δ_l·log l + C₀` (paper-faithful **definition**) |
| `DExactLowerTarget_of_explicit` | `Mzk1L7DefinitionalActual` | `e_F=1, f=p, δ_l log l + C₀ ≥ 0, l≥1 ⇒ target` (proved) |
| `DExactLowerTarget_of_explicit_general` | same | `e_F≥1` version (coefficient only grows) |
| `ThetaDataInvariants C l` | same | external fields: `D_eq`, `e_F=1`, `f=p`, `l≥1`, `rem_nonneg` |
| `L7_of_invariants` | same | definition-level L7 closure |
| `ssIneqExplicit_of_L7` / `ssIneqExplicit_of_invariants` | `Mzk1L7ProofActual` / `Mzk1L7DefinitionalActual` | L7 + Mestre–Oesterlé + Θ-data legality ⇒ `SSIneqExplicit (sL l) (e·log p) l (((l+5)/4)D_exact)` |
| `paperGap_of_primeConductor` | `Mzk1PrimeConductorRouteActual` | same conclusion via L6 reduction |

Alignment: the abc side consumes exactly `SSIneqExplicit (sL l) logQ l V`
(`Mzk1SSIneqExplicitFormActual`); L7's `D_exact` enters as `V = ((l+5)/4)·D_exact`
and `logQ = e_p·log p`, so `DExactLowerTarget` is precisely the missing input of the
`paperGap` theorem.  No naming mismatch remains; the only external identification is
`ThetaDataInvariants` (paper normalization ↔ explicit expression).
