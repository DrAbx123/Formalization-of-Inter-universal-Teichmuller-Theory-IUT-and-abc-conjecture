# PORT-PRIORITY — C-route port ordering

Live snapshot; ranks by C-route value, not by file count. `%` = compiled/source.

## 1. Port sources

| rank | source | files | compiled | C-route value | dependency | expected first error |
|---|---|---|---|---|---|---|
| P0 | FLT271 (`tmp/external/flt271`) | 271 | 0 | highest: Frey/Galois/patching/level-lowering skeleton (260 FLT; Patching 14 = 7 top + 7 Utils, closure 19) | own FLT library; toolchain v4.35.0 vs project v4.32.2 | `unknown module` / `unknown identifier` (toolchain+namespace drift), then typeclass mismatch |
| P0 | anthro Definitions (`tmp/external/flt-defs`) | 1450 | 0 | C language layer: Def_ModularCurve 291, Def_AutomorphicForm 106, Def_CuspForm 32, Def_Hecke 10, Def_ModularForm 5 | own Definitions imports; toolchain v4.33.1 | `unknown module`/`unknown identifier` (v4.33.1 API drift) |
| P0 | Mathlib ModularForms | 19 | 38 oleans (100%) | zero-cost base: CuspForm, qExpansion, discriminant, petersson | Mathlib green | none (green) |
| P1 | Heights remaining | 8 (64 total/56 compiled) | 8 remaining | Faltings/height scaffold; `SilvermanHeight` not compiled and explicitly not Arakelov/Faltings | Mathlib + Heights modules | missing import/typeclass in period-data integration |
| P1 | EllipticCurves remaining | 455 (480 total/25 compiled) | 455 remaining | Néron–Ogg–Shafarevich/reduction/Tate modules | Mathlib + EllipticCurves basics | `unknown identifier`/failed instance (Basic and Reduction not compiled) |
| P2 | CurvesJacobian | 590 | 0 | Jacobian/period side; useful for Néron period, huge | scheme/function-field foundations | `unknown module` (scheme/API layers not compiled) |
| P2 | FormalSchemes remaining | 570 (647 total/77 compiled) | 570 remaining | scheme foundations; indirect | Mathlib schemes/own glue | `unknown module`/instance mismatch (glue layer) |
| P2 | WeilCurves | 49 | 0 | Weil curves/Bombieri/point bounds; low-medium | function field/height APIs | `unknown identifier` (all dependencies uncompiled) |
| P3 | Oka remaining | 705 (828 total/123 compiled) | 705 remaining | low for C route; complex analytic foundations | Oka own tree; 9 axiom files | axiom/import mismatch; not evidence until axioms removed |
| P3 | flt-regular | 25 | 0 | low: regular-prime FLT case only | toolchain v4.36.0-rc2 | `unknown module` (v4.36 rc drift) |
| P3 | FLT ported remaining | 117 (131 total/14 compiled) | 117 remaining | scaffolding only; not evidence | shims; no lean-toolchain | `unknown identifier`; 5 sorry/1 axiom upstream |

## 2. C-route component -> best source

| component | best source | fallback |
|---|---|---|
| newform | **anthro** `Thm_CuspForm_*isNewform*` (101) + `Def_CuspForm_Newforms` | Mathlib CuspForm base |
| Shimura | **anthro** `Thm_CerednikDrinfeld_ShimuraCurveModel_*` (28) + `Def_CerednikDrinfeld_ShimuraCurve` | none (defer with ModularCurve 7708) |
| δ (parameterization degree) | **no source**; self-build | anthro `Def_ModularCurve` language |
| Faltings height | **vendor Heights** scaffold + self-build | anthro Height-named lemmas (199) |
| Néron period | **anthro** 26 `Def_Neron*`/`J*Neron*` definitions | vendor EllipticCurves reduction (uncompiled) |
| Petersson norm | **Mathlib** `petersson` integrand + anthro 4 `Def_CuspForm_Petersson*` | none for norm estimates |

## 3. Stage4 port priority (A854)

1. `Thm_FreyPackage_frey_isModular` (closure unknown; extract first).
2. `Thm_FreyPackage_atPNewLowering`; `Thm_RibetIrr_*` (13); Taylor–Wiles entries (23+8).
3. `Thm_CuspForm_*isNewform*` (101) + Heights (199).
4. **DEFER** `ModularCurve` 7,708 (includes Shimura/Cerednik–Drinfeld 28 + 750 QM/fake EC and δ language).

## 4. Not evidence (sorry/axiom upstream)

- FLT271: **70 sorry / 3 axiom declarations** (`Assumptions/{KnownIn1980s,Mazur,Odlyzko}.lean`), stage4 A868 correction; port source only after removal.
- FLT ported: 5 sorry / 1 axiom (`KnownIn1980s`).
- EllipticCurves: 9 sorry / 1 axiom (`FormalGroup/LogAdditivity` etc.).
- Oka: 9 axiom files; FormalSchemes: 2 axiom files (`FormalGm`, `GlueDataSectionGlue`).
- anthro, flt-regular, Heights, CurvesJacobian, WeilCurves: no sorry/axiom detected in source scan.
- Mathlib ModularForms: no actual sorry (only a doc comment).
