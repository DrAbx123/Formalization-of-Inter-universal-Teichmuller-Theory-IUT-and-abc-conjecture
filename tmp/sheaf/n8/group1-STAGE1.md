# N8 group 1 - stage 1: prime-strip / Frobenioid / Hodge-theater source-object links

- Node: `n8-group1-source-objects` (`dag/nodes/n8-group1-source-objects.json`).
- Stage: 1 only. No production file edited, no Lean file written or compiled, no proof attempted.
- Version anchor: git HEAD `9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee`; Lean `v4.32.2`; Mathlib `v4.32.2` / rev `905b95818eb32af7874a58b427f50c1711a5e96c` (SETUP.md).
- Date: 2026-10-22.
- Chapter: `logs/coordination/n8-distilled-01-frobenioid-construction-20261018.md` (SHA256 `4812D0858E53B5AAE40DC86BF8765CA8216D89454EF622EAC0EA01F3FC5167D3`).
- Skeleton: `tmp/sheaf/n8/N8-STAGE1-MASTER.md` (SHA256 `32E518690E96F080EDDE9D9491E6F18803A0259193C3DB10BFB55A1F1F9C4CF8`).
- Deliverable: this file only. STATE/queue/DAG are left to the parent; see section 9.
- Method: SHEAF node-local stage 1, consumer first. Freeze the paper objects and quantifiers, list the donors that actually exist at the pinned sources with `file:line`, state the exact gaps, and name one smallest next statement. No whole-repo audit.

## 1. Verdict

The arithmetic half of the chapter is already in the tree, at coordinate level and at actual number-field places: the local fractional-ideal dictionary is proved, the global ideal-family category and its principal-divisor arrows are proved, the torsor/ideal-family coordinate equivalence is proved, the sharp divisorial monoid (effective cone), its group completion, the model `Input`, the object dictionary `d(J) = -delta(J)` and the arrow-level `Hom` interface are proved, and the actual finite/infinite local value kernels with their degree/realification identifications are proved. The single missing capstone on the Frobenioid side is that no `Iut.FrobenioidPresentation` is produced from these data for a number field: the only existing source-facing `FrobenioidPresentation` is the one-finite-place `stageModelFrobenioidPresentation concretePlace`, and `frobenioidPresentation` itself is never applied in `LeanFormal` (grep this session: 0 hits).

The source-object link is worse than the Frobenioid: `SourceOriginalInput.OriginalInput` carries an arbitrary place index `V` and an arbitrary `FPrimeStrip`, with no identification to the places of its own arithmetic field and no link to any Frobenioid. Conversely the Frobenioid side (`Iut.FrobenioidPresentation`, `SourceProposition37Frobenioid`) never sees `OriginalInput`. The Theorem 3.11 assembly therefore takes the whole Frobenioid boundary as a free parameter (`SourceInternalWiring` fields `X Y : Type` and `k2 : K2FrobenioidBoundary`, `SourceInternalWiring.lean:380-391`).

Smallest next statement, fixed in section 7:

```lean
noncomputable def sourceOriginalInputFrobenioidPresentation
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Iut.FrobenioidPresentation
```

i.e. the global Example 3.6 Frobenioid at the arithmetic base field `I.initial.arithmetic.Fmod`, with two small prerequisites (`IsConnected BottomBase`, all arrows epi) recorded in the same section. It does not claim the Ex3.6(iii) natural isomorphism, the Prop3.7(iii)-(iv) prime-strip tuple, or the K2 boundary.

## 2. Paper objects and quantifiers

Local corpus: `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt`. Read this session: lines 6181-6548 (Example 3.6 and Proposition 3.7). Page anchors: Ex3.6 on III p.107, Prop3.7 on III pp.109-111.

### 2.1 IUT III, Example 3.6 (concrete representations of global Frobenioids)

Freeze first: `F_mod` is the base field of the IUTchI Definition 3.1 input, `V` its set of places, and for each `v in V`, `beta_v : F_mod^× -> K_v^× / O_{K_v}^×` is the homomorphism determined by the valuation (archimedean places use the positive-real multiple of the closed unit ball `O^def_{K_v}`).

**(i) Rational-function-torsor version `F⊛_MOD`.**

- Object: `T = (T, {t_v}_{v in V})` where `T` is an `F_mod^×`-torsor and each `t_v` is a trivialization of the contracted product `T_v = Gamma_v x^{F_mod^×} T` obtained by change of structure group along `beta_v` (equivalently a chosen point of the `Gamma_v`-torsor `T_v`).
- Finite-support condition: there exists `t in T` such that `t_v` is the trivialization determined by `t` for all but finitely many `v`.
- Elementary morphism `T_1 -> T_2`: an `F_mod^×`-torsor isomorphism that is integral at every `v`, i.e. carries `t_{1,v}` into the `O^⊿_{K_v}`-orbit of `t_{2,v}`.
- Morphism: a positive integer `n` plus an elementary morphism `(T_1)^{tensor n} -> T_2`; composition is the evident one; tensor powers `T^{tensor n}` exist for `n in Z` as objects.
- Claimed structure: a natural Frobenioid structure ([FrdI] Definition 1.3) whose **base category is the category with precisely one arrow**; the elementary morphisms are exactly the linear morphisms and the integer `n` is the Frobenius degree.
- Natural isomorphism `F⊛_mod -> F⊛_MOD` of Frobenioids, inducing the identity on the rational-function monoid `F_mod^×`.

**(ii) Local-fractional-ideal version `F⊛_mod`.**

- Object: `J = {J_v}_{v in V}` with `J_v` a finitely generated nonzero `O_{K_v}`-submodule of `K_v` for `v in V_non`, a positive real multiple of `O^def_{K_v}` for `v in V_arc`, and `J_v = O_{K_v}` for all but finitely many `v`.
- `f · J` for `f in F_mod^×`; tensor powers `J^{tensor n}` for `n in Z`.
- Elementary morphism `J_1 -> J_2`: an element `f in F_mod^×` which is integral, i.e. `f · J_{1,v} ⊆ J_{2,v}` for every `v in V`.
- Morphism: `n > 0` plus an elementary morphism `(J_1)^{tensor n} -> J_2`.
- Same Frobenioid claim (one-arrow base category, elementary = linear, `n` = Frobenius degree) and a natural isomorphism `F⊛_mod -> F⊛_mod` (line-bundle model), identity on `F_mod^×`.

**(iii) Comparison.** Composing (i) and (ii) gives a natural isomorphism of Frobenioids `F⊛_mod -> F⊛_MOD` inducing the identity on `F_mod^×`; the text notes that the isomorphism is not necessarily determined by that condition, but the induced isomorphism between **perfections (hence realifications)** is completely determined by it.

Two negative guards that a stage-2 statement must not violate:

1. The comparison is a natural isomorphism between two **global** Frobenioid categories. There is no local-to-global section `K_v^×/O_{K_v}^× -> F_mod^×` in the source, and none may be invented.
2. The identity is asserted on the rational-function monoids, not on the divisor/value monoids. The two Frobenioids have different divisor data (arithmetic line bundles vs fractional ideals); a `modMap`/`MODMap` on value carriers is not the paper's map.

### 2.2 IUT III, Proposition 3.7 (global packet-theoretic Frobenioids)

`A` is the packet index of Proposition 3.3; `alpha in A`; `(dagger M⊛_mod)_alpha` and `(dagger M⊛_MOD)_alpha` are the rational-function monoids of the packet; `Psi^log(A,alpha F_v) ⊆ log(A,alpha F_v)` are the Galois invariants of the local monoids for `v in V`.

- **3.7(i)**: for each `alpha in A`, an algorithm constructing `(dagger F⊛_MOD)_alpha` as in Ex3.6(i) from the number field `(dagger M⊛_MOD)_alpha` (image of the composite `(dagger M⊛_mod)_alpha -> (dagger M⊛_mod)_A -> log(AF_V^Q)` of Prop3.3(i),(ii)), plus a natural isomorphism `(dagger F⊛_mod)_alpha -> (dagger F⊛_MOD)_alpha` inducing the tautological isomorphism on rational-function monoids. Realification written `(dagger F⊛R_MOD)_alpha`.
- **3.7(ii)**: for each `alpha in A`, an algorithm constructing `(dagger F⊛_mod)_alpha` as in Ex3.6(ii) from the number field `(dagger M⊛_mod)_alpha = (dagger M⊛_MOD)_alpha` **and the Galois invariants of the local monoids**; each local `J_v` is a subset (a submodule when `v in V_non`) of `I^Q(A,alpha F_v)` whose `Q`-span equals it; natural isomorphisms `(dagger F⊛_mod)_alpha -> (dagger F⊛_mod)_alpha` and `(dagger F⊛_mod)_alpha -> (dagger F⊛_MOD)_alpha` inducing the tautological isomorphisms on rational-function monoids. Realification `(dagger F⊛R_mod)_alpha`.
- **3.7(iii)**: composing the isomorphisms `dagger C⊩_j -> (dagger F⊛R_mod)_j` of IUTchII Cor4.8(iii) with the realifications `(dagger F⊛R_mod)_alpha -> (dagger F⊛R_MOD)_alpha` of (i) gives a functorial algorithm in the log-link of Theta±ellNF-Hodge theaters `ddagger HT -> dagger HT` producing a global realified LGP-Frobenioid `C⊩_LGP(dagger HT)`; together with the data `Psi_FLGP(dagger HT)` of Prop3.4(ii) this gives rise to an **F⊩-prime-strip**

```text
dagger F⊩_LGP = (dagger C⊩_LGP, Prime(dagger C⊩_LGP) ~> V, dagger F⊢_LGP, {dagger rho_LGP,v}_{v in V})
```

  plus a natural isomorphism `dagger F⊩_gau -> dagger F⊩_LGP` of F⊩-prime-strips.
- **3.7(iv)**: the same with `mod` in place of `MOD`, producing `C⊩_lgp(dagger HT)`, `dagger F⊩_lgp = (dagger C⊩_lgp, Prime(dagger C⊩_lgp) ~> V, dagger F⊢_lgp, {dagger rho_lgp,v}_{v in V})`.

Prop3.7 is where the Frobenioid and the prime strip are actually joined: the first component of the F⊩-prime-strip is the global realified Frobenioid `dagger C⊩`, and the remaining components are a bijection `Prime(dagger C⊩) ~> V`, a sub-strip `dagger F⊢`, and restriction isomorphisms `{dagger rho_v}`. Any Lean link that omits `Prime(~> V)`, `dagger F⊢` or `{rho_v}` is not this link.

### 2.3 IUT I companions (quoted from the tree, not re-read in the corpus this session)

`PrimeStripsFrobenioidLinks.lean:15-41` records the source locations used by the existing link layer: IUT I Definition 4.1 and Definition 5.2(i)-(iv) (the prime-strip collections `ddagger F`, `ddagger F⊢`, `ddagger F⊩ = (ddagger C⊩, Prime(ddagger C⊩) ~> V, ddagger F⊢, {ddagger rho_v})`); Example 3.2(iii), 3.3(i),(iii)-(iv) (local Frobenioids `C_v`, `C⊢_v`); Example 3.4 (archimedean MLF-Galois TM-pair); Example 3.5(i) (global realified `C⊩mod`, `Prime(C⊩mod) ~> Vmod`, `rho_v : log⊢mod(p_v) |-> 1/[K_v:(Fmod)_v] * logPhi(p_v)`); Corollary 5.3(ii),(iv) (rigidity of F-prime-strip vs D-prime-strip).

These are the local/global Frobenioids that the Ex3.6 dictionary is supposed to identify. They are not constructed in Lean (see G7).

### 2.4 Quantifier table (paper vs current Lean)

| paper object | paper quantification | current Lean carrier | linked? |
|---|---|---|---|
| `F_mod` | fixed number field of the Definition 3.1 input | `I.initial.arithmetic.Fmod` (`InitialTheta/ArithmeticData.lean:63`) | yes, by projection |
| `V` | set of places of `F_mod` | `OriginalInput` type parameter `V : Type uv` (`SourceOriginalInput.lean:41`) | **no** (G5) |
| `K_v`, `O_{K_v}`, `beta_v` | completion, integer ring, valuation class map | `v.adicCompletion F`, `v.adicCompletionIntegers K`, `completionUnitClass` (`FinitePlaceFractionalIdealUnitQuotient.lean:38`) | donor exists for a general `F`; not instantiated at `Fmod` of an `OriginalInput` |
| `T` | `F_mod^×`-torsor | `GTorsor.regular Fˣ` (`Example36TorsorTheory.lean:193`); a presentation carries `T : GTorsor Fˣ` (`Example36TorsorPresentation.lean:56`) | coordinate level only |
| `t_v` | local trivialization of `T_v` | finite/infinite coordinates of `TorsorPresentation` | coordinate level only |
| `n > 0` | morphism degree | `Hom.degree : Nat` + `Hom.positive_degree` (`Example36GlobalIdealFamily.lean:161-174`) | yes |
| `n in Z` | object tensor power | `GlobalIdealFamily.add`/`neg` (`Example36GlobalIdealFamily.lean:85,99-102`) but no `AddCommGroup` instance; `powerTranslationArrow` takes `n : Nat` (`Example36GlobalIdealFamilyActual.lean:185`) | nonnegative only |
| `f in F_mod^×` | global multiplier | `Hom.multiplier : Fˣ` (`:167`) | yes |
| `f J_1^n ⊆ J_2` | integrality at every `v` | `Hom.finite_incl` / `Hom.infinite_incl` (`:169-173`) via `LocalValueData.localInclusion` | yes (value coordinates) |
| `J`, `J_v` | global fractional ideals | `GlobalIdealFamily` value coordinates: `finite : HeightOneSpectrum ->_0 Z`, `infinite : InfinitePlace -> R` (`Example36GlobalIdealFamily.lean:53-57`) | actual `FractionalIdeal` objects exist only locally (`LocalFractionalIdealUnitQuotient.lean:71`) |
| almost all `v` standard | finite support | `Finsupp` + `GlobalIdealFamily.standard` (`:72`) | yes |
| `alpha in A` | packet index | no Lean carrier in `OriginalInput`; `SourceTheorem311Realization` uses `Choice` (`SourceHodgeTheaterBridge.lean:910-919`) | **no** (G4/G9) |
| `dagger HT` | Theta±ellNF Hodge theater, log-link functorial | `HodgeTheater` / `SourceHodgeTheaterFamily`; `SourceHodgeTheaterSystem` is a separate abstraction | **no** (G9) |
| `Psi_FLGP`, `dagger F⊢`, `Prime(C⊩) ~> V`, `{rho_v}` | Prop3.7(iii)-(iv) data | none (`FPrimeStrip` has only per-place `Pi`, `G`, `Mon`, action, degree) | **no** (G4) |

## 3. Lean interfaces actually present

### 3.1 Source input and Hodge theaters

| declaration | type / fields | location |
|---|---|---|
| `HodgeTheater l V` | `arithmetic : InitialThetaArithmeticData l`, `primeStrip : FPrimeStrip V`, `thetaPacket : FiniteThetaPacket l` | `HodgeTheater/HodgeTheaterCore.lean:31-34` |
| `HodgeTheaterLink S T` | `primeStripEquiv : FPrimeStripEquiv`, `theta_q_eq`, `theta_scale_eq` | `:36-42` |
| `SourceHodgeTheaterFamily l V` | `index`, `theater : index -> HodgeTheater`, `distinct`, `link`, `link_refl/symm/trans`, `permutation`, `permutationLink`, `permutation_naturality` | `HodgeTheater/SourceHodgeTheaterFamily.lean:32-50` |
| `OriginalInput l V` | `initial : SourceDefinition31Data l`, `family : SourceHodgeTheaterFamily l V`, `index_equiv : family.index ≃ Int x Int`, `arithmetic_alignment : forall i, (family.theater i).arithmetic = initial.arithmetic` | `Theorem311/SourceOriginalInput.lean:41-46` |
| `OriginalInput.primeStripAt n m` | `FPrimeStrip.{umon,uv,upi} V := (I.theaterAt n m).primeStrip` | `:788-789` |
| `OriginalInput.dPrimeStripAt`, `monoAnalyticAt`, `geometricAt`, `valueMonoidAt` | projections of the above | `:791-802` |
| `OriginalInput.primeStripLinkAt`, `dPrimeStripLinkAt` | `FPrimeStripEquiv` / `DPrimeStripEquiv` between theaters | `:804-810` |
| `SourceHodgeTheaterSystem l` | independent abstract carrier: `source`, `index`, `theaterCarrier`, `theater`, `qParameter`, `scale`, `link`, `permutation`, naturality fields | `Theorem311/SourceHodgeTheaterBridge.lean:40-65` |
| `SourceTheorem311Realization l Label Choice` | `procession`, `packet`, `vertical`, `evaluation`, `genericFamily`, `labelledCount` | `:910-919` |

Note the split: `SourceHodgeTheaterFamily` (used by `OriginalInput`) and `SourceHodgeTheaterSystem` (used by the bridge) are not related by any declaration. `SourceTheorem311Realization` produces the derived package `Theorem311Source.Input`, not an `OriginalInput`.

### 3.2 Prime strips

| declaration | type / fields | location |
|---|---|---|
| `DPrimeStrip V` | `Pi : V -> Type`, `[Group]`, `G : V -> Type`, `[Group]`, `proj : Pi v ->* G v`, `proj_surjective` | `HodgeTheater/PrimeStripCore.lean:24-30` |
| `DPrimeStrip.geometric v` | `(proj v).ker : Subgroup (Pi v)` | `:38` |
| `DPrimeStripEquiv` | `isoPi`, `isoG`, `compat` | `:61-66` |
| `FPrimeStrip V` | extends `DPrimeStrip V` with `Mon : V -> Type`, `[CommMonoid]`, `action : Pi v ->* MulAut (Mon v)`, `degree : Mon v ->* Multiplicative Real` | `:117-121` |
| `FPrimeStripEquiv` | `isoPi`, `isoG`, `isoMon`, `compatProj`, `compatAction`, `compatDegree` | `:166-177` |

`FPrimeStrip` is a per-place value/action carrier. It contains no global Frobenioid object, no `Prime(C⊩) ~> V` bijection, no sub-strip `dagger F⊢`, and no restriction isomorphisms `{rho_v}`.

### 3.3 Frobenioid side and the frozen consumer

| declaration | type / fields | location |
|---|---|---|
| `Iut.FrobenioidPresentation` | `PreFrobenioidPresentation` (`carrier`, `baseCategory`, `isFSM`, `preFrobenioid`, connected/epi fields) + `axioms : preFrobenioid.FrobenioidAxioms` | `Iut/Foundations/Frobenioid.lean:915-916` |
| `Iut.SourceModelFrobenioid.Carrier.frobenioidPresentation` | `[IsConnected D] -> (forall {X Y} (f : X ⟶ Y), Epi f) -> FrobenioidPresentation` from `Phi : DivisorialMonoidOn D IsFSM` and `data : Input Phi` | `Iut/Foundations/SourceModelFrobenioidPresentation.lean:25-30` |
| `SourceModelBackend.globalDivisorMonoidOn` | `DivisorialMonoidOn BottomBase BottomFSM` | `Example36SourceModelBackend.lean:419-426` |
| `SourceModelBackend.numberFieldSourceModelInput` | `Iut.SourceModelFrobenioid.Input globalDivisorMonoidOn` | `:476-492` |
| `stageModelFrobenioidPresentation` | `FrobenioidPresentation` for **one** finite place `place : NumberField.FinitePlace K` | `Iut/Foundations/SourceFiniteStageModelFrobenioid.lean:418` |
| `SourceProposition37Frobenioid X` | `degree : X ->* Multiplicative Real`, `realification : X -> Real`, `realification_mul`, `degree_realification`, `unit`, `unit_realification`, `effective : X -> Prop`, `effective_proved : forall x, effective x`, `transport`, `transport_degree` | `Theorem311/SourceDependencyChain.lean:995-1008` |
| `K2FrobenioidBoundary R K X Y` | `localFrobenioid`, `globalFrobenioid : SourceProposition37Frobenioid`, `modMap : X -> Y`, `MODMap : Y -> X`, degree/realification/transport equations, `comparison`, `upperSemi` | `Theorem311/SourceK1K2Construction.lean:350-385` |
| `FrobenioidValueKernel X` | same fields as `SourceProposition37Frobenioid` at the IUT-II layer | `IUTII/Frobenioid/PrimeStripsFrobenioidLinks.lean:296-307` |
| `PrimeStripFrobenioidLinkLayer X Y` | `localFrobenioid`, `globalFrobenioid : FrobenioidValueKernel`, `modMap`, `MODMap`, degree/transport compatibility | `:359-374` |
| `sourceProposition37FrobenioidOfValueKernel` | `FrobenioidValueKernel X -> SourceProposition37Frobenioid X` | `Theorem311/SourceK1K2Realization.lean:223-234` |
| `k2FrobenioidBoundaryOfLinkLayer` | `PrimeStripFrobenioidLinkLayer X Y -> ... -> K2FrobenioidBoundary R K X Y` | `:240-270` |

## 4. Donors actually proved (evidence at the pinned HEAD)

All line numbers verified by reading this session. `olean` presence is not a current-build claim; see section 8.

| donor | what it proves | location |
|---|---|---|
| local unit quotient = fractional ideals | `K^× / O^× ≃ (FractionalIdeal R^0 K)^×` for a PID (over a Dedekind fraction field) | `LocalFractionalIdealUnitQuotient.lean:31,58,71` |
| unique integral unit | `aO = bO <-> exists! u : R^×, u*a = b` | `:84-108` |
| generator torsor | `Generators I` nonempty + `generatorChart : R^× ≃ Generators I` | `:111,114,130-150` |
| ideal inclusion criterion | `aO <= bO <-> a/b in O`; also `f*(aO)^n <= bO <-> f a^n / b in O` | `:154-178` |
| composition law on ideals | `(n,f);(m,g) = (nm, g f^m)` for actual fractional ideals | `:182-198` |
| actual finite place | quotient, `beta_v = completionUnitClass`, integrality via the adic valuation | `FinitePlaceFractionalIdealUnitQuotient.lean:30,38,51,67` |
| global ideal family | `GlobalIdealFamily` object, `standard`, `Hom` `(n,f)` with per-place inclusion, `id`, `comp` | `Example36GlobalIdealFamily.lean:53,72,161-174,187,197-209` |
| principal divisor arrows | `principalDivisor`, `principalArrow : J -> J + div f`, `principalArrow_isIso`, composition | `Example36GlobalIdealFamilyActual.lean:47,77,107,129-140` |
| torsor <-> ideal family | coordinate functors both ways and `torsorIdealFamilyEquivalence : CoordinateEquivalence D` | `Example36TorsorEquivalence.lean:341,479,730,774` |
| effective cone sharp/saturated | `EffectiveDivisor`, `effectiveDivisorialAddMonoid` (integral, sharp, saturated) | `Example36SourceModelBackend.lean:68,403-415` |
| group completion | `coneGrothendieckEquiv : GrothendieckAddGroup (EffectiveDivisor F) ≃+ ExplicitDivisor F` | `:381-397` |
| model input | `globalDivisorMonoidOn`, `globalRationalFunctions`, `principalDivisorExplicit`, `globalModelDivisor`, `numberFieldSourceModelInput` | `:419,430,444,471,476` |
| object dictionary | `idealFamilyDivisorClass J = -delta(J)` and `objectOfIdealFamily` | `:498,504` |
| arrow dictionary | `idealFamilyHomToBackendHom`, `torsorArrowToBackendHom` into `Iut.SourceModelFrobenioid.Hom` | `Example36BackendHomInterface.lean:167,257` |
| finite local kernel | `finitePlaceUnitValueKernel : FrobenioidValueKernel (completion units)`; degree = `-nu * log #(O/v)` | `Example36PrimeStripBridge.lean:279,211,265` |
| archimedean kernel | `archimedeanValueGroupKernel : FrobenioidValueKernel (Multiplicative R)`, degree = `-log ||x||` | `:504,483-495` |
| prime strip <-> model divisor | finite/archimedean divisor coordinates and realifications agree with `numberFieldSourceModelInput` | `:660,667,694,706,718,732` |
| actual place components | `NumberFieldPlaceIndex`, `PrimeStripComponent`, `numberFieldPrimeStrip : FPrimeStrip NumberFieldPlaceIndex` | `Example36PrimeStripComponentIdentification.lean:178,242,569,575` |
| single-place global Frobenioid | `stageModelFrobenioidPresentation` (genuine sharp divisor monoid `ULift Nat`, ramification-weighted pullbacks, model `Input`) | `Iut/Foundations/SourceFiniteStageModelFrobenioid.lean:157,419-429` |
| concrete source boundary | `ConcreteSourceFrobenioidBoundary.model : Iut.FrobenioidPresentation` = `concreteStageModel` | `ConcreteSourceFrobenioidBridge.lean:69-91` |
| Hodge theater algebra | `HodgeTheater`, `HodgeTheaterLink` reflexivity/symmetry/transitivity, `SourceHodgeTheaterFamily` link laws | `HodgeTheaterCore.lean:31-82`, `SourceHodgeTheaterFamily.lean:57-140` |
| source-input links | `primeStripLinkAt_compatProj/Action/Degree`, route lemmas, `primeStripLinkAt_isoG_bijective` | `SourceOriginalInput.lean:833,841,851,870,1202-1230` |

## 5. Exact gaps

### G1 (blocking, small): no global Frobenioid from the model data

`frobenioidPresentation` occurs 0 times in `LeanFormal` and is applied only in `Iut/Foundations/SourceFiniteStageModelFrobenioid.lean:423` (one finite place) and the axiom files. There is no `Iut.FrobenioidPresentation` built from `globalDivisorMonoidOn` + `numberFieldSourceModelInput`, even though every `Input` obligation is already proved and only the base-category hypotheses are missing. Consumer: the `Iut.FrobenioidPresentation` consumers of 6.2 and, indirectly, the K2 boundary.

### G2 (small, prerequisite of G1): base-category hypotheses

`BottomBase` (`Example36SourceModelBackend.lean:41`) has a one-object/one-arrow category (`bottomBaseCategory`, `:46`; `BottomFSM`, `:56`; all homs are identities, `bottomBase_hom_eq_id`, `:59`). There is no `CategoryTheory.IsConnected BottomBase` instance and no lemma `Epi f` for its arrows. These two facts are exactly what `frobenioidPresentation` asks for. Mathematically trivial; not yet written.

### G3 (blocking, medium): Ex3.6(iii)/Prop3.7(i),(ii) is only coordinate-level

`Example36TorsorEquivalence.torsorIdealFamilyEquivalence` (`:774`) is an equivalence of two bespoke coordinate categories (`GlobalIdealFamily` with `Hom`, `TorsorPresentation` with `TorsorArrow`). Neither is an `Iut.PreFrobenioid`, and the file states it does not assert a global Frobenioid equivalence (`:47-50`). Therefore the paper's natural isomorphism `F⊛_mod ≅ F⊛_MOD` of Frobenioid categories is not proved; only the object/arrow dictionary that a future functor would use is proved.

### G4 (blocking, medium): the Prop3.7(iii)-(iv) F⊩-prime-strip is not expressible

The paper's output is `(dagger C⊩, Prime(dagger C⊩) ~> V, dagger F⊢, {dagger rho_v})`. `Iut.FrobenioidPresentation` has no `Prime` set and no restriction/`rho_v` data; `FPrimeStrip` has no global Frobenioid component. So the tuple cannot be stated without new definitions. This is the real content of the master record's `actualThetaLinkCarrier`/`sourceObjectIdentification` name; the name currently has 0 occurrences in the tree.

### G5 (blocking, structural): `V` is not the place set of `F_mod`

`OriginalInput` quantifies an arbitrary `V : Type uv` (`:41`) and `index_equiv : family.index ≃ Int x Int` (`:44`), with `arithmetic_alignment` only on `arithmetic` (`:45-46`). Nothing relates `v : V` to a place of `I.initial.arithmetic.Fmod`, so no `K_v`, `O_v`, `beta_v` can be attached to `I.primeStripAt`. The concrete bridge also proves that the singleton family over the concrete carrier cannot be an `OriginalInput` (`Example36SourceObjectBridge.lean:154-161, 204-215`). A place realization must be a new structure, not a silently added field of `OriginalInput`.

### G6 (consumer defect): the K2 record is a reduced shape, not the paper's comparison

Three independent issues:

1. `effective_proved : forall x, effective x` (`SourceDependencyChain.lean:1005`) forces totality. It cannot express the sharp effective cone that already exists in `Example36SourceModelBackend.effectiveDivisorialAddMonoid` (`:403`); any inhabitant on a group carrier must set `effective := True`.
2. `modMap : X -> Y` and `MODMap : Y -> X` (`SourceK1K2Construction.lean:357-358`) read as local/global maps. The paper's map is a natural isomorphism between two **global** Frobenioids, and `Example36PrimeStripBridge.lean:77-79` records that no local-to-global section exists. An inhabitant of `MODMap` therefore cannot be source-faithful as a section; the paper's `mod`/`MOD` comparison needs a different type.
3. There is no bridge from `Iut.FrobenioidPresentation` to `SourceProposition37Frobenioid` (different data: axioms vs a bare `CommMonoid` record).

### G7 (card CAT, out of this node): the categorical local Frobenioids

`C_v`, `C⊢_v`, `C⊩mod` (IUT I Examples 3.2/3.3/3.5) are not constructed. `PrimeStripFrobenioidCards` proves the reduced negative forms `frobenioidLinkUnitStrip_no_divisorialAddMonoid` (`:154`) and `frobenioidLinkIntegralStrip_not_sharp` (`:166`): the current prime-strip value carriers are groups, so no sharp divisorial monoid can be additively equivalent to them. This blocks building `C_v` **on the group-valued prime-strip carrier**; it does not block the ideal-family/model route of G1, whose sharp cone is a new carrier (`EffectiveDivisor`).

### G8 (card, recorded in tree): geometric pi_1 of the punctured curve

The concrete number-field prime strip has identity projection, hence trivial geometric kernel (`Example36PrimeStripComponentIdentification.lean:86-103`, `numberFieldPrimeStrip_not_hasNontrivialGeometricComponentAt`, `:1081`; `SourceCurveGeometricComponent`, `:1047`). The affine Tate strips give actual nontrivial finite Tate kernels (`:105-159`) but not the tempered/etale pi_1 of the once-punctured elliptic curve. Consequence for this node: the `D`-side of any `dagger F⊩` built from the current strips has trivial geometric content.

### G9 (card, out of this node): the Hodge-theater/Theta-link carrier

`SourceHodgeTheaterSystem` (`SourceHodgeTheaterBridge.lean:40-65`) is an abstract q/scale/link carrier and is not connected to `HodgeTheater`/`SourceHodgeTheaterFamily`; `SourceTheorem311Realization` (`:910`) does not produce an `OriginalInput`. No `actualThetaLinkCarrier` exists (0 occurrences in the tree). Prop3.7(iii)-(iv) functoriality in the log-link of Theta±ellNF-Hodge theaters is therefore absent.

## 6. Actual consumer trace

### 6.1 Where Frobenioid data enters Theorem 3.11

```text
SourceTheorem311Assembly.SourceTheorem311Layers.canonical  (:70)
  -> SourceInternalWiring.canonical                        (SourceInternalWiring.lean:405)
     -> SourceInternalWiring.k2 : K2FrobenioidBoundary       (:391)
        -> localFrobenioid/globalFrobenioid :
           SourceProposition37Frobenioid                     (SourceK1K2Construction.lean:355-356)
           -> SourceDependencyChain.SourceProposition37Frobenioid (:995)
```

`SourceInternalWiring` quantifies `X Y : Type` with `[CommMonoid X] [CommMonoid Y]` as free parameters (`:380-391`); `K2FrobenioidBoundary` is an explicit hypothesis, never derived from `I`. The assembly is therefore conditional on a Frobenioid boundary that has no link to the source input. That hypothesis is the consumer this node must eventually fill.

### 6.2 Where `Iut.FrobenioidPresentation` is consumed today

Only by the concrete theta/history bridges: `ConcreteSourceEtaleThetaBridge.sourceModel : Iut.FrobenioidPresentation := ConcreteSourceFrobenioidBridge.concreteStageModel` (`:44`), stored as `AlgebraicFiniteThetaLevel.sourceFrobenioid` with `sourceFrobenioid_eq : sourceFrobenioid = sourceModel` (`:86-87`); and `ConcreteSourceHistoryLinkBridge.ConcreteSourceHistoryLinkOutput.sourceModel` (`:234`), again `= ConcreteSourceEtaleThetaBridge.sourceModel`. Both are `abbrev`/`rfl`-tied to the single-place `concreteStageModel` (`ConcreteSourceFrobenioidBridge.lean:47`). No consumer takes a Frobenioid derived from `OriginalInput` or from a general number field.

### 6.3 Where the prime strip is consumed today

The prime strip is load-bearing for the Cor3.12 hull: `SourceImageHull.lean:82-83` (`ValueMonoidAt := (I.primeStripAt n m).Mon v`) and `:100-101` (`logDegreeAt := Multiplicative.toAdd ((I.primeStripAt n m).degree v x)`), with multiplicativity/additivity lemmas at `:103-119`; also `SourcePacketDegreeLedger.lean:367-411`. So the prime strip's `Mon`/`degree` data matters for the upper layers, but no Frobenioid enters that path.

### 6.4 Consequence

There is no existing declaration that consumes a link between `OriginalInput.primeStripAt` and a Frobenioid. The gap is real and load-bearing exactly at `K2FrobenioidBoundary`; the prime-strip path and the Frobenioid path currently meet only in the frozen consumer record.

## 7. Smallest stage-2 statement

### 7.1 Why the master-record candidate is not the smallest

The master skeleton proposes `SourceOriginalInput`-level `actualThetaLinkCarrier`/`sourceObjectIdentification`. No such type exists (0 occurrences). Its intended content is the Prop3.7(iii)-(iv) F⊩ tuple `(dagger C⊩, Prime(dagger C⊩) ~> V, dagger F⊢, {dagger rho_v})` plus log-link functoriality, which needs at least: a `Prime` notion for the Frobenioid, a sub-strip `dagger F⊢`, restriction isomorphisms `rho_v`, and the Hodge-theater/log-link carrier (G9). That is several new definitions plus G4/G5/G9, not a smallest statement. It is recorded as child node G1-c below.

### 7.2 The statement

Prerequisites (same file, same commit):

```lean
namespace LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend

/-- The one-object/one-arrow base category of Example 3.6 is connected. -/
instance bottomBase_isConnected :
    CategoryTheory.IsConnected (SourceModelBackend.BottomBase)

/-- Every arrow of the one-arrow base category is an epimorphism. -/
theorem bottomBase_arrow_epi
    {X Y : SourceModelBackend.BottomBase} (f : X ⟶ Y) : Epi f

/-- Frobenioids I, Theorem 5.2(ii), at the actual place data of `F`; the
divisor monoid is the effective cone of `F` and the rational functions are
`Additive F^×` (Example 3.6, (ii)). -/
noncomputable def numberFieldFrobenioidPresentation
    (F : Type u) [Field F] [NumberField F] :
    Iut.FrobenioidPresentation := by
  exact Iut.SourceModelFrobenioid.Carrier.frobenioidPresentation
    (D := BottomBase) (IsFSM := BottomFSM)
    (Phi := globalDivisorMonoidOn (F := F))
    (data := numberFieldSourceModelInput (F := F))
    (fun {X Y} f => bottomBase_arrow_epi f)

end LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend

namespace LeanFormal.IUT.Theorem311Source

/-- The global Frobenioid of IUT III, Example 3.6, (ii) attached to the
arithmetic base field `F_mod` of a Theorem 3.11 input. -/
noncomputable def sourceOriginalInputFrobenioidPresentation
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Iut.FrobenioidPresentation :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend.numberFieldFrobenioidPresentation
    (F := I.initial.arithmetic.Fmod)

end LeanFormal.IUT.Theorem311Source
```

The designated **smallest stage-2 statement** is the last declaration. Its exact type is

```lean
OriginalInput.{ua, uv, upi, umon, ui} l V -> Iut.FrobenioidPresentation
```

with `l : PrimeGeFive` and `V : Type uv` implicit as in `SourceOriginalInput.lean:41-51`. The two preceding declarations are its proof obligations; they are small enough to live in the same tmp file and to be discharged before the corollary.

### 7.3 What it does and does not claim

Claims: a genuine `Iut.FrobenioidPresentation` for the arithmetic field `F_mod` of any Theorem 3.11 input, built from the already-proved sharp effective cone, its group completion, the principal-divisor map, and the connected/one-arrow base category. This is the Ex3.6(ii) Frobenioid at the actual place data, via the model-type theorem.

Does not claim: the Ex3.6(i) arithmetic-line-bundle Frobenioid `F⊛_MOD`; the Ex3.6(iii)/Prop3.7 natural isomorphism (G3); the Prop3.7(iii)-(iv) F⊩-prime-strip tuple (G4); any identification of `I.primeStripAt` with the places of `F_mod` (G5); any inhabitant of `SourceProposition37Frobenioid` or `K2FrobenioidBoundary` (G6); the categorical local Frobenioids (G7); the geometric pi_1 (G8); the Theta-link carrier (G9).

### 7.4 Why this is the smallest useful statement

- Every later comparison needs an actual Frobenioid object to compare against. The tree has one only for a single finite place; the model `Input` for a general number field is complete but never packaged.
- The remaining side conditions are exactly G2 (`IsConnected`, `Epi`), both trivial for the one-arrow category; all `Input` and `DivisorialAddMonoid` obligations are already proved.
- It adds no assumption, changes no existing definition, and is a construction rather than a `sorry` card. It is a `def`, so it can be written at stage 2 without a named sorry.
- It uses only `I.initial.arithmetic.Fmod`; it is therefore compatible with every `OriginalInput` and does not pre-empt G5.

### 7.5 Rejected alternatives

1. `PrimeStripFrobenioidLinkLayer X Y` instance from source data: rejected for now. It would require `MODMap : Y -> X`, which the tree itself documents as having no source counterpart (`Example36PrimeStripBridge.lean:77-79`); the paper's comparison is global-global. This is G6, not a small statement.
2. `FrobenioidValueKernel` on each `FPrimeStrip.Mon v` fiber: rejected. It is definable (`degree` is already a field; `realification := toAdd ∘ degree`; `transport := id`) but `effective := True` is vacuous, and the consumer record's `effective_proved` forces totality anyway. It would manufacture a source-effective cone that the source does not give.
3. Adding `placeEquiv`/local-field fields to `OriginalInput`: rejected. It changes the input contract (SHEAF section 2), and `Example36SourceObjectBridge.no_originalInput_of_all_theaters_concrete` (`:204`) shows concrete-carrier inputs cannot exist. It must be a separate realization structure (child node G1-a).
4. `actualThetaLinkCarrier` on `SourceOriginalInput` (master record): rejected as the smallest, see 7.1. Kept as child node G1-c.

### 7.6 Child nodes spawned by this stage-1 pass

| child | stage | content | blocked by |
|---|---|---|---|
| G1-a place realization | 1 open | `SourcePlaceRealization I`: `V ≃ (HeightOneSpectrum (O Fmod) ⊕ InfinitePlace Fmod)` plus identification of `primeStripAt` fibers with the actual local value monoids, and `beta_v` compatibility | needs G2 only for typing; the identification is the real work |
| G1-b K2 bridge | 1 open | `Iut.FrobenioidPresentation -> SourceProposition37Frobenioid` (or a corrected replacement record that keeps the sharp cone) | G6 |
| G1-c F⊩-prime-strip | 1 open | `Prime(C⊩) ~> V`, `dagger F⊢`, `{rho_v}`, and the Prop3.7(iii)-(iv) tuple | G4, G5, G9 |
| G1-d categorical Frobenioids | offline | `C_v`, `C⊢_v`, `C⊩mod`; card CAT | G7, G8 |

## 8. Status ledger and evidence versions

| item | status |
|---|---|
| `statement_compiles` | not run for the new declarations (no Lean written) |
| `proof_body_checked` | not applicable (no proof body written) |
| `kernel_closed` | not applicable |
| `target_accepted` | no; `locked_targets` unchanged |
| production edits | none |
| Lean build | not run; no `lake` invocation in this package |
| donor oleans | present for `SourceOriginalInput` (2026-10-16T18:19), `SourceHodgeTheaterBridge` (18:22), `SourceK1K2Construction` (18:23), `PrimeStripsFrobenioidLinks` (10-16T08:52), `Example36SourceModelBackend` (10-19T02:06), `Example36PrimeStripComponentIdentification` (10-20T03:37), `ConcreteSourceFrobenioidBridge` (10-16T18:35); presence is not a current-build claim |
| dirty tree caveat | `ConcreteSourceFrobenioidBridge.lean`, `SourceK1K2Construction.lean` and many other files are git-modified at this HEAD; only the read interfaces above are pinned by the SHA table |

Evidence file versions read this session (SHA256):

| file | SHA256 |
|---|---|
| `SourceOriginalInput.lean` | `11C288D385682760B56890B24C57F1738A771DC6A75E2543EFFD67D9FFAFA795` |
| `SourceHodgeTheaterBridge.lean` | `DDACDA6560CEE45712A134F96585BB001B8B519745FB4291CEC602A5D6F366BE` |
| `SourceDependencyChain.lean` | `95811DB6377A9A69CF94824A8FE5BA76EF69AD733BBFC5A4D93ED29E3FBF14D2` |
| `SourceK1K2Construction.lean` | `05DA83BC1AB91D9D3B01CE76882EE967C653DD4EC5ED91ADF5736DF2429A2DC3` |
| `SourceK1K2Realization.lean` | `0F8ACA41D5133FC13D017068D4A4F5B76F6C56B004FBA72CCFD6E0991A782C95` |
| `SourceInternalWiring.lean` | `DA6A52B798EF69050D4AB389BCB3C04AF4AA881507A1BEFCD7E32AFC8C03C3BC` |
| `SourceTheorem311Assembly.lean` | `49998EDA25022BCDE0B25F5732B719B20084FECC06EAA57CF944F2DB2BB5EE04` |
| `HodgeTheaterCore.lean` | `60DE5CA3F1E0BAEDDB920782055E3CF58DE294236950C8B673FBE9BAC6B1FDA9` |
| `PrimeStripCore.lean` | `B67C2ABFC38C6317377B89F484B6F772631E99D73026A23D8AE2C8E6E14D58DA` |
| `SourceHodgeTheaterFamily.lean` | `753FB10628100FB2BA72DF71873C33070FCC19D9A6E76117D1BDCA1F49F41C05` |
| `PrimeStripsFrobenioidLinks.lean` | `7899B1856EEDF3DB24FF127C121BA5CA12E17787E416EC6AD61862747F099891` |
| `Example36SourceModelBackend.lean` | `C602CCEB03D1CE299DD9C040768EDCB6F347F90D1A0038137A7B289A1400E365` |
| `Example36TorsorEquivalence.lean` | `2EC484C70405D9C3E093A7F31F2D84FC47764A7A209E97811F4D8D4B412CC62F` |
| `Example36PrimeStripBridge.lean` | `71C39CE52850E28C192C9D608D036A4962876758173D60CAD36BEA03B8F4D571` |
| `Example36PrimeStripComponentIdentification.lean` | `FFD785BCFEB048C020A312773FA87DF8D80B310C6180935DA2E0F597198B12F5` |
| `ConcreteSourceFrobenioidBridge.lean` | `9434C08B2E25AA68399E30588673F4572E7937540BA00A2DD4AA9B9B8AC97BD0` |
| `LocalFractionalIdealUnitQuotient.lean` | `459DDAD57E8559DF182620A03122D2E3CAF112A532FE3AD0969ED0C77D91DE22` |
| `ConcreteSourceEtaleThetaBridge.lean` | `FCA9A7218E3A10D0B552A249D6C850A880F787662740522296929A9131DF4D9D` |
| `ConcreteSourceHistoryLinkBridge.lean` | `037DDC3ECA0CF23FDFFA67E60D75A6E8A3791941C08F6120F94C8ACE6AEC3347` |
| `SourceModelFrobenioidPresentation.lean` | `DEC191E9BFEA356529070009E0D56D5042213773B634B9EEEDC3D9EA671C6E94` |
| `SourceFiniteStageModelFrobenioid.lean` | `220FD44BF58FEF572EA30FFD483560CD9D4406962D8EAA59006446830EC5220B` |
| `Frobenioid.lean` | `B6B8F4E1F1712CA711CE62584D036DAA715E0B86A289F0599E03F7D8F80C2279` |

## 9. Next action (one)

Assign one owner to write `tmp/sheaf/n8/Group1Statement.lean` containing exactly: `SourceModelBackend.bottomBase_isConnected`, `SourceModelBackend.bottomBase_arrow_epi`, `SourceModelBackend.numberFieldFrobenioidPresentation`, and `Theorem311Source.sourceOriginalInputFrobenioidPresentation` as typed in 7.2; compile it with `lake env lean tmp/sheaf/n8/Group1Statement.lean` and record the elaborated type of the last declaration plus `statement_compiles`. Do not edit `SourceModelBackend`, `SourceOriginalInput`, `SourceTheorem311Assembly`, or any consumer.

## 10. Delivery

- Path: `D:/lean/tmp/sheaf/n8/group1-STAGE1.md`.
- Body: the bytes of this file before the final section heading (the body ends with the blank line immediately before it).
- Body SHA256: `E4DE80B7E888949C72C5772BADBDC62DD0DD80652EC02EFA4D747BECC1A017F7`.
- Whole-file SHA256: reported in the parent delivery message (it cannot be written here without changing the file).
- This record is stage 1 only: it freezes objects, quantifiers, donors, gaps and one next statement. It is not a completion claim for `n8-group1-source-objects`.
