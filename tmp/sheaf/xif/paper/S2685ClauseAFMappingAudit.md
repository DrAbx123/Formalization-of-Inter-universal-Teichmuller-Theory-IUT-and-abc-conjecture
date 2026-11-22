# S2685 — ClauseA–F mapping audit for `SourceNativeInitialThetaData`

Date: 2026-11-06 (Asia/Shanghai). Read-only audit. **No compilation was run.**
Evidence = sources, existing `.olean` timestamps/sizes, existing `.out` axiom logs.
No source file, ledger, or STATE was modified; this report is the only new file.

## 0. Verdict (up front)

1. **The current D9 false target does not block clauseF, and clauseF does not
   consume it.** `SourceClauseF` has five fields and none of them mentions
   `S2671`, `S1881`, `S2667`, `S2619ActionGroupoidData`, `IsStack`,
   `IsPrestack`, a sheaf/descent predicate, `S1987D5LargeImageFive`, or an
   arithmetic-compatibility slot. A repo-wide grep of
   `SourceDefinition31Quantifiers.lean` (which defines all six clauses and T)
   for `S2601|S1987|S2587|S2622|S2677|S2555|S1881|S2671|S2619|IsStack|IsPrestack|ArithmeticCuspOriginCompatibility|D9CompatibilitySupply`
   returns **0 matches**; same for `SourceClauseConstructors.lean`,
   `SourceTorsionRankOneQuotient.lean`, `SourceSignQuotientConstruction.lean`.
2. **Structurally, clauseF is the cheapest clause.** Given clauseC's
   `D.k_torsion_basis` and `S.epsilon : Iut.OrbicurveBoundaryCusp S.cK`
   (a field of the sign-quotient datum `S`), clauseF is constructible with
   `SourceClauseConstructors.ofCanonicalBoundaryData` using the constant
   origin map at `S.epsilon`; the cuspidal decomposition is constructed by
   `S2555CuspidalDecomposition` (no assumption). No D9 target is used.
3. **What actually blocks T is not D9 and not clauseF**: it is (i) the missing
   geometric core `S : SourceSignQuotientData A` and (ii) clauses A–E, which
   have no actual inhabitants for arbitrary `A`. Over the concrete Gaussian
   root (`S1280Arithmetic`, where K = F) clauseC is moreover *impossible*
   (`S1519_nativeThetaActual_impossible`), so T is empty over that root — a
   second, root-specific blocker unrelated to D9. D5–D8 artifacts live in the
   *other* (old `SourceDefinition31Data`) framework and/or in specific models;
   they do **not** fill the native clauses (consistent with STATE 4213 "D5–D8
   do not fill T").
4. **D9 is still relevant to T only at the object level**: `S` contains
   `cF, xK, cK` and the sign-quotient witness, which overlap the D9 orbicurve
   slot (`S1881D9OrbicurveSlot`). The D9 *open construction* is therefore part
   of the wider `S` construction, but the D9 *false stack proposition*
   (`S2671Fiber_not_isPrestack/not_isStack`) is only a refutation of one
   proposed construction route (bare action-groupoid fiber on the full étale
   site). It neither inhabits nor refutes a clauseF field.

## 1. The exact object T

`SourceDefinition31Quantifiers.lean:1681–1689`:

```lean
structure SourceNativeInitialThetaData (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData.{u} l
  tuple      : SourceInitialThetaTuple arithmetic
  clauseA    : SourceClauseA arithmetic tuple.source
  clauseB    : SourceClauseB arithmetic tuple.source clauseA
  clauseC    : SourceClauseC arithmetic tuple.source clauseA clauseB
  clauseD    : SourceClauseD arithmetic tuple.source clauseA clauseB clauseC
  clauseE    : SourceClauseE arithmetic tuple.source clauseA clauseB clauseC clauseD
  clauseF    : SourceClauseF arithmetic tuple.source clauseA clauseB clauseC clauseD clauseE
```

`tuple` (`:1612–1628`) is `fbar : SourceFbarExtension A`, `source :
SourceSignQuotientData A`, then the printed entries `xF, cK, V, V_mod_bad,
epsilon` together with the equalities `xF = source.xF`, `source.cK = cK`,
`V = source.V`, `V_mod_bad = source.V_mod_bad`, and the transported
`epsilon` equality. Thus `T` is *not only* the six clauses: `tuple.source`
carries the geometric sign-quotient package (see §3).

Spec projections: `:1695–1700`. Dependent existential:
`:1708–1718` (`∃ clauseA..clauseF, clauseF = clauseF`). Existence:
`:1726–1729`. Packaged ↔ existence: `:1746–1763`. Gate:
`:1772–1775` `SourceNativeArithmeticToSourceGate l := ∀ A, ∃ T, T.arithmetic = A`.

## 2. Clause-by-clause field inventory (exact types)

### SourceClauseA — `:889–902` (section header: "Clause (a): field, curve, and solvable extension")

| field | type |
|---|---|
| `stable_reduction_nonarchimedean` | `∀ p : NumberField.FinitePlace A.F, A.curve.HasStableReductionAt p` |
| `field_of_moduli` | `SourceFieldOfModuli A` = `{jModuli : A.Fmod // algebraMap A.Fmod A.F jModuli = A.curve.jInvariant}` |
| `maximal_solvable_extension` | `IntermediateField A.Fmod A.F` |
| `maximal_solvable_property` | `isFiniteSolvableGaloisSubextension maximal_solvable_extension` = `FiniteDimensional ∧ IsGalois ∧ IsSolvable` |
| `maximal_solvable_contains` | `∀ E : IntermediateField A.Fmod A.F, isFiniteSolvableGaloisSubextension E → E ≤ maximal_solvable_extension` |

### SourceClauseB — `:959–975` ("bad places and actual Tate comparisons")

| field | type |
|---|---|
| `multiplicative_over_bad` | `∀ p : NumberField.FinitePlace A.F, comap (k := A.Fmod) p ∈ S.V_mod_bad → A.curve.HasMultiplicativeReductionAt p` |
| `q_comparison` | `∀ (p) (hp : comap p ∈ S.V_mod_bad), Nonempty (SourceTateComparisonWitness A p)` |
| `residue_characteristic_prime_to_l` | `∀ (p) (hp), Nat.Coprime l.value (NumberFieldFinitePlace.residueCharacteristic (comap p))` |

`SourceTateComparisonWitness` (`:952–957`): `parameter : FinitePlaceQCandidate p`,
`comparison : TateCurveComparison A.curve p parameter`, `order_coprime : Nat.Coprime parameter.order l.value`.

### SourceClauseC — `:1007–1033` ("torsion representation and kernel field")

| field | type |
|---|---|
| `torsion23_rational` | `PuncturedEllipticCurve.Torsion23Rational A.curve` |
| `torsion_basis` | `(Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] A.curve.LTorsion l` (F-side) |
| `representation` | `SourceAbsoluteGalois A →* Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)` |
| `representation_eq_canonical` | `representation = A.curve.galoisLTorsionMatrixRepresentation l torsion_basis` |
| `image_contains_SL2` | `Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤ representation.range` |
| `kernel_field_identification` | `A.K ≃ₐ[A.F] A.curve.galoisLTorsionKernelField l torsion_basis` |
| `kernel_field_identification_range` | `Set.range (fun x : A.K => (kernel_field_identification x : AlgebraicClosure A.F)) = (kernel field : Set (AlgebraicClosure A.F))` |

Derived K-side basis: `k_torsion_basis : (Fin 2 → ZMod l.value) ≃ₗ (A.curve.baseChange A.K).LTorsion l`
via `k_to_f_torsion_transport` (`:1041–1058`).

### SourceClauseD — `:1106–1144` ("actual K orbicurves, covers, and fundamental groups")

| field | type |
|---|---|
| `k_signAction` | `Iut.OrbicurveSignAction S.xK` |
| `k_quotient` | `Iut.OrbicurveSignInvariantMorphism k_signAction S.cK` |
| `k_quotientWitness` | `Iut.OrbicurveSignQuotientWitness k_signAction k_quotient` |
| `k_quotientExtension` | `SourceOrbicurveMorphismScalarExtension S.xKExtension S.cKExtension S.quotient.map` |
| `k_quotient_map_eq_extension` | `k_quotient.map = Hom.cast S.xK_eq_extension.symm S.cK_eq_extension.symm k_quotientExtension.result` |
| `k_l_torsion_cover` | `SourceOrbicurveFiniteEtaleCover S.xK S.cK` |
| `k_l_torsion_cover_map_eq_quotient` | `k_l_torsion_cover.map = k_quotient.map` |
| `x_groups` | `SourceOrbicurveGroupData S.xK (Iut.AbsoluteGaloisProfinite A.K)` |
| `c_groups` | `SourceOrbicurveGroupData S.cK (Iut.AbsoluteGaloisProfinite A.K)` |
| `group_inclusion` | `Iut.ProfiniteFundamentalGroupInclusion` (x/c geometric, arithmetic, over `G_K`) |
| `x_to_F_groups` | `Iut.ProfiniteFundamentalExactSequenceEmbedding` (K-side x → `S.xFGroups` over `G_F`) |
| `c_to_F_groups` | same for c → `S.cFGroups` |

`SourceOrbicurveFiniteEtaleCover` (`:539–543`): `map : source.Hom target`,
`finiteEtale : Iut.EtaleStackFiniteEtaleMorphism map`.
`SourceOrbicurveGroupData` (`:527–531`): `groups : OrbicurveFundamentalGroupData X G`,
whose exact sequence is `profiniteKernelExactSequence projection` (`:51–55`).

### SourceClauseE — `:1432–1452` ("the literal selected subset and local diagrams")

| field | type |
|---|---|
| `selected_eq_V` | `S.V = S.V_section.selected` |
| `selected_equiv` | `NumberFieldPlace A.Fmod ≃ {v : NumberFieldPlace A.K // v ∈ S.V}` |
| `finite_local` | `∀ (v : {v // v ∈ S.V}) (hv : v.1.IsFinite), SourceFiniteLocalSource A S C B D E (selectedFinitePlace hv)` |
| `infinite_local` | `∀ (v) (hv : v.1.IsInfinite), SourceInfiniteLocalSource A S C B D E (selectedInfinitePlace hv)` |

`SourceFiniteLocalSource` (`:1212–1270`) has 12 data fields: `localCurve` +
`local_curve_eq_actual`, `xExtension`, `cExtension`, `signAction`,
`quotientMapExtension`, `quotient`, `quotient_map_eq_extension`, `quotientWitness`,
`xGroups`, `cGroups`, `local_group_inclusion`, `xGlobalEmbedding`,
`cGlobalEmbedding`, `galois_embedding_agreement` (15 total). The infinite version
is `:1325–1379` with the same shape.

### SourceClauseF — `:1543–1561` ("cusp with a source boundary and canonical sign")

| field | type |
|---|---|
| `boundary_origin` | `TorsionQuotientBoundaryOrigin l A S.cK` |
| `quotient_basis_eq_k_torsion_basis` | `boundary_origin.rank_one_quotient.torsion_basis = D.k_torsion_basis` |
| `boundary_cusp_eq_epsilon` | `boundary_origin.cusp = S.epsilon` |
| `cusp_decomposition` | `Iut.OrbicurveCuspidalDecompositionData E.c_groups.groups` |
| `cusp_decomposition_cusp_eq_origin` | `cusp_decomposition.cusp = boundary_origin.cusp` |

`TorsionQuotientBoundaryOrigin` (`SourceTorsionRankOneQuotient.lean:115–127`):

```lean
structure TorsionQuotientBoundaryOrigin (l) (A) (X : HyperbolicOrbicurve A.K) where
  rank_one_quotient : TorsionRankOneQuotientData l (A.curve.baseChange A.K)
  originMap : {q : rank_one_quotient.Quotient // q ≠ 0} → Iut.OrbicurveBoundaryCusp X
  cusp : Iut.OrbicurveBoundaryCusp X
  originMap_distinguishedClass : originMap ⟨distinguishedClass, nonzero⟩ = cusp
```

`TorsionRankOneQuotientData` (`:30–34`) has exactly one field
`torsion_basis : (Fin 2 → ZMod l.value) ≃ₗ X.LTorsion l`.

`OrbicurveCuspidalDecompositionData` (`SourceDefinition31Quantifiers.lean:59–69`):
`cusp : OrbicurveBoundaryCusp X`, `decompositionSubgroup : ClosedSubgroup
groups.arithmetic.group`, `decompositionProjection_surjective : Surjective
(profiniteClosedSubgroupRestriction ...)`.

## 3. Paper mapping — important regrouping

Paper: `papers/motizuki_corpus/text/Inter-universal Teichmuller Theory I.txt`,
Definition 3.1, lines 3123–3295.

The native clause letters are **not** the paper clause letters field-for-field:

- **Paper (a)** (F with √−1, `Fbar`, G_F; lines 3127–3130) is **not** in
  clauseA. `√−1` lives in `InitialThetaArithmeticData` (`tower.sqrtNegOne`,
  `ArithmeticData.lean:26–36, 62–81`) and `Fbar` is `tuple.fbar :
  SourceFbarExtension A`.
- **Native clauseA** contains paper **(b)** data: stable reduction over all
  nonarchimedean places (lines 3131–3133), field of moduli `F_mod` (3137–3138),
  maximal solvable `F_sol` (3138–3139). The section header "Clause (a)" is the
  project's internal letter, not the paper's (a).
- **Native clauseB** contains the bad-set half of paper (b) (3139–3157:
  `V^bad_mod` nonempty, odd residue characteristic, multiplicative reduction)
  plus the coprimality half of paper (c) (3180–3184: l prime to bad residue
  characteristics and to q-parameter orders).
- **Native clauseC** contains paper (c) main content (l-torsion image ⊇ SL₂,
  K = kernel field; 3176–3180) **plus** the 2·3-torsion rationality from the end
  of paper (b) (3174–3175).
- **Native clauseD** = paper (d) (C_K = C_F ×_F K, X_K, cartesian diagrams,
  open group inclusions; 3185–3215). The existence/typing of the ambient
  `xK, cK` already lives in `tuple.source` (`S.xK, S.cK, S.xKExtension,
  S.cKExtension, S.xKType, S.cKType`).
- **Native clauseE** = paper (e) (V a section of V(K) ↠ V_mod; local models and
  group inclusions; 3216–3272). `selected_eq_V`/`selected_equiv` are copied
  from `S`; the per-place local sources are genuine new data.
- **Native clauseF** = the **first half** of paper (f) (ε is a cusp of C_K from
  a nonzero quotient element; 3273–3279). The paper's remaining (f) conditions
  — "if v ∈ V^bad then ε_v is the cusp arising from the canonical generator ±1"
  and the derived orbicurves (3277–3295) — are **not encoded**; the former is
  the parked card `IUT-I.definition-3.1-D9-cusp-local-generator`
  (`coord/reports/S1887-d9-cusp-actual.md:162–164`).

Also note: paper (b)'s `C_F = [X_F/{±1}]`, the F-side/X-side fundamental
groups, `V^bad_mod`, `V_mod_bijection`, and the K-core `xK/cK` are carried by
`tuple.source : SourceSignQuotientData` (`SourceDefinition31Quantifiers.lean:578–631`),
**not** by clauseA–F. So a paper-faithful T needs much more than the six clauses;
conversely the six clauses are not a transcription of paper (a)–(f) one-to-one.

## 4. Dn mapping (project work-plan numbering)

The D-numbering is the `Definition31D0D11Aligned.lean` ledger numbering
(D0 `:39`, D1 `:112`, D2 `:173`, D3 `:294`, D4 `:408`, D5 `:561`,
D6 `:706`, D7 `:921`, D8 `:1095`, D9 `:1238`, D10 `:1284`, D11 `:1398`),
as used by the 2026-11-06 STATE/ledger entries (e.g. STATE 4026, 4058, 4066,
4072, 4155, 4204). It is a *plan* numbering, not a bijection onto clause letters.

| Dn | ledger stage | native/framework correspondence | actual status (2026-11-06) |
|---|---|---|---|
| D0 | kernel + arithmetic root | `T.arithmetic` | `InitialThetaArithmeticData` is input; no construction from nothing |
| D1 | prime data closed | `l : PrimeGeFive` | arithmetic, `l` is a parameter |
| D2 | arithmetic root output / Def 3.1(a) | `T.arithmetic` + native `clauseA` (partial) | `Definition31D2Root.ofArithmetic` is canonical only for tower/curve/√−1/degree; clauseA fields are **missing** |
| D3 | bad places + selected-place carrier | `S.V_mod_bad, S.V, S.V_mod_bijection` + `clauseB` side | place half unconditional (`sourcePlaceSelectionNonempty`, `SourceDefinition31SignQuotientSupplyReduction.lean:217–228`); bad-reduction content missing |
| D4 | stable/multiplicative reduction + local q | native `clauseB` | cards/conditional only (`D4ReductionSupply`); Tate-q analytic half still gap (STATE 4155–4200) |
| D5 | torsion, representation, large image | native `clauseC` | actual artifact `S2601_d5LargeImage` is **model-specific large-image**, not clauseC; rank-two basis card unproved |
| D6 | orbicurves, covers, exact sequences | native `clauseD` (+ `S.xK/cK`) | `S2587/S2622` model-specific cover iso, not clauseD |
| D7 | selected places, local groups, section | native `clauseE` | `S2677D7SectionConstruction` builds old `SourceSectionClause`, not clauseE; rich per-place `Pi_Xv/Pi_Cv` still no-go |
| D8 | cusp data | native `clauseF` | `S2619CuspUniformizerActual` builds old `SourceCuspClause` (real ε), not clauseF |
| D9 | coherence records / five compatibility pairs / orbicurve stack slot | **no native T field** | `D9CompatibilitySupply` + `S1881D9OrbicurveSlot` + `S2671` stack no-go; see §5 |
| D10 | assembly of six clauses | `SourceClauseConstructionWitness.sourceData` (`SourceClauseConstructors.lean:1088–1127`) | conditional on clauseA–F |
| D11 | conclusion | `SourceNativeInitialThetaExists` / A2 gate | open |

Gate equivalences (read, not recompiled):
`SourceNativeArithmeticToSourceGate l ↔ ∀ A, ∃ SQ : SourceSignQuotientData A,
Nonempty (SourceClauseAssembly A SQ)` — `SourceDefinition31SignQuotientSupplyReduction.lean:384–392`;
same restatement in `tmp/sheaf/xif/paper/S1494NativeArithmeticRootActual.lean:348–364`.
`SourceClauseAssembly` = the six clauses over a fixed `(A, SQ)`
(`SourceDefinition31SignQuotientSupplyReduction.lean:295–303`).

## 5. D9: exact false target vs clauseF

### 5.1 What S2671 actually proves

`tmp/sheaf/xif/paper/S2671D9StackRepairActual.lean` (namespace
`LeanFormal.IUT.XiFPaper.S2671D9StackRepairActual`), imports only
`S2667FiberCoherenceActual`, `S2662D9StackGoalReductionActual`,
`S2666NewTorsorSheafActual`, `S2670D9EssSurjActual`:

```lean
theorem S2671Fiber_not_isPrestack (D : S2619ActionGroupoidData l F) :
  ¬ (S2667FiberPseudofunctor l F D).IsPrestack (Iut.SchemeOverField.etaleTopology F)   -- :241
theorem S2671Fiber_not_isStack (D : S2619ActionGroupoidData l F) :
  ¬ (S2667FiberPseudofunctor l F D).IsStack (Iut.SchemeOverField.etaleTopology F)      -- :269
theorem S2671FiberIsStack_of_input (D) (hpre) (hess) :
  (S2667FiberPseudofunctor l F D).IsStack (etaleTopology F)                            -- :299
```

`S2676D9StackConditionalActual.S2676FiberIsStack_of_input` is the same
conditional statement. Axioms in `S2671D9StackRepairActual.out`: trios only
(`propext, Classical.choice, Quot.sound`), no `sorryAx`.

The no-go is about the *bare action-groupoid fiber* of `S2619ActionGroupoidData`
over the full étale site: the empty slice object has a covering sieve, so the
hom presheaf cannot be a sheaf there. The file itself says: "One must either
remove the empty object from the site or pass to the stackification"
(`:39–41`). Nothing in it mentions `SourceClause`, `SourceNative`,
`Definition 3.1`, or a clause (grep: 0 matches).

### 5.2 Why clauseF cannot consume it (field-level proof)

- `boundary_origin : TorsionQuotientBoundaryOrigin l A S.cK` — fields are
  `rank_one_quotient`, `originMap`, `cusp`, `originMap_distinguishedClass`.
  No stack/sheaf/descent.
- `quotient_basis_eq_k_torsion_basis` — equality with clauseC's
  `D.k_torsion_basis`.
- `boundary_cusp_eq_epsilon` — equality with `S.epsilon`.
- `cusp_decomposition` — `OrbicurveCuspidalDecompositionData E.c_groups.groups`,
  whose fields are a cusp, a closed subgroup, and surjectivity of the restricted
  projection. No stack/sheaf/descent.
- `cusp_decomposition_cusp_eq_origin` — an equality of cusps.

No field of clauseA–E or of `SourceSignQuotientData` refers to
`S2667FiberPseudofunctor`, `S2619ActionGroupoidData`, `IsStack`, or
`IsPrestack` either. (`EtaleStackOverField` and `HyperbolicOrbicurve` do carry
an `isStack` *field* — a proof supplied with the orbicurve — but that is an
input, not the S2671 target.)

**Stronger formal fact.** `tmp/sheaf/xif/paper/S1887D9CuspActual.lean:276–285`:

```lean
theorem S1887CuspOrigin_nonempty_iff_cusp (hI) {X} :
  Nonempty (TorsionQuotientBoundaryOrigin l (S1732A l) X) ↔
    Nonempty (Iut.OrbicurveBoundaryCusp X)
```

with the forward map `O ↦ O.cusp` and the backward map the **constant origin
map** at the given cusp (`S1887ActualOrigin`, `:205–213`;
`S1887ActualOrigin_originMap_constant`, `:236–241`). So, under the current
contract, `TorsionQuotientBoundaryOrigin` carries no content beyond *one
boundary cusp* plus the rank-one quotient. In clauseF, the rank-one quotient is
canonical from `D.k_torsion_basis` (`canonicalKQuotientData`,
`SourceClauseConstructors.lean:874–884`) and the cusp must be `S.epsilon`,
which is already a field of `S`. Hence clauseF is automatically inhabitant
given clauseC and `S.epsilon`:

```lean
SourceClauseConstructors.ofCanonicalBoundaryData
  (C := C) (B := B) (D := D) (E := E) (L := L)
  (originMap := fun _ => S.epsilon) rfl
  (S2555CuspidalDecomposition E.c_groups.groups S.epsilon) rfl
```

and equivalently `S2555SourceClauseF O hbasis hcuspeq`
(`S2555D8CuspidalDecompositionActual.lean:43–53`) once any
`O : TorsionQuotientBoundaryOrigin l A S.cK` with the two equalities is given.
The `S.epsilon` itself is part of the missing `S`, so **clauseF is blocked by
`S` being missing, not by D9**.

**D9-adjacent data that does exist in the pipeline, and why it does not change
the verdict:**

- `D9CompatibilitySupply.cusp := ArithmeticCuspOriginCompatibility O`
  (`SourceDefinition31D4D9Supply.lean:198–208`, `SourceDefinition31ArithmeticCompatibilitySlots.lean:221–226`)
  is a *downstream consumer* of the same `O`; it is proved from `O`
  (`arithmeticCuspOriginCompatibility_of_supply`, `:231–236`), not a
  precondition of clauseF. (Note: this is the old `SourceDefinition31Data`
  D9, not the S2671 stack D9.)
- `S1881D9OrbicurveSlot` (`S1881D9D7bActual.lean:165–183`) demands
  `cF : HyperbolicOrbicurve F` with signature `(1,1)^±`, `core`,
  `cK` with `(1,l-tors)^±`, `xK` with `(1,l-tors)`, `coverMap`,
  `coverFiniteEtale`, `groups`. This overlaps `S`'s `cF, xK, cK,
  xKExtension, cKExtension, xKType, cKType`, but T does not reference this
  structure; and the missing `S` needs strictly more (sign action, quotient
  witness, `xF`, `V`, `epsilon`). The D9 **open object** is thus a
  prerequisite of `S`, but the D9 **false proposition** is not.
- `S1887D9CuspFirstMissing l S := OrbicurveBoundaryCusp S.cK`
  (`S1887-d9-cusp-actual.md:121–129`) is the exact first missing field of the
  D9 cusp slot; it is *also* exactly the extra datum clauseF needs beyond
  `D.k_torsion_basis` — and in T it is already a field (`S.epsilon`).

### 5.3 Verdict

**D9-blocking verdict: NO.** The current D9 false target
(`S2671Fiber_not_isPrestack`/`not_isStack`) does not block clauseF, does not
appear in clauseF's type, and is not required to construct clauseF. If someone
insists on building `S.cF`/`S.cK` *as* the bare action-groupoid fiber
`S2667FiberPseudofunctor D` over the full étale site, then S2671 blocks that
route — but T only needs *some* `HyperbolicOrbicurve` values (each carrying its
own `isStack` proof), and S2671 itself points to stackification / removing the
empty object as the repair. Conversely, clauseF cannot be used to "fix" D9: it
does not supply the C_F/C_K objects.

## 6. T construction — actual required checklist

Status legend: **AVAILABLE** (actual, in tree, olean present) / **CONDITIONAL**
(constructor exists, inputs missing) / **MISSING** (no inhabitant in tree).

1. **A : InitialThetaArithmeticData l** — input. AVAILABLE by hypothesis.
2. **fbar : SourceFbarExtension A** — AVAILABLE:
   `SourceFbarExtension.canonical A` (`SourceArithmeticPrelude.lean:65`),
   carrier `AlgebraicClosure A.F`, comparison `AlgEquiv.refl`.
3. **S : SourceSignQuotientData A** — **MISSING**. Equivalent to
   `SourceSignQuotientGeometricCore A` + `SourcePlaceSelection A`
   (`nonempty_sourceSignQuotientData_iff_core_and_selection`,
   `SourceDefinition31SignQuotientSupplyReduction.lean:190–202`).
   - Place-selection half: **AVAILABLE** unconditionally
     (`placeSelectionOfArithmeticData`, `:210–220`; `sourcePlaceSelectionNonempty`, `:217–220`).
   - Geometric-core half: **MISSING**; no inhabitant in the tree; first field
     `G.xF : Iut.HyperbolicOrbicurve A.F` with
     `G.xF_geometry : SourceOncePuncturedGeometry A.curve G.xF`
     (`SourceSignQuotientConstruction.lean:30–66`;
     `S1494NativeArithmeticRootActual.lean:376–392`).
     Six units needed: base `xF`; involution; sign quotient `cF` + witness;
     F-side groups; K-side `xK, cK` + scalar extensions + signatures;
     boundary cusp `epsilon` (`SourceGeometricCoreFieldUnits`,
     `SourceGeometricCoreFieldUnitsReduction.lean:243–275`).
4. **clauseA** — **MISSING**. Only conditional constructor
   `SourceClauseA.ofGoodOrMultiplicativeReduction`
   (`SourceClauseConstructors.lean:229–249`), requiring for every
   `p : FinitePlace A.F`: `HasGoodReductionAt p ∨ HasMultiplicativeReductionAt p`;
   plus `SourceFieldOfModuli A`; plus a genuine maximal solvable
   `IntermediateField A.Fmod A.F` with the finite-Galois-solvable property and
   maximality. `Definition31D2Root.ofArithmetic` does **not** supply these
   (it only projects tower/curve/√−1/degree).
5. **clauseB** — **MISSING**. Only `SourceClauseB.ofTateComparisonWitnesses`
   (`:385–400`): multiplicative reduction over `S.V_mod_bad`, a
   `SourceTateComparisonWitness` (q-candidate + `TateCurveComparison` +
   order coprimality) for every bad place, and residue-characteristic
   coprimality. The old D4 supply `D4ReductionSupply`
   (`SourceDefinition31D4D9Supply.lean:99–114`) assembles the old
   `SourceReductionClause`, not native clauseB.
   Caution: the only compiled l=5 no-go bearing on the *coprimality card* is
   `S1280_clauseC_refuted_at_five : ¬ Nonempty (BadPlaceQParameterCards (S1280Selection S1280Five))`
   (`S1280SourceDefinition31Actual.lean:445–455`), about the old D4 card for the
   concrete Gaussian selection (bad residue characteristic 5). It is **not** a
   theorem `¬ Nonempty (SourceClauseB ...)`; the STATE/ledger claim "clauseB
   refuted at l=5" is an audit claim without a compiled native-clause theorem.
   (The separate clauseC no-go at the Gaussian root is S1519, see item 6.)
6. **clauseC** — **MISSING**, and *refuted* over the Gaussian K=F root.
   Conditional assembly `SourceTorsionDatum.toSourceClauseC`
   (`SourceTorsionCarrierReduction.lean:187–193`) from a D5 datum
   (rank-two basis + `SL_2` image + kernel-field identification) plus
   `Torsion23Rational A.curve`. Open cards in tree:
   `RankTwoTorsionBasisGap` (`:260–262`, unproved; Mathlib lacks
   `finrank (ZMod l) E[l] = 2`), `SerreStyleLargeImageStatement`. The actual
   `S2601_d5LargeImage : S1987D5LargeImageFive` is **not** a
   `SourceTorsionDatum` for arbitrary `A`: it is the S1725/S1982Basis model
   target (see §7).
   **Compiled no-go:** `S1519_no_sourceClauseC_false` — if
   `Nonempty (A.K ≃ₐ[A.F] A.F)` then every candidate `SourceClauseC A S C B`
   yields `False` (kernel field `L = A.K` becomes `⊥`, the representation is
   trivial, and `image_contains_SL2` fails on `!![1,1;0,1]`). Hence
   `S1519_nativeThetaActual_impossible (l) :
   ¬ Nonempty { T : SourceNativeInitialThetaData l // T.arithmetic =
   S1280Arithmetic l }`, for every `l : PrimeGeFive`. `S1543` records that a
   corrected root must replace `K` by a nontrivial finite Galois extension of
   `F`; no corrected-root T is constructed.
7. **clauseD** — **MISSING**. Only `SourceClauseD.ofKSideWitnesses`
   (`:609–660`): K-side sign action, quotient + universal witness, scalar
   extension of the quotient morphism with the cast equality, finite-étale cover
   `xK → cK` equal to the quotient map, group data for `xK`/`cK` over `G_K`,
   group inclusion, and the two embeddings into the F-side sequences. None of
   these exists in the tree for arbitrary `A`.
8. **clauseE** — **MISSING**. Only `SourceClauseE.ofLocalFamilies`
   (`:799–810`): the two selected-place equalities are copied from `S`
   (`S.V_eq_section`, `S.V_mod_bijection`), but the finite/infinite
   `SourceFiniteLocalSource`/`SourceInfiniteLocalSource` families for every
   selected `v` must be supplied (completions, local base-changed curves, sign
   actions, quotient witnesses, local/global groups, embeddings). Missing.
9. **clauseF** — **CONDITIONAL, and only on items 3/6**: given `D : SourceClauseC`
   and `S.epsilon`, use `SourceClauseConstructors.ofCanonicalBoundaryData`
   (`:981–1012`) with `originMap := fun _ => S.epsilon`,
   `originMap_epsilon := rfl`,
   `cuspDecomposition := S2555CuspidalDecomposition E.c_groups.groups S.epsilon`,
   `cuspDecomposition_origin := rfl`. Equivalently `S2555SourceClauseF` with
   `O` built by `boundaryOriginFromKBasis` (`:886–906`). **No D9 data is
   needed.** The paper-faithful origin map / bad-place local generator
   condition is *not* encoded and remains the parked card
   `IUT-I.definition-3.1-D9-cusp-local-generator`; supplying the constant map
   is formally admissible but not paper-faithful.
10. **Package T** — AVAILABLE once 3–9 exist:
    `SourceClauseConstructionWitness.sourceData`
    (`SourceClauseConstructors.lean:1088–1127`), or
    `witnessOfClauseAssembly` (`SourceDefinition31SignQuotientSupplyReduction.lean:317–330`).
    The A2 gate is exactly `∀ A, ∃ SQ, Nonempty (SourceClauseAssembly A SQ)`
    (`:384–392`) and remains open.

Minimal dependency picture for clauseF:

```
S : SourceSignQuotientData A ──> S.cK, S.epsilon
        │
clauseC (D) ──> D.k_torsion_basis ──┐
                                    ▼
             TorsionQuotientBoundaryOrigin (rank-one quotient + cusp)
                                    │  (constant origin map is allowed)
                              clauseF  ◄── cuspidal decomposition (automatic)
```

D9 (S2671/S2667/S2619 stack) appears nowhere in this picture.

## 7. Actual artifacts: what they really supply

All oleans below are present and newer (by mtime) than their sources; none was
recompiled in this audit. Axiom claims are quoted from the existing `.out`
files (trio `propext, Classical.choice, Quot.sound`).

| artifact | olean (size, mtime UTC) | theorem(s) | actual content | does it supply a native clause? |
|---|---|---|---|---|
| `S2601D5LargeImageAssembleActual` | 10,736 B, 2026-11-06 12:43 | `S2601_d5LargeImage : S1987D5LargeImageFive` | large-image for the S1725/S1982Basis model (Q(i) line) | **No** — not `SourceClauseC`; not arbitrary A |
| `S2587CanonicalCoverIsoFromDataActual` | 33,152 B, 2026-11-06 12:42 | `S2587CanonicalCoverIsoFromData : S2562CanonicalCoverIsoFromData` | canonical cover iso for the S2482 Qi orbicurve model | **No** — not `SourceClauseD` |
| `S2622D6AssemblyActual` | 103,632 B, 2026-11-06 12:42 | `S2622CanonicalCoverIsoFromData : S2562CanonicalCoverIsoFromData` | second proof of the same model cover iso | **No** |
| `S2677D7bLocalGroupsActual` | 149,032 B, 2026-11-06 13:04 | `S2677D7SectionConstruction : D7SectionConstruction l`; `S2677D7bLocalGroupSectionConstruction` | old-framework `SourceSectionClause` gate | **No** — not `SourceClauseE` |
| `S2619CuspUniformizerActual` | 49,264 B, 2026-11-06 12:58 | `S2619CuspClause : SourceCuspClause`; `S2619CuspUniformizerRequired` | old `SourceCuspClause` = real ε + cuspScale, uniformizer at the place above 5 | **No** — not `SourceClauseF` (native clauseF has no real ε) |
| `S2671D9StackRepairActual` | 260,696 B, 2026-11-06 13:04 | `S2671Fiber_not_isPrestack`, `S2671Fiber_not_isStack`, `S2671FiberIsStack_of_input` | D9 stack no-go + conditional stack | **No** — and not required by clauseF |
| `S2555D8CuspidalDecompositionActual` | 68,440 B, 2026-11-05 16:04 | `S2555CuspidalDecomposition`, `S2555SourceClauseF` | **native** `SourceClauseF` constructor from `O` + basis/cusp equalities | **Yes**, conditionally on `O` |
| `S1887D9CuspActual` | 414,752 B, 2026-11-01 04:40 | `S1887CuspOrigin_nonempty_iff_cusp`, `S1887ActualOrigin` | shows `TorsionQuotientBoundaryOrigin` ≡ one boundary cusp (constant origin map) | supporting only |
| `S1519NativeThetaConcreteActual` | 187,624 B, 2026-10-30 18:59 | `S1519_no_sourceClauseC_false`, `S1519_nativeThetaActual_impossible`, `S1519_first_native_field_is_clauseC` | **no-go**: over the Gaussian K=F root, clauseC is empty, hence no T over that root | it is a *refutation*, not a provider |
| `S1543CorrectedGaussianArithmeticActual` | 146,112 B, 2026-10-30 19:05 | `s1543_uncorrected_no_clauseC`; `S1543CorrectedArithmeticRoot` | records that a corrected root must have K ≠ F; no corrected T | boundary only |
| `SourceDefinition31Quantifiers` | 5,469,648 B, 2026-10-31 18:34 | definitions of T/clauses | native structure | definitional |
| `SourceClauseConstructors` | 569,552 B, 2026-10-16 11:24 | `ofCanonicalBoundaryData` etc. | conditional clause constructors | constructors |

Also relevant old-framework gates (`SourceDefinition31RootLemmas.lean:5145–5174`):
`D5TorsionConstruction`, `D6OrbicurveConstruction`, `D7SectionConstruction`,
`D8CuspConstruction` are `∀ A, Nonempty (SourceTorsionClause / SourceOrbicurveClause /
SourceSectionClause / SourceCuspClause)` — all over the **old** clause types,
none equivalent to the native `SourceClauseC/D/E/F`. This is the precise sense
of STATE 4213 "D5–D8 do not fill T".

## 8. Caveats / corrections / not claimed

- **No compile, no kernel check.** Everything above is a source/olean-mtime
  audit. The clauseF inhabitance argument is a term-construction argument on
  paper (the constructors exist and typecheck in the source; I did not rerun
  Lean).
- **STATE.md grows concurrently.** During this audit it was appended from 4207
  to 4234 lines. New entries (STATE 4216–4234) say "T at l=5 REFUTED in current
  encoding" and "T/D9 is a side branch; its blockers do not block paper 3.12".
  There **is** a compiled root-specific no-go:
  `S1519_nativeThetaActual_impossible (l) : ¬ Nonempty {T // T.arithmetic =
  S1280Arithmetic l}` for the Gaussian K=F root, for every `l` (via clauseC;
  `S1519_no_sourceClauseC_false`). It is **not** an `l = 5` theorem and does not
  refute T for arbitrary `A`. I found no compiled theorem of the form
  `¬ Nonempty (SourceNativeInitialThetaData 5)` or
  `¬ Nonempty (SourceClauseB ...)` (grep: 0 hits). The only compiled l=5
  no-go specific to l is `S1280_clauseC_refuted_at_five` about
  `BadPlaceQParameterCards` for the concrete Gaussian selection. Treat the
  ledger's "T at l=5 refuted" as a paraphrase of S1519 at that root (or as a
  claim awaiting its own theorem), not as a general l=5 obstruction.
- The `TorsionQuotientBoundaryOrigin` ↔ cusp equivalence (S1887) is stated for
  the `S1732A` line and requires its `hI`; the same argument transports to any
  supplied rank-one quotient, and clauseC supplies one. I did not formalize that
  transport.
- Using the constant origin map is **formally** allowed but does not encode the
  paper's local generator condition; do not present it as a paper-faithful
  construction of clause (f).
- `S2671` olean is 260,696 B here; STATE 4066 records 260,688 B. The difference
  is not investigated (no recompilation); both postdate the source by mtime.
- `SourceArithmeticGateConsequences.lean`, cited in
  `THEOREM311_A2_SOURCE_COMPLETION_CHECKLIST.md`, does **not** exist in the
  tree (glob: 0 hits). Do not cite it as evidence.
- Nothing in this report asserts that `SourceNativeArithmeticToSourceGate`,
  `SourceClauseA`–`E`, or the geometric core have inhabitants.
