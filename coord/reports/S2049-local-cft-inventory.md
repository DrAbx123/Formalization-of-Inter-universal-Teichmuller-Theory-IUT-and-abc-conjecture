# S2049: local field / local CFT foundation inventory

Date: 2026-11-02 (Asia/Shanghai). Workspace: D:/lean. Lean: `leanprover/lean4:v4.32.2`.
Mathlib: `v4.32.2`, rev `905b95818eb32af7874a58b427f50c1711a5e96c`.
Workspace HEAD at audit time: `9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee` (dirty tree; source files were read directly).

Scope: audit Mathlib v4.32.2 and the tree for reusable local field / local CFT
foundations (`IsNonarchimedeanLocalField`, unramified extensions, Frobenius, roots of
unity, norm, profinite completion, Galois groups, topological abelianization); record
the exact API and the gap chain for P1-P3; supply a reusable Lean interface.

Report status: audit + interface only. This report does **not** construct the local
Artin map, does not fabricate an inhabitant of any missing object, and does not claim
`target_accepted`. The companion Lean file constructs only what is constructible from
Mathlib v4.32.2 alone; its one open structure is explicitly the missing P1 object.

---

## 0. What P1/P2/P3 mean in this report

These labels follow the predecessor chain S2039/S2040 and are used consistently below:

| Label | Exact mathematical target | Existing formal target |
|---|---|---|
| **P1** | the maximal unramified extension `L^ur` of a finite `L/Q_p` inside a fixed algebraic closure, together with a topological group isomorphism `Gal(L^ur/L) ≃ Ẑ` sending arithmetic Frobenius to the topological generator | new: `UnramifiedGaloisData` in this report's Lean file; S2040 P1 |
| **P2** | the cyclotomic/torsion identification `μ(L) = torsion(L^×) ≃* torsion(Gal(L^ab/L))` | S2027 `localArtinTorsion` / `localArtinTorsionTopological`; S2039 M2a |
| **P3** | norm limitation, the local existence theorem, and transfer/norm compatibility `rec_H ∘ N_{L_H/L_K} = V ∘ rec_K` | S2024 `LocalReciprocityData.transfer_compat`; S2017 Verlagerung; missing norm limitation/existence |

P1 is only the **unramified quotient**. It is not P2: `Gal(L^ur/L) ≅ Ẑ` is torsion-free,
whereas P2's torsion lives in the inertia/cyclotomic direction of `Gal(L^ab/L)`. P1 does
not imply P2, and P2 does not imply P3.

---

## 1. Executive summary

### 1.1 Mathlib v4.32.2

Mathlib v4.32.2 has substantially more local-field infrastructure than the predecessor
reports S2039/S2040 assumed. In particular it has:

- a bundled `IsNonarchimedeanLocalField` class with the discrete valuation ring, finite
  residue field, compact integer ring, complete field, and a canonical value-group iso to
  `ℤᵐ⁰`;
- the valuation ring, integrality criterion, valuation extension API, and the fact that
  the maximal ideal of `𝒪[L]` lies over that of `𝒪[K]`;
- ramification index, inertia degree, the fundamental identity, decomposition/inertia
  subgroups, and the finite exact sequence `Stabilizer/Inertia ≃* Gal(κ_L/κ_K)`;
- arithmetic Frobenius elements `arithFrobAt` at a prime with finite residue field,
  uniqueness for unramified extensions, and the action on prime-to-`p` roots of unity;
- `Algebra.norm`, `CommGroup.torsion`, `rootsOfUnity`, `IsPrimitiveRoot`,
  `modularCyclotomicCharacter`, `cyclotomicCharacter`, and continuity of the cyclotomic
  character on a Galois group;
- profinite completion with its universal property and dense image, topological
  abelianization, absolute Galois groups, the infinite Galois correspondence, Krull
  topology, and the identification of `Gal(K/k)` with the limit of finite quotients.

Mathlib v4.32.2 still does **not** have:

- a maximal unramified extension `L^ur` as an object, or the theorem `Gal(L^ur/L) ≅ Ẑ`;
- a named `Ẑ` object (only `ProfiniteCompletion.completion ℤ`);
- the unramified local Artin map `rec_ur`, or the local Artin map `rec_L`;
- norm limitation, the local existence theorem, or Hilbert symbols;
- the identification `μ(L) ≃ torsion(Gal(L^ab/L))`.

### 1.2 Tree

The tree already has the **abelian carrier** for P2/P3 but not the unramified/P1 carrier:

- S2027 constructs `L^ab` as the fixed field of the closed commutator of
  `Gal(Qbar_p/L)`, proves `TopologicalAbelianization Gal(Qbar_p/L) ≃* Gal(L^ab/L)`, defines
  `mu L = CommGroup.torsion L^×`, proves the norm of a root of unity is torsion, and
  constructs the profinite completion of `L^×`;
- S2024 reduces S2017's `muQZComparison`/`muHatComparison` to `LocalReciprocityData`
  (fields `equiv` and `transfer_compat`); S2039 packages the same missing datum as
  `S2039FirstMissing`;
- the local-field analytic stack (`Integers`, compact unit group, principal units, finite
  torsion, logarithm, Galois action, Kummer rigidity) is reusable for P2/P3, but it is
  **norm-based** (`NormedField.valuation`) rather than the `ValuativeRel` API used by
  `IsNonarchimedeanLocalField`; a bridge is required;
- no file in the tree defines `L^ur`, `Ẑ`, `rec_ur`, or `Gal(L^ur/L) ≅ Ẑ`.

### 1.3 Donors outside the dependency graph

Two complete local-CFT developments exist under `tmp/` and were source-audited:

| Donor | Lean/Mathlib | P1 | P2 | P3 | Status |
|---|---|---|---|---|---|
| `tmp/.../lana/local-class-field-theory` (LCFF) | Lean v4.32.0, Mathlib `81a5d257...` | `maxUnramified`, `frobUr`, `galMaxUnramifiedEquiv` | `artin`, `artinCompletionEquiv`, `unitsInertiaEquiv` | `NormLimitation.exists_abFin_le_norm`, `ExistenceTheorem.existence`, `NormCompat` | source scan: 0 `sorry`/`admit`/`native_decide`, 0 `axiom` declarations; no `.lake`, not built here; depends on `continuous-kummer-theory` |
| `tmp/TauCeti` | Lean v4.36.0-rc1, Mathlib `2cabef97...` | `maximalUnramifiedExtension`, `maximalUnramifiedFrobenius`, `maximalUnramifiedGaloisGroupEquivZHat` | `artinMap`, `localArtinMap_*`, inertia | `Norm/`, `unitFiltration_le_normGroup_*` | CI-enforced no-sorry project; not built here; newer Mathlib API |

LCFF is the closest practical P1/P2/P3 port because its toolchain is only a patch behind.
TauCeti is the better reference for statement design and naming, but its Mathlib is newer.

### 1.4 New Lean artifact

`tmp/sheaf/xif/paper/S2049LocalCFTInventory.lean` (EXIT=0) constructs:

- `Zhat := ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))`;
- `zhatOfInt : Multiplicative ℤ →* Zhat` and `DenseRange zhatOfInt`;
- `normalizedValuation L : Lˣ →* Multiplicative ℤ` for `[IsNonarchimedeanLocalField L]`;
- `normalizedValuation_eq_one_iff : v(u)=1 ↔ valuation L u = 1`;
- the exact P1 structure `UnramifiedGaloisData` with fields `Lur`,
  `isMaximalUnramified : IsMaximalUnramified L Lur`, and
  `galEquiv : Gal(Lur/L) ≃ₜ* Zhat`;
- from an inhabitant: `frobenius`, `artin : Lˣ →* Gal(Lur/L)`, the defining square
  `galEquiv (artin x) = zhatOfInt (v x)`, `artin_unit`, and `artin_uniformizer`;
- `P1ExactMissing L := Nonempty (UnramifiedGaloisData L)` (stated, not inhabited).

Nothing in the file is a fake: the only open structure is the explicit missing P1
carrier; all other declarations are proved. Axiom footprint of every new theorem is
`[propext, Classical.choice, Quot.sound]`.

---

## 2. Mathlib v4.32.2 exact API inventory

All paths below are relative to `D:/lean/.lake/packages/mathlib/Mathlib/`. Line numbers
are from the pinned checkout.

### 2.1 Nonarchimedean local fields

`NumberTheory/LocalField/Basic.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `IsNonarchimedeanLocalField K` | 45 | `class ... [Field K] [ValuativeRel K] [TopologicalSpace K] : Prop extends IsValuativeTopology K, LocallyCompactSpace K, ValuativeRel.IsNontrivial K` |
| `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` | 116 | `ValueGroupWithZero K ≃*o ℤᵐ⁰` (noncomputable) |
| instance `CompactSpace 𝒪[K]` | 102 | `CompactSpace (Valuation.integer (valuation K))` |
| instance `IsDiscreteValuationRing 𝒪[K]` | 108 | discrete valuation ring structure |
| instance `IsCyclic (ValueGroupWithZero K)ˣ` | 130 | value group units cyclic |
| instance `ValuativeRel.IsDiscrete K` | 133 | discreteness |
| instance `ValuativeRel.IsRankLeOne K` | 136 | rank one |
| instance `Finite 𝓀[K]` | 140 | finite residue field |
| instance `CompleteSpace K` | 157 | requires a compatible uniform space |
| instance `CompleteSpace 𝒪[K]` | 167 | same |
| instance `IsAdicComplete 𝓂[K] 𝒪[K]` | 176 | adic completeness of the integer ring |

Notation: `𝒪[K]` is `Valuation.integer (valuation K)`; `𝓀[K]` is its residue field;
`𝓂[K]` is its maximal ideal (available through `Valued.integer`/`IsLocalRing` API).

### 2.2 Valuation ring, integrality, and valuation extension

`RingTheory/Valuation/Integral.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `Valuation.Integers.isIntegral_iff_v_le_one` | 34 | for `hv : Integers v O`, `IsIntegral O x ↔ v x ≤ 1` |
| `Valuation.Integers.integralClosure` | 61 | `integralClosure O R = ⊥` (integral closure is `O`) |
| `Valuation.Integers.isIntegrallyClosed` | 76 | `IsIntegrallyClosed O` in the fraction-field case |

`RingTheory/Valuation/Extension.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `Valuation.HasExtension vR vA` | 66 | `class ... : Prop` with field `val_isEquiv_comap : vR.IsEquiv (vA.comap (algebraMap R A))` |
| `HasExtension.val_map_le_iff` | 77 | `vA (algebraMap x) ≤ vA (algebraMap y) ↔ vR x ≤ vR y` |
| `HasExtension.instAlgebraInteger` | 120 | `Algebra vR.integer vA.integer` |
| `HasExtension.instIsScalarTowerInteger` | 142 | `IsScalarTower vR.integer vA.integer A` |
| `HasExtension.instIsLocalHomValuationInteger` | 155 | `IsLocalHom (algebraMap vR.integer vA.integer)` |
| `HasExtension.maximalIdeal_comap_algebraMap_eq_maximalIdeal` | 202 | `(maximalIdeal L₀).comap (algebraMap K₀ L₀) = maximalIdeal K₀` |
| `HasExtension` instance `Ideal.LiesOver (maximalIdeal L₀) (maximalIdeal K₀)` | 206 | maximal ideals lie over |
| `HasExtension.algebraMap_residue_eq_residue_algebraMap` | 209 | residue map compatibility |

This is the exact bridge needed to apply Mathlib's ramification theory to local fields:
`A = 𝒪[K]`, `B = 𝒪[L]`, `p = 𝓂[K]`, `q = 𝓂[L]`.

### 2.3 Ramification, inertia, decomposition, and finite Frobenius

`NumberTheory/RamificationInertia/Ramification.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `Ideal.ramificationIdx'` | 67 | `ℕ`, multiplicity of `P` in `map f p` |
| `Ideal.ramificationIdx'_eq_factors_count` | 278 | equals multiplicity |
| `Ideal.ramificationIdx'_algebra_tower` | 394 | multiplicativity in towers |

`NumberTheory/RamificationInertia/Inertia.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `Ideal.inertiaDeg'` | 69 | `finrank (R⧸p) (S⧸P)` |
| `Ideal.inertiaDeg'_algebra_tower` | 195 | multiplicativity in towers |

`NumberTheory/RamificationInertia/Basic.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `Ideal.sum_ramification_inertia` | 585 | `∑ P, e(P) * f(P) = finrank K L` |
| `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` | 639 | local-ring case: `e * f = finrank K L` |

`NumberTheory/RamificationInertia/Galois.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `Ideal.ramificationIdxIn` | 59 | common `e` over a prime in a Galois extension |
| `Ideal.inertiaDegIn` | 68 | common `f` |
| `Ideal.card_inertia_eq_ramificationIdxIn` | 317 | `Nat.card (inertia) = e` |
| `Ideal.card_stabilizer_eq` | 330 | `Nat.card (stabilizer) = e * f` |

`RingTheory/Valuation/RamificationGroup.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `ValuationSubring.decompositionSubgroup` | 30 | stabilizer of a valuation subring in `L ≃ₐ[K] L` |
| `ValuationSubring.subMulAction` | 35 | action on the valuation subring |
| `ValuationSubring.decompositionSubgroupMulSemiringAction` | 40 | `MulSemiringAction` on `A` |
| `ValuationSubring.inertiaSubgroup` | 50 | kernel of the action on the residue field of `A` |

`RingTheory/Invariant/Basic.lean` is the finite exact sequence used by the donor:

| Declaration | Line | Statement / role |
|---|---|---|
| `Ideal.Quotient.stabilizerHom` | 341 (Over.lean) | `Stabilizer G Q →* ((B⧸Q) ≃ₐ[A⧸p] (B⧸Q))` |
| `IsFractionRing.stabilizerQuotientInertiaEquiv` | 373 | `Stabilizer Q ⧸ inertia ≃* Gal(L/K)` (residue fraction fields) |
| `Ideal.Quotient.stabilizerQuotientInertiaEquiv` | 386 | `Stabilizer Q ⧸ inertia ≃* Gal((B⧸Q)/(A⧸P))` |

For a finite unramified `L/K`, the inertia is trivial and the stabilizer is all of
`Gal(L/K)`, so this is the exact finite-level isomorphism
`Gal(L/K) ≃* Gal(κ_L/κ_K)`. Mathlib does not package that specialization as one named
theorem; it must be assembled from `IsUnramified`/`ramificationIdx` and the above.

`RingTheory/Frobenius.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `AlgHom.IsArithFrobAt` | 54 | `∀ x, φ x - x ^ Nat.card (R⧸Q.under R) ∈ Q` |
| `IsArithFrobAt` | 181 | action version for `σ : M` |
| `IsArithFrobAt.mem_stabilizer` | 192 | Frobenius lies in the stabilizer |
| `IsArithFrobAt.mul_inv_mem_inertia` | 198 | two Frobenii differ by inertia |
| `AlgHom.IsArithFrobAt.apply_of_pow_eq_one` | 109 | on prime-to-`q` roots of unity, `φ ζ = ζ^q` |
| `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt` | 162 | uniqueness in the unramified case |
| `IsArithFrobAt.exists_of_isInvariant` | 219 | existence for finite `G` with finite residue field |
| `arithFrobAt` | 258 | chosen Frobenius element |
| `arithFrobAt_mem_stabilizer` | 266 | it stabilizes the prime |
| `isConj_arithFrobAt` | 270 | conjugate Frobenii at primes over the same ideal |

This is a genuine **finite-level** Frobenius, not `Gal(L^ur/L) ≅ Ẑ`. The inverse system
of finite unramified levels and its limit are exactly what Mathlib lacks.

### 2.4 Norm map

`RingTheory/Norm/Defs.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `Algebra.norm` | 61 | `S →* R`, determinant of left multiplication |
| `Algebra.norm_apply` | 64 | `norm R x = LinearMap.det (lmul R S x)` |
| `Algebra.norm_algebraMap` | 100 | `norm R (algebraMap x) = x ^ finrank R S` |

On units, use `Units.map (Algebra.norm K) : Lˣ →* Kˣ` (the donor's `normU`). Mathlib has
no norm limitation theorem, no norm-group openness, and no local existence theorem.

### 2.5 Roots of unity, torsion, cyclotomic character

`RingTheory/RootsOfUnity/Basic.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `rootsOfUnity k M` | 56 | `Subgroup Mˣ` of `k`-th roots of unity |
| `mem_rootsOfUnity` | 63 | `ζ ∈ rootsOfUnity k M ↔ ζ ^ k = 1` |
| `rootsOfUnity.mkOfPowEq` | 94 | constructor from `ζ ^ n = 1` |
| `rootsOfUnityEquivNthRoots` | 222 | equivalence with `nthRoots k 1` |

`RingTheory/RootsOfUnity/PrimitiveRoots.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `IsPrimitiveRoot ζ k` | 63 | structure proposition |
| `IsPrimitiveRoot.toRootsOfUnity` | 69 | coercion to `rootsOfUnity` |

`GroupTheory/Torsion.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `CommMonoid.torsion G` | 184 | torsion submonoid |
| `CommGroup.torsion G` | 307 | torsion subgroup for commutative groups |
| `CommGroup.mem_torsion` | 320 | `g ∈ torsion G ↔ IsOfFinOrder g` |
| `CommGroup.map_torsion_le` | 337 | torsion maps into torsion |
| `Torsion.ofTorsion` | 294 | `torsion (torsion G) ≃* torsion G` |

`NumberTheory/Cyclotomic/CyclotomicCharacter.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `modularCyclotomicCharacter` | 212 | `(L ≃+* L) →* (ZMod n)ˣ` when `L` has enough `n`-th roots |
| `cyclotomicCharacter L p` | 307 | `(L ≃+* L) →* ℤ_[p]ˣ` |
| `cyclotomicCharacter.spec` | 323 | `g ζ = ζ ^ (χ(g) mod p^n)` on `p^n`-th roots |
| `cyclotomicCharacter.continuous` | 336 | continuity on `Gal(L/K)` |

The cyclotomic character is defined on **ring automorphisms**. It does not produce a
map `L^× →* Gal(L^ab/L)`, so it cannot by itself close P2; it is the target-side
compatibility that the missing Artin map must satisfy.

### 2.6 Profinite completion and `Ẑ`

`Topology/Algebra/Category/ProfiniteGrp/Completion.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `ProfiniteCompletion.completion G` | 73 | limit of finite quotients, a `ProfiniteGrp` |
| `ProfiniteCompletion.etaFn G` | 77 | canonical function `G → completion G` |
| `ProfiniteCompletion.eta G` | 81 | canonical morphism `G ⟶ GrpCat.of (completion G)` |
| `ProfiniteCompletion.denseRange G` | 103 | `DenseRange (etaFn G)` |
| `ProfiniteCompletion.lift` | 147 | universal property |
| `ProfiniteCompletion.lift_eta` | 168 | `eta ≫ lift f = f` |
| `profiniteCompletion` | 190 | functor `GrpCat ⥤ ProfiniteGrp` |
| `ProfiniteCompletion.adjunction` | 214 | left adjoint to the forgetful functor |

There is **no** declaration named `Zhat` in Mathlib v4.32.2, and no theorem identifying
`ProfiniteCompletion.completion ℤ` with `∏_p ℤ_p`. The S2049 file names the completion
`Zhat` and uses `denseRange`; it does not need the product decomposition.

### 2.7 Galois groups, infinite Galois theory, absolute Galois group

`Gal(L/K)` is notation for `L ≃ₐ[K] L`; the field-theoretic API is in
`FieldTheory/Galois/Basic.lean`, `FieldTheory/Galois/Infinite.lean`, and
`FieldTheory/Galois/Profinite.lean`.

| Declaration | File:line | Statement / role |
|---|---|---|
| `IntermediateField.fixingSubgroup` | `Galois/Basic.lean:230` | `Subgroup Gal(E/F)` fixing an intermediate field |
| `IntermediateField.fixedField` | `Galois/Basic.lean` (definition) | fixed field of a subgroup |
| `IntermediateField.fixingSubgroupEquiv` | `Galois/Basic.lean:269` | `fixingSubgroup K ≃* Gal(E/K)` |
| `IntermediateField.fixedField_fixingSubgroup` | `Galois/Infinite.lean:84` | `fixedField (fixingSubgroup L) = L` |
| `InfiniteGalois.fixingSubgroup_isClosed` | `Galois/Infinite.lean:63` | fixing subgroup is closed |
| `InfiniteGalois.IntermediateFieldEquivClosedSubgroup` | `Galois/Infinite.lean:195` | order isomorphism intermediate fields ↔ closed subgroups |
| `InfiniteGalois.normalAutEquivQuotient` | `Galois/Infinite.lean:227` | `Gal(K/k) ⧸ H ≃* Gal(fixedField H/k)` for closed normal `H` |
| `InfiniteGalois.isOpen_iff_finite` | `Galois/Infinite.lean:240` | open fixing subgroup ↔ finite-dimensional |
| `InfiniteGalois.normal_iff_isGalois` | `Galois/Infinite.lean:260` | normal subgroup ↔ fixed field Galois |
| `InfiniteGalois.mulEquivToLimit` | `Galois/Profinite.lean:274` | `Gal(K/k) ≃* limit` of finite quotients |
| `InfiniteGalois.continuousMulEquivToLimit` | `Galois/Profinite.lean:323` | topological version |
| `InfiniteGalois.ProfiniteGalGrp` | `Galois/Profinite.lean:341` | `Gal(K/k)` as a profinite group |
| `IsGaloisGroup G K L` | `RingTheory/IsGaloisGroup/Basic.lean` (class), `FieldTheory/Galois/IsGaloisGroup.lean` | faithful action with fixed field `K` |
| `IsGaloisGroup.card_eq_finrank` | `Galois/IsGaloisGroup.lean:85` | `Nat.card G = finrank K L` |

`InfiniteGalois.normalAutEquivQuotient` is exactly what S2027 uses to identify
`TopologicalAbelianization Gal(Qbar_p/L)` with `Gal(L^ab/L)`.

### 2.8 Topological abelianization and absolute Galois group

`Topology/Algebra/Group/TopologicalAbelianization.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `TopologicalAbelianization G` | 42 | `G ⧸ Subgroup.topologicalClosure (commutator G)` |
| `TopologicalAbelianization.commGroup` | 48 | `CommGroup (TopologicalAbelianization G)` |

`FieldTheory/AbsoluteGaloisGroup.lean`

| Declaration | Line | Statement / role |
|---|---|---|
| `Field.absoluteGaloisGroup K` | 43 | `AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K` with Krull topology |
| `Field.absoluteGaloisGroupAbelianization K` | 59 | `TopologicalAbelianization (absoluteGaloisGroup K)` |

### 2.9 Exact Mathlib gaps (ordered)

1. No object `L^ur` (maximal unramified extension) and no proof that the finite
   subextensions of a candidate are exactly the unramified ones.
2. No theorem `Gal(L^ur/L) ≃* Ẑ` with Frobenius ↦ `1`; no proof that the arithmetic
   Frobenius is a topological generator.
3. No unramified local Artin map `rec_ur : L^× →* Gal(L^ur/L)`, and no local Artin map
   `rec_L : L^× →* Gal(L^ab/L)`.
4. No norm limitation theorem, no local existence theorem, no Hilbert symbol.
5. No identification `μ(L) ≃* torsion(Gal(L^ab/L))`; the cyclotomic character alone
   does not supply the Artin map.

Items 1-3 are P1; item 5 is P2; item 4 plus transfer compatibility is P3.

---

## 3. Tree inventory (reusable, actual)

### 3.1 Concrete local-field instances

`Iut/Foundations/SourceFiniteStageValuationDivisor.lean`:

| Declaration | Line | Statement / role |
|---|---|---|
| `stageIsNonarchimedeanLocalField` | 82 | `IsNonarchimedeanLocalField stage` for every finite Galois stage of a number-field finite place |
| `stageValueGroupWithZeroIsoInt` | 89 | value group iso to `ℤᵐ⁰` |
| `stageNormalizedAdditiveValuation` | 191 | `Additive stageˣ →+ ℤ`, normalized valuation |
| `stageNormalizedAdditiveValuation_nonnegative_iff` | 218 | nonnegativity ↔ valuation ≤ 1 |
| `stageNormalizedAdditiveValuation_nonnegative_iff_isIntegral` | 240 | nonnegativity ↔ integrality |
| `stageEffectiveRationalFunctionEquivIntegralMonoid` | 379 | effective monoid = integral monoid |

Reuse: this is the only production file that builds `IsNonarchimedeanLocalField`
instances from actual number-field data. It has no unramified/Frobenius content.

### 3.2 Analytic local-field stack

`LeanFormal/IUT/Foundations/LocalFields/` (norm-based):

| Declaration | File:line | Role |
|---|---|---|
| `Integers K` | `IntegralUnits.lean:25` | `(NormedField.valuation K).integer` |
| `compactSpace_units` | `IntegralUnits.lean:70` | compactness of `(Integers K)ˣ` under properness |
| `principalUnits` | `IntegralUnits.lean:82` | `1 + 𝔪` subgroup |
| `finite_principalUnitQuotient` | `IntegralUnits.lean:119` | finite quotient by principal units |
| `finite_integralUnitTorsion` | `IntegralUnitLogarithmTorsionFinite.lean:44` | `Finite (CommGroup.torsion (Integers K)ˣ)` |
| `unitLogHom_ker_eq_torsion` | `IntegralUnitLogarithmKernel.lean:54` | kernel of the actual log = torsion |
| `unitLogTorsionQuotientEquivRange` | `IntegralUnitLogarithmKernel.lean:83` | torsion quotient ≃ log image |
| `finite_logShellResidueField` | `IntegralLogShellIndexResidueFormula.lean:63` | finite residue field |
| `logShellResidueCard` | same:55 | residue cardinal `q` |
| `one_lt_logShellResidueCard` | same:103 | `1 < q` |
| `logShellRamificationExponent` | `IntegralLogShellRamificationInertia.lean:81` | norm-based `e = v_K(p)` |
| `logShellRamificationExponent_pos` | same:101 | `0 < e` |
| `localGaloisUnitMap` | `IntegralUnitLogarithmGalois.lean:36` | Galois action on `(Integers K)ˣ` |
| `unitLog_localGalois_smul` | same:58 | log equivariance |

Reuse: P2's finiteness/torsion side and P3's unit/transfer side can consume these
results. Caveat: these files use `NormedField.valuation` and `IsUltrametricDist`,
while Mathlib's `IsNonarchimedeanLocalField` uses `ValuativeRel.valuation`; a bridge
lemma `NormedField.valuation` ↔ `ValuativeRel.valuation` is needed before mixing them.

### 3.3 Kummer rigidity and normalized valuation

`LeanFormal/IUT/IUTII/Kummer/LocalFieldRigidity.lean`:

| Declaration | Line | Role |
|---|---|---|
| `fieldUnit_eq_one_of_roots` | 219 | `G_m` Kummer rigidity for a full nonarchimedean local field |
| `MultiplicativeKummerMap.injective_of_localField` | 253 | injectivity of a Kummer map with the standard kernel |
| `residuallyFinite_of_profinite` | 59 | compact totally disconnected ⇒ residually finite |
| private `localFieldUnitValuation` | 152 | normalized valuation `Fˣ →* Multiplicative ℤ` (not exported) |
| private `localFieldUnitValuation_eq_one_iff` | 161 | unit kernel (not exported) |

S2049 exposes the public version of the last two as `normalizedValuation` and
`normalizedValuation_eq_one_iff`, with attribution. This removes a real duplication
gap for P1/P2.

### 3.4 S2027/S2024/S2017/S2011/S2039 (abelian carrier and missing datum)

`tmp/sheaf/xif/paper/S2027LocalArtinActual.lean`:

| Declaration | Line | Role |
|---|---|---|
| `localField` | 178 | `FixedField U` |
| `localGaloisGroup` | 182 | `Gal(Qbar_p/L)` |
| `localGaloisGroupEquiv` | 192 | `U ≃* Gal(Qbar_p/L)` |
| `maximalAbelianExtension` | 212 | fixed field of the closed commutator |
| `galoisGroupMaximalAbelian` | 230 | `TopologicalAbelianization Gal(Qbar_p/L) ≃* Gal(L^ab/L)` |
| `le_maximalAbelianExtension_of_isAbelianGalois` | 250 | maximality |
| `mu` | 290 | `CommGroup.torsion L^×` |
| `muInGlobal` | 293 | injective map to global roots of unity |
| `mu_nontrivial` | 349 | μ(L) has at least 2 elements |
| `isOfFinOrder_norm` | 317 | norm of torsion is torsion |
| `unitProfiniteCompletion` | 396 | profinite completion of `L^×` |
| `localReciprocityIsomorphism` | 417 | exact M2a-core target |
| `localArtinTorsion` | 428 | exact P2 target |
| `localArtinTorsionTopological` | 434 | topological-carrier form |
| `LocalArtinSourceData` | 494 | fields `artin` and `carrier`; no inhabitant |
| `levelwiseEquiv` | 505 | from source data to `torsion(Ab U) ≃* μ(L)` |
| `localReciprocityData_of_source` | 512 | source data + transfer ⇒ `LocalReciprocityData` |
| `muQZComparison_of_source` | 527 | source data ⇒ S2017 comparison |
| `muHatComparison_of_source` | 536 | source data ⇒ S2017 comparison |

`tmp/sheaf/xif/paper/S2024LocalReciprocityActual.lean`:

| Declaration | Line | Role |
|---|---|---|
| `LocalReciprocityData` | 236 | structure with `equiv : ∀ U, torsion(Ab U) ≃* torsion(FixedField U)ˣ` and `transfer_compat` |
| `localReciprocityOnTorsion_of_data` | 249 | consumer |
| `muQZComparison_of_data` | 483 | consumer |
| `muHatComparison_of_data` | 547 | consumer |
| `localReciprocityDataMissing` | 556 | exact missing datum |

`tmp/sheaf/xif/paper/S2017VerlagerungActual.lean`: `verlagerungOpen` (227),
`muQZ` (257), `muHatZ` (333), `muQZComparison` (346), `muHatComparison` (339).

`tmp/sheaf/xif/paper/S2011Cor110bActual.lean`: `localReciprocityOnTorsion` (474),
`weakFrobeniusNormalization` (489).

`tmp/sheaf/xif/paper/S2039ActualPsiCnsInterface.lean`: `S2039FirstMissing` (17),
`S2039_muQZ_muHat_of_source` (23), `S2039_localArtinTorsion_of_source` (32).

### 3.5 Other tree material

`vendor/promachina/snapshots/1fa6387f.../Iut/SourceTrace/M1M3PaperLedger.lean` records
`SourceNonarchimedeanLocalFieldIntegers` with `ofFinitePlace`, `rationalPrime`, `localDegree`, `normalizedHaarMeasure`, `normalizedLogVolume`, and quotient modules.
It is a secondary donor for the local integer/Haar layer; it has no unramified/Artin
content. It is a snapshot, not a built dependency.

---

## 4. Donor inventory with exact APIs

### 4.1 LCFF (`local-class-field-theory`, Mathlib v4.32.0)

Path: `tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/local-class-field-theory/local-class-field-theory-main`.
Toolchain: Lean `v4.32.0`; Mathlib rev `81a5d257c8e410db227a6665ed08f64fea08e997`;
dependency `continuous-kummer-theory` rev `98b67dfe9c82415aa17caa633d93960b6829af2e`.
Source scan: 0 occurrences of `sorry`/`admit`/`native_decide`; no `.lake` directory and
no build artifact in this checkout. It was **not** compiled in this session.

Unramified/P1:

| Declaration | File:line | Statement / role |
|---|---|---|
| `PadicField.IsUnramified p K L` | `PadicField/Unramified.lean:31` | `e p K L = 1` |
| `PadicField.isUnramified_iff_f_eq` | same:43 | `e = 1 ↔ f = finrank` |
| `PadicField.adjoin_teichmullerSet_eq_top` | same:78 | unramified ⇒ generated by Teichmüller reps |
| `PadicField.maxUnramified p K Ω` | `PadicField/MaxUnramified.lean:114` | `⨆ n, unramifiedOfDegree p K Ω n` |
| `PadicField.frobUr p K Ω` | same:195 | arithmetic Frobenius in `Gal(K^ur/K)` |
| `PadicField.frobUr_apply` | same:199 | restriction to each finite level |
| `PadicField.dense_zpowers_frobUr` | same:281 | powers of Frobenius are dense |
| `PadicField.gal_maxUnramified_mul_comm` | same:301 | `Gal(K^ur/K)` is abelian |
| `PadicField.exists_restrict_eq` | same:312 | restriction to each finite level is surjective |
| `PadicField.urFix` | `PadicField/UnramifiedZHat.lean:41` | open normal subgroup fixing `K_n` |
| `PadicField.frobUr_pow_mem_urFix_iff` | same:71 | `Frob^k` fixes `K_n` iff `n ∣ k` |
| `PadicField.galMaxUnramifiedEquiv` | same:113 | `Gal(K^ur/K) ≃ₜ* Ẑ` |
| `PadicField.galMaxUnramifiedEquiv_frobUr` | same:128 | Frobenius ↦ `1` |
| `PadicField.galMaxUnramifiedEquiv_symm_apply` | same:124 | `a ↦ Frob^a` |

P2:

| Declaration | File:line | Role |
|---|---|---|
| `PadicField.maxAbelian` | `Reciprocity/Artin.lean:67` | maximal abelian extension |
| `PadicField.artin` | same:133 | `Kˣ →* Gal(K^ab/K)` |
| `PadicField.artin_apply` | same:150 | finite restriction formula |
| `PadicField.artin_apply_eq_self_iff` | same:157 | fixes `L` iff `x` is a norm |
| `PadicField.artin_injective` | `Reciprocity/ArtinInertia.lean:133` | injectivity |
| `PadicField.unitsInertiaEquiv` | same:246 | `𝒪ˣ ≃* inertia` |
| `PadicField.denseRange_artin` | same:261 | dense image |
| `PadicField.artinCompletionEquiv` | `Reciprocity/ProfiniteCompletion.lean:126` | `L^×-hat ≃ₜ* Gal(K^ab/K)` |
| `PadicField.artinCompletionEquiv_eta` | same:141 | `η x ↦ artin x` |

P3:

| Declaration | File:line | Role |
|---|---|---|
| `PadicField.normU` | `Reciprocity/NormCompat.lean:35` | `Units.map (Algebra.norm K)` |
| `PadicField.cycRec_baseChange` | same:277 | cyclic reciprocity under base change |
| `PadicField.abRec_baseChange` | same:391 | abelian reciprocity under base change |
| `PadicField.artin_baseChange` | same:416 | absolute Artin under base change |
| `PadicField.exists_abFin_le_norm` | `Reciprocity/NormLimitation.lean:135` | norm limitation step |
| `PadicField.existence` | `Reciprocity/ExistenceTheorem.lean:280` | local existence theorem |
| `PadicField.index_normGroup_eq_finrank` | same:286 | index of norm group = degree |
| `PadicField.le_iff_normGroup_le` | same:292 | inclusion of fields ↔ reverse inclusion of norm groups |
| `PadicField.existsUnique_normGroup_eq` | same:310 | unique norm group for each finite-index subgroup |

Porting LCFF is the shortest route to P1-P3, but it is not a drop-in: it is a separate
Mathlib pin and needs `continuous-kummer-theory` for the Brauer/duality layer. The
`PadicField` unramified layer (`Integers`, `Complete`, `Teichmuller`, `Unramified`,
`UnramifiedExistence`, `MaxUnramified`, `UnramifiedZHat`, `Galois/ZHat`) is the minimal
P1 set and does not obviously need the external Kummer package; that must be checked
file-by-file before porting.

### 4.2 TauCeti

Path: `tmp/TauCeti`. Toolchain: Lean `v4.36.0-rc1`; Mathlib rev `2cabef97b63d3275776b8b060d802de6a6fa1055`
(master at audit time). CI contract says no `sorry` and only standard axioms; not built
in this session.

| Declaration | File:line | Role |
|---|---|---|
| `TauCeti.maximalUnramifiedExtension` | `NumberTheory/LocalField/Unramified/Maximal.lean:97` | `L^ur = ⨆ f, unramifiedExtension K Ω f` |
| `TauCeti.maximalUnramifiedFrobenius` | same:378 | arithmetic Frobenius in `Gal(L^ur/L)` |
| `TauCeti.isGalois_maximalUnramifiedExtension` | same:250 | `L^ur/L` Galois |
| `TauCeti.topologicalClosure_zpowers_maximalUnramifiedFrobenius` | same:524 | Frobenius is a topological generator |
| `TauCeti.maximalUnramifiedGaloisGroupEquivZHat` | `NumberTheory/LocalField/Unramified/ZHat.lean:197` | `Gal(K^ur/K) ≃ₜ* Ẑ` |
| `TauCeti.maximalUnramifiedGaloisGroupEquivZHat_apply_frobenius` | same:219 | Frobenius ↦ `zHat.gen` |
| `TauCeti.not_isOfFinOrder_maximalUnramifiedFrobenius` | same:241 | Frobenius has infinite order |
| `TauCeti.ClassFieldTheory.artinMap` | `NumberTheory/ClassFieldTheory/Local/ArtinMap.lean:114` | `Kˣ →* G_K^ab` |
| `TauCeti.ClassFieldTheory.artinMap_restrict` | same:132 | finite restriction |
| `TauCeti.ClassFieldTheory.denseRange_artinMap` | same | dense image |
| `TauCeti.ClassFieldTheory.continuous_artinMap` | same | continuity |
| `TauCeti.ClassFieldTheory.localArtinMap_uniformizer` | `.../Local/Unramified.lean:342` | uniformizer ↦ Frobenius |
| `TauCeti.ClassFieldTheory.localArtinMap_eq_frobenius_pow_valuation` | same:354 | finite Artin = Frobenius^v |
| `TauCeti.ClassFieldTheory.localArtinMap_unit_of_unramified` | same:389 | units ↦ 1 |
| `TauCeti.ClassFieldTheory.unramifiedCoordinate_artinMap` | same:407 | unramified coordinate = normalized valuation |
| `TauCeti.ClassFieldTheory.mem_inertiaSubgroup_of_mk_eq_artinMap` | same:456 | unit Artin lies in inertia |
| `TauCeti.unitFiltration_le_normGroup_of_upperRamificationGroup_eq_bot` | `NumberTheory/LocalField/Norm/Surjectivity.lean:231` | norm limitation input |

TauCeti's naming and statement design are the best reference for the target API, but a
direct port to v4.32.2 is not realistic without adapting newer Mathlib lemmas. It is a
forward reference and a source of proof ideas, not a dependency.

### 4.3 Donor comparison

| Need | Mathlib v4.32.2 | tree | LCFF v4.32.0 | TauCeti v4.36 |
|---|---|---|---|---|
| `L^ur` object | no | no | yes | yes |
| `Gal(L^ur/L) ≃ Ẑ` | no | no | yes | yes |
| `rec_ur` | no | no | yes (via `artin`) | yes |
| `rec_L : L^× →* Gal(L^ab/L)` | no | only as `LocalArtinSourceData` field | yes | yes |
| `μ(L) ≃ torsion Gal(L^ab/L)` | no | exact Prop `localArtinTorsion` | yes | yes |
| norm limitation | no | no | `exists_abFin_le_norm` | `Norm/` + norm group API |
| local existence | no | no | `existence`, `existsUnique_normGroup_eq` | yes |
| transfer compatibility | no | `LocalReciprocityData.transfer_compat` (hypothesis) | `NormCompat` | `Norm/` |
| buildable in this workspace | yes | partial | no `.lake`; separate pin | no; newer toolchain |

---

## 5. Gap chain P1-P3

### 5.1 P1: maximal unramified extension and `Gal(L^ur/L) ≃ Ẑ`

**Exact formal target (this report).**

```lean
/-- Lur is the fixed field of the inertia subgroup of a valuation subring
of AlgebraicClosure L extending the valuation ring of L. -/
def IsMaximalUnramified (Lur : IntermediateField L (AlgebraicClosure L)) : Prop :=
  ∃ A : ValuationSubring (AlgebraicClosure L),
    (∀ x : L, algebraMap L (AlgebraicClosure L) x ∈ A ↔
      ValuativeRel.valuation L x ≤ 1) ∧
    Lur = IntermediateField.fixedField
      ((A.inertiaSubgroup L).map (A.decompositionSubgroup L).subtype)

structure UnramifiedGaloisData (L : Type u) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] where
  Lur : IntermediateField L (AlgebraicClosure L)
  isMaximalUnramified : IsMaximalUnramified L Lur
  galEquiv : Gal(Lur/L) ≃ₜ* Zhat

def P1ExactMissing : Prop := Nonempty (UnramifiedGaloisData L)
```

The predicate is a real characterization, not a free proposition: it uses
Mathlib's `ValuationSubring.inertiaSubgroup` and the fixed-field construction.
A future P1 construction can discharge it either by this inertia definition or by
proving the equivalence with the union-of-finite-unramified-extensions definition.

**Constructed in S2049 (no inhabitant of the structure).**

- `Zhat`, `zhatOfInt`, `denseRange_zhatOfInt`, `zhatGenerator`;
- `normalizedValuation`, `normalizedValuation_eq_one_iff`;
- `UnramifiedGaloisData.frobenius`, `.artin`, `.galEquiv_artin`, `.artin_unit`,
  `.artin_uniformizer`.

**Exact first missing mathematical object.** The structure fields `Lur`,
`isMaximalUnramified`, and `galEquiv`. More concretely, the missing chain is:

1. define `L^ur` inside `AlgebraicClosure L` as the union of finite unramified
   extensions (or the fixed field of the inertia subgroup of `Gal(Lbar/L)` for a chosen
   extension of the valuation);
2. prove `L^ur/L` is Galois and identify its finite Galois subextensions with finite
   unramified extensions;
3. construct the inverse system `Gal(L_n/L) ≅ ℤ/n` with Frobenius as a compatible
   generator;
4. take the limit and identify `Gal(L^ur/L)` with `ProfiniteCompletion.completion ℤ`;
5. prove Frobenius ↦ the topological generator.

**What Mathlib supplies toward this.** `arithFrobAt` gives step 3 at each finite level
once the ring action and finite residue field are set up; `Ideal.Quotient.stabilizerQuotientInertiaEquiv`
gives `Gal(L_n/L) ≅ Gal(κ_n/κ)`; `IsGaloisGroup.card_eq_finrank` and `Ideal.inertiaDeg`
give the degree; `InfiniteGalois.mulEquivToLimit` gives the limit identification for a
proved `IsGalois` extension. What Mathlib does **not** supply is the object `L^ur`, the
unramified finite-level specialization, and the Frobenius-compatibility proof across the
inverse system.

**Downstream use.** From an inhabitant `d : UnramifiedGaloisData L`, S2049 gives
`d.artin : L^× →* Gal(L^ur/L)` with `d.galEquiv (d.artin x) = zhatOfInt (v x)`; this is
the unramified local Artin map. It is not the full `rec_L`, and its image is only the
dense cyclic subgroup generated by Frobenius.

### 5.2 P2: cyclotomic/torsion identification

**Exact formal target (already in the tree).**

```lean
-- S2027LocalArtinActual.lean:428
def localArtinTorsion (p : Nat) [Fact (Nat.Prime p)] (U : Index p) : Prop :=
  Nonempty (mu p U ≃*
    CommGroup.torsion (Gal(maximalAbelianExtension p U / localField p U)))
```

The topological-carrier form `localArtinTorsionTopological` (line 434) is proved
equivalent to it by `localArtinTorsion_iff_topological` (line 438).

**Actual available.**

- `mu U = CommGroup.torsion (localField p U)ˣ` (S2027:290); `muInGlobal` injective
  (S2027:293/299); `mu_nontrivial` (S2027:349); `isOfFinOrder_norm` (S2027:317).
- `galoisGroupMaximalAbelian` (S2027:230) identifies the topological abelianization
  with `Gal(L^ab/L)`; `TopologicalAbelianization` and `InfiniteGalois.normalAutEquivQuotient`
  supply the group theory.
- `cyclotomicCharacter` (Mathlib) gives the action of a ring automorphism on roots of
  unity, including continuity on `Gal(L/K)`.
- The tree's `finite_integralUnitTorsion` (norm-based) proves torsion finiteness for the
  analytic integer ring, and `unitLogHom_ker_eq_torsion` identifies the log kernel with
  torsion. These are reusable for `mu(L)` after bridging the norm and `ValuativeRel`
  valuation rings.

**Exact first missing object.** A multiplicative map
`rec_L : L^× →* Gal(L^ab/L)` together with the theorem that on torsion it induces
`mu(L) ≃* torsion(Gal(L^ab/L))` and that the Galois action on roots of unity is the
cyclotomic character. Equivalently, an inhabitant of `LocalArtinSourceData` (S2027:494)
or of `S2039FirstMissing` (S2039:17).

**Why P1 does not give P2.** `Gal(L^ur/L) ≅ Ẑ` is torsion-free, so its torsion subgroup
is trivial. `mu(L)` is nontrivial (`mu_nontrivial`). The P2 torsion is the image of
`rec_L` on roots of unity, which lies in the inertia/cyclotomic direction of
`Gal(L^ab/L)`, not in the unramified quotient. P2 needs the cyclotomic character on the
Artin image and the norm/transfer side; P1 alone is insufficient.

**Route.** Port LCFF `Reciprocity/Artin.lean`, `Reciprocity/ArtinInertia.lean`, and the
Kummer/Brauer torsion identification (`Brauer/KummerH2`, `Brauer/H2ZHat`, `Duality/*`),
or TauCeti `ClassFieldTheory/Local/{ArtinMap,Unramified,Reciprocity}.lean`. The finite
Artin map `abRec` and the limit construction in LCFF `Reciprocity/Artin.lean` are the
closest match to S2027's `LocalArtinSourceData`.

### 5.3 P3: norm limitation, local existence, transfer compatibility

**Exact formal target.**

- norm limitation: for a finite abelian `L/K`, the norm group `N_{L/K}(L^×)` is the
  kernel of the finite Artin map (equivalently, the Artin map induces an isomorphism
  `K^×/N ≃* Gal(L/K)`);
- local existence: every finite-index open subgroup of `K^×` is a norm group;
- transfer compatibility: for `H ≤ K` open subgroups of `G_v`, the Verlagerung
  `V : (K^ab)_tors → (H^ab)_tors` corresponds to the inclusion of roots of unity of
  the fixed fields (S2024's `transfer_compat`).

**Actual available in the tree.**

- `verlagerungOpen` (S2017:227) constructs the Verlagerung on torsion;
- `LocalReciprocityData.transfer_compat` (S2024:236) is the exact hypothesis consumed
  by `localReciprocityData_of_source` (S2027:512);
- `isOfFinOrder_norm` (S2027:317) proves the norm of a root of unity is torsion;
- `muQZComparison_of_source` and `muHatComparison_of_source` (S2027:527/536) are the
  downstream consumers; `S2039_muQZ_muHat_of_source` packages them.

**Exact first missing object.** An inhabitant of `LocalReciprocityData` (equivalently, a
proof of `transfer_compat` from actual reciprocity), plus the norm limitation and local
existence theorems. No such inhabitant exists in Mathlib v4.32.2 or the tree.

**Route.** Port LCFF `Reciprocity/NormCompat.lean`, `Reciprocity/NormLimitation.lean`,
`Reciprocity/ExistenceTheorem.lean`; or TauCeti `NumberTheory/LocalField/Norm/*` and
`NumberTheory/ClassFieldTheory/Local/{Reciprocity,Restriction}.lean`. LCFF's
`exists_abFin_le_norm` and `existence` are the closest to the two missing theorems;
TauCeti's `unitFiltration_le_normGroup_of_upperRamificationGroup_eq_bot` is a more
modern norm-limitation input.

### 5.4 Dependency graph

```text
Mathlib v4.32.2: local field, valuation ring, residue field, finite Frobenius,
                norm, torsion, roots of unity, cyclotomic character,
                profinite completion, infinite Galois, topological abelianization
        |
        +--> S2049: Zhat, normalized valuation, unit kernel, P1 interface
        |         |
        |         +--> P1: L^ur + Gal(L^ur/L) ≃ Ẑ  [missing; port LCFF/TauCeti]
        |                   |
        |                   +--> rec_ur : L^× →* Gal(L^ur/L)  [constructed from P1]
        |
        +--> S2027: L^ab, TopologicalAbelianization, mu(L), norm, L^×-hat
                  |
                  +--> P2: mu(L) ≃ torsion Gal(L^ab/L)  [missing rec_L/cyclotomic]
                  |
                  +--> P3: norm limitation + existence + transfer  [missing; port donor]
```

P1, P2, P3 are independent leaves in this graph: P1 does not imply P2, and P2 does not
imply P3. P3 consumes P2's carrier plus norm theory.

---

## 6. S2049 Lean artifact

File: `tmp/sheaf/xif/paper/S2049LocalCFTInventory.lean`

- lines: 198; bytes: 9481;
- SHA256: `351D7C0977A3F2ABBE3CAD1B0B7717F79AE94CA3D8FF4B47FB3E61005B2C4097`;
- compile command: `lake env lean tmp/sheaf/xif/paper/S2049LocalCFTInventory.lean`;
- EXIT=0; no `sorry`, no `admit`, no `native_decide`, no new axiom;
- olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S2049LocalCFTInventory.olean`;
- olean bytes: 276344; olean SHA256: `94A147D5C662645EB79DB35125673ECD976827E46947CCA90CED088C38A4911B`.

Declarations:

| Declaration | Kind | Content |
|---|---|---|
| `Zhat` | abbrev | `ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))` |
| `zhatOfInt` | def | `Multiplicative ℤ →* Zhat` |
| `denseRange_zhatOfInt` | theorem | `DenseRange zhatOfInt` |
| `zhatGenerator` | def | `zhatOfInt (ofAdd 1)` |
| `normalizedValuation` | def | `Lˣ →* Multiplicative ℤ` |
| `normalizedValuation_eq_one_iff` | theorem | `v(u)=1 ↔ valuation L u = 1` |
| `IsMaximalUnramified` | def | fixed field of an inertia subgroup of a valuation subring extending `𝒪[L]` |
| `UnramifiedGaloisData` | structure | `Lur`, `isMaximalUnramified`, and `galEquiv : Gal(Lur/L) ≃ₜ* Zhat` |
| `UnramifiedGaloisData.frobenius` | def | preimage of the generator |
| `UnramifiedGaloisData.artin` | def | `Lˣ →* Gal(Lur/L)` |
| `UnramifiedGaloisData.galEquiv_artin` | theorem | defining square |
| `UnramifiedGaloisData.artin_unit` | theorem | integral units ↦ 1 |
| `UnramifiedGaloisData.artin_uniformizer` | theorem | normalized uniformizer ↦ Frobenius |
| `P1ExactMissing` | def | `Nonempty (UnramifiedGaloisData L)` |

Axiom probes (printed by the file): every listed theorem depends only on
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`.

### 6.1 What the artifact does and does not claim

Constructed: `Ẑ` as a profinite group, the dense map `ℤ → Ẑ`, the normalized valuation
and its unit kernel, and the formal unramified Artin map from any P1 inhabitant.

Not constructed / not claimed:

- no `Lur` value, no inhabitant of `UnramifiedGaloisData`;
- no proof that `Gal(L^ur/L) ≃ Ẑ` for any actual local field;
- no full local Artin map, no `μ(L) ≃ torsion Gal(L^ab/L)`;
- no norm limitation, local existence, or transfer compatibility;
- no P2/P3 inhabitant.

---

## 7. Verification ledger

Commands run in this session:

| Command | Result |
|---|---|
| `lake env lean tmp/sheaf/xif/paper/S2049LocalCFTInventory.lean` | EXIT=0; axiom probes printed standard triple |
| `lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2049LocalCFTInventory.olean tmp/sheaf/xif/paper/S2049LocalCFTInventory.lean` | EXIT=0; olean written; SHA256 above |
| source scan of LCFF for `sorry`/`admit`/`native_decide` | 0 matches |
| `Get-FileHash` on Lean and olean | SHA256 above |

Not run: full `lake build`, Project build, comparator, S2027/S2024 recompilation, donor
builds, independent review. Donor source was audited, not compiled.

Environment: `lean-toolchain` = `leanprover/lean4:v4.32.2`; Mathlib rev
`905b95818eb32af7874a58b427f50c1711a5e96c` (`v4.32.2`); workspace HEAD
`9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee`.

---

## 8. Concrete next steps for P1-P3

1. **P1, shortest path.** Port the LCFF `PadicField` unramified layer, not the whole
   CFT development: `Integers`, `Complete`, `Teichmuller`, `Uniformizer`, `Unramified`,
   `UnramifiedExistence`, `MaxUnramified`, `UnramifiedZHat`, and the `ZHat` files. Target
   an inhabitant of `UnramifiedGaloisData L`; S2049 then supplies `artin` and its
   normalization for free. If the port keeps LCFF's `PadicField`-specific API, define a
   bridge `PadicField → IsNonarchimedeanLocalField` first; do not mix the two valuation
   rings silently.
2. **P1, Mathlib-only alternative.** If porting is blocked, the minimal Mathlib path is:
   define `L^ur` as the fixed field of the inertia subgroup of `Gal(Lbar/L)` for a chosen
   extension of the valuation (Mathlib has `ValuationSubring.inertiaSubgroup`), prove its
   finite subextensions are unramified, and use `InfiniteGalois.mulEquivToLimit`; this
   still requires the valuation-extension uniqueness and the finite-level Frobenius
   compatibility, which are not in Mathlib. LCFF is more direct.
3. **P2.** After P1, port LCFF `Reciprocity/Artin.lean` and `Reciprocity/ArtinInertia.lean`;
   connect the resulting Artin map to S2027's `LocalArtinSourceData.artin` and
   `localArtinTorsion`. The target is already exactly stated; do not add a new Prop.
4. **P3.** Port LCFF `Reciprocity/NormCompat.lean`, `NormLimitation.lean`, and
   `ExistenceTheorem.lean`; feed `LocalReciprocityData.transfer_compat` and eliminate the
   remaining hypothesis in `localReciprocityData_of_source`.
5. **Do not** add `Nonempty`/`Prop` wrappers around the missing data, and do not call the
   S2049 interface a construction of the local Artin map. The only new inhabitant that
   would count is an actual `UnramifiedGaloisData` or `LocalReciprocityData` value.

---

## 9. Files and reports read

Mathlib: `NumberTheory/LocalField/Basic.lean`; `RingTheory/Valuation/{Integral,Extension,RamificationGroup}.lean`;
`NumberTheory/RamificationInertia/{Basic,Inertia,Ramification,Galois,HilbertTheory}.lean`;
`RingTheory/Invariant/Basic.lean`; `RingTheory/Frobenius.lean`; `RingTheory/Norm/Defs.lean`;
`RingTheory/RootsOfUnity/{Basic,PrimitiveRoots}.lean`; `GroupTheory/Torsion.lean`;
`NumberTheory/Cyclotomic/CyclotomicCharacter.lean`; `Topology/Algebra/Category/ProfiniteGrp/Completion.lean`;
`Topology/Algebra/Group/TopologicalAbelianization.lean`; `FieldTheory/AbsoluteGaloisGroup.lean`;
`FieldTheory/Galois/{Basic,Infinite,Profinite,IsGaloisGroup}.lean`.

Tree: `Iut/Foundations/SourceFiniteStageValuationDivisor.lean`;
`LeanFormal/IUT/Foundations/LocalFields/{IntegralUnits,IntegralUnitLogarithmTorsionFinite,IntegralUnitLogarithmKernel,IntegralLogShellIndexResidueFormula,IntegralLogShellRamificationInertia,IntegralUnitLogarithmGalois}.lean`;
`LeanFormal/IUT/IUTII/Kummer/LocalFieldRigidity.lean`;
`tmp/sheaf/xif/paper/{S2027LocalArtinActual,S2024LocalReciprocityActual,S2017VerlagerungActual,S2011Cor110bActual,S2039ActualPsiCnsInterface}.lean`;
reports `coord/reports/S2039-M2a-localArtin-exact.md`, `coord/reports/S2039-actual-psicns.md`,
`coord/reports/S2040-P1-unramified-artin-exact.md`, `coord/reports/S2040-P1-mathlib-missing-chain.md`.

Donors: LCFF checkout under `tmp/dsh-oct6-openai-math-survey-20261016/repos/lana/local-class-field-theory/local-class-field-theory-main`;
TauCeti under `tmp/TauCeti`; promachina snapshot `vendor/promachina/snapshots/1fa6387f.../`.

---

## 10. Bottom line

- Mathlib v4.32.2 has enough local-field and Galois infrastructure to state P1/P2/P3
  exactly and to prove the reductions, but not to construct the unramified or full local
  Artin map.
- The tree's S2027/S2024/S2017/S2011/S2039 already provide the abelian carrier and the
  exact missing datum for P2/P3. The tree's local analytic stack provides torsion
  finiteness and unit/log tools.
- P1 is exactly `Nonempty (UnramifiedGaloisData L)`; S2049 constructs the normalized
  valuation, `Ẑ`, the unramified Artin map from an inhabitant, and the normalization
  theorems, but no inhabitant.
- The shortest real path to P1-P3 is a port of the LCFF `PadicField`/`Reciprocity` files
  (Mathlib v4.32.0, no sorries), with TauCeti as the modern statement reference. No fake
  wrapper can replace that port.

`statement_compiles=true` for the S2049 Lean file; `proof_body_checked=true` for its
proved declarations (kernel-checked by `lake env lean`, standard axioms only);
`kernel_closed` for the S2049 file = true in the sense that it has no `sorry` and no new
axiom. The P1/P2/P3 targets remain uninhabited. `target_accepted=false`.
