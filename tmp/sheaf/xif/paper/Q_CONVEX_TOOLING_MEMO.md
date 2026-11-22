# Q memo: Mathlib convex geometry / Polytope / Ehrhart / Minkowski / Newton polytope / tropical against the paper Theta-pilot hull log

Date: 2026-10-30.
Status: research memo. No Lean theorem is claimed by this memo; no fake object, no target change.
Scope: `D:\lean` (LeanFormal), pinned Mathlib `v4.32.2` at commit
`905b95818eb32af7874a58b427f50c1711a5e96c`; LeanFormal commit
`9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee` (worktree has unrelated modifications).
Evidence probes (all three exit 0, logs beside them):
* `tmp/sheaf/xif/paper/Q_CONVEX_TOOLING_PROBE.lean` / `.log`
* `tmp/sheaf/xif/paper/Q_HULL_LOG_AXIOM_PROBE.lean` / `.log`
* `tmp/sheaf/xif/paper/Q_PADIC_COVOLUME_AXIOM_PROBE.lean` / `.log`

## 0. Verdict (TL;DR)

**No.** The fractional-lattice scaled region / hull log cannot be turned into a
convex-body volume with the tools in the pinned Mathlib, and doing so would not be
the paper-faithful operation. There are four independent obstructions:

1. **The formal "hull" is not a convex hull.** The project's product hull
   `LocalFieldProductHull.hull` is the intersection of all admissible
   multiplicative disc regions `region lam = lam . unitRegion`
   (`LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/LocalFieldProductHull.lean:37-40,137-138`).
   The root-theta hull `rootThetaHull` is the closure of a union of
   `Z_p`-fractional-lattice regions
   (`tmp/sheaf/xif/paper/RootHullContainmentInequalityActual.lean:65-79`).
   Neither is `convexHull` of a finite vertex set.
2. **No real/ordered scalar structure on the p-adic carrier.**
   `Convex` needs `[PartialOrder k]`; `ConvexBody` needs `[SMul Real V]`;
   `gauge` needs `[Module Real E]`. The carrier
   `ArithmeticTensorTupleBlock` is a finite-dimensional `Q_p`-vector space
   (`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTensorBlocks.lean:26`).
   The probe confirms that Mathlib cannot synthesize `PartialOrder Q_p`,
   `SMul Real Q_p`, `Module Real Q_p`, or `Algebra Real Q_p`; hence
   `Convex Q_p` does not even elaborate.
3. **The invariant is wrong.** The paper quantity is a normalized additive
   Haar log of a compact open `Z_p`-lattice region:
   `arithmeticTupleNormalizedLogVolume` is
   `(1 / finrank) * (log (mu S) - log (mu O_hol))`
   (`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedUnitScalingLogVolume.lean:92-98`),
   and the actual theorem
   `arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic`
   computes it as `-((sum c_i) * log p)` (`:379-390`).
   A real convex-body volume would be a Lebesgue volume of a bounded real set,
   not a p-adic Haar mass. Mathlib's `ZLattice.covolume` is real-only and is
   defined as the volume of a fundamental domain
   (`Mathlib/Algebra/Module/ZLattice/Covolume.lean:69-88`), not as the mass of a
   compact open p-adic lattice. There is no theorem in Mathlib or LeanFormal
   linking `ZLattice.covolume` to `arithmeticTupleNormalizedLogVolume`.
4. **The exact gap is a set/root-carrier obligation, not a volume computation.**
   `PaperRootHullFormulaGap` asks for scaling data plus
   `paperRootThetaHull = F(c) * O_hol`
   (`tmp/sheaf/xif/paper/BadPlacePaperRootThetaHullActual.lean:56-66`). Even a
   magical convex-volume identity for the right-hand side would not produce that
   set equality. Moreover the completion-carrier gap is impossible by the
   missing completion `2l`-root (S342), as recorded in
   `tmp/sheaf/xif/paper/PAPER_THETA_NORMALIZATION_STATUS.md:78-102`; do not chase it.

The project already has the correct p-adic "covolume" machinery, and it is
axiom-clean: `CompactOpenAddSubgroup.relative_log_measure_eq_log_indices`
(`LeanFormal/IUT/Foundations/MeasureTheory/CompactOpenAddSubgroupIndex.lean:80`)
computes the relative Haar log from the two compact-open intersection indices;
`FinitePlaceIntegralTensorCovolume.arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog`
(`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean:128`)
instantiates it, and `..._le_hull` (`:143`) compares it with the product hull.
These are the p-adic analogues of covolume; **no convex-body volume is needed or
available**.

The only convex-hull route aimed at a paper-level hull log in LeanFormal is a **conditional card** for a
different, sup-type "volume": `SourceHullConvexVertexData`
(`LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullVertexConvexityAssembly.lean:187-211`)
and its consumers `sourceHullVolume_le_vertices_of_convexVertexData` (`:217`) /
`sourceHullVolume_eq_vertices_of_convexVertexData` (`:277`). The file's own audit
note says no datum of this shape is constructed, the direct convexity of
`sourceLocalLogDegree` is unstatable because `ThetaPilotPoint` is a
multiplicative value monoid with no `Real`-module structure, and the paper does
not claim a convex-hull identification of the holomorphic hull
(`:291-321`). This is a rejection, not a tool.

## 1. The actual formal objects (so the comparison is not fake)

### 1.1 p-adic fractional lattice and its Haar log

* `ArithmeticTensorTupleBlock places tuple := FinitePadicTensor (fun i => CommonPrimeCompletion (places i (tuple i)))`
  (`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTensorBlocks.lean:26-27`).
  It is a finite-dimensional `Q_p`-vector space, not a real vector space.
* `arithmeticTupleHolomorphicLattice` is the integral closure `Z_p`-submodule
  (`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedUnitScalingLogVolume.lean:75-79`);
  its carrier is the canonical unit reference `O_hol`.
* `arithmeticTupleNormalizedLogVolume` is the degree-normalized Haar log
  (`:89-98`).
* `ArithmeticTuplePureFractionalScalingData c` supplies local generators of norm
  `p^(-c_i)`, a common exponent, and the pure-tensor action on `O_hol`
  (`:125-153`).
* Actual theorem:
  `arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic`
  (`:379-390`) states
  `mu_log (F(c) * O_hol) = -((sum_i c_i) * log p)`.
  The probe `Q_HULL_LOG_AXIOM_PROBE.lean` prints its axioms as exactly
  `[propext, Classical.choice, Quot.sound]`; this is actual, not an interface.
* The hull:
  `rootThetaRegion j = F(j^2 * c_root) * O_hol`;
  `rootThetaHull = closure (union_j rootThetaRegion j)`;
  `rootThetaHullLog = arithmeticTupleNormalizedLogVolume mu rootThetaHull`
  (`tmp/sheaf/xif/paper/RootHullContainmentInequalityActual.lean:65-79,117-120`).
  This is a closure of a union of lattice regions, not a `convexHull`.
* Completion-carrier paper gap:
  `paperRootThetaHull`, `paperRootThetaHullLog`, `paperRootThetaFormulaLog`,
  and `PaperRootHullFormulaGap` are in
  `tmp/sheaf/xif/paper/BadPlacePaperRootThetaHullActual.lean:40-66`;
  the conditional formula is `:68-80`.
  But `PaperRootHullFormulaGap` requires a completion generator of norm
  `p^(-order/(2l))`, i.e. a completion `2l`-root of `q[1u]`, which is impossible
  by S342 (`PAPER_THETA_NORMALIZATION_STATUS.md:78-102`). The ledger already lists
  it under "EXACT but completed/obsolete (do not chase)"
  (`tmp/sheaf/xif/paper/TASK_LEDGER.md:96-102`).
* Current paper-faithful log:
  `paperPerBThetaHullLog := perBThetaHullLog` (a definition), and the theorem
  `paperPerBThetaHullLog_eq_rootNormHullLog` identifies it with
  `rootThetaHullLog rootHalfCoefficient`
  (`tmp/sheaf/xif/paper/S716PaperThetaHullLogSourceAuditActual.lean:46-57`);
  it is nonpositive (S726, `:47-56`). The signed-hull input used by S733 is
  `S733CorrectedHullLog P := P.signedHullLogVolume = -paperPerBThetaHullLog`
  (`tmp/sheaf/xif/paper/S733CorrectedPaperFinalCor312Actual.lean:45-47`), and
  S729 constructs `paperSignedHullActual` with that signed log
  (`tmp/sheaf/xif/paper/S729PaperSignedHullActualHullLogActual.lean:91-116`).
  None of this is a convex-body volume computation.

### 1.2 The product hull is not a convex hull

* `LocalFieldProductHull.unitRegion := {x | forall i, ||x i|| <= 1}`
  (`LocalFieldProductHull.lean:37`).
* `region lam := {x | forall i, ||x i|| <= ||lam i||}`
  (`:40`), and `region lam = lam . unitRegion` for nonzero `lam` (`:44-59`).
* `hull S := {x | forall lam, (forall i, lam i != 0) -> S subset region lam -> x in region lam}`
  (`:137-138`): the **intersection of all admissible multiplicative disc regions**.
  This is the paper's `lambda * O` hull, not `convexHull`.
* Key actual theorems: `hull_minimal` (`:143`), `hull_region` (`:150`),
  `hull_idempotent` (`:154`), `exists_hull_eq_region` (`:162`),
  `hull_closure` (`:172`), `measure_hull_pos_lt_top` (`:234`),
  `normalizedLogVolume_le_hull` (`:269`).
* `arithmeticTupleHullUnitLogVolume` is the normalized log of
  `hull (arithmeticTupleFieldLogImage ...)`, with actual existence/uniqueness
  and nonnegativity:
  `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTupleHullVolume.lean:24-31,60-77,79-96`.
  Again: product hull, not convex body.

## 2. Mathlib inventory (exact names, signatures, applicability)

The probe `Q_CONVEX_TOOLING_PROBE.lean` compiled with exit 0. The signatures below
are copied from its output.

### 2.1 Convex sets, convex hulls, gauges

| Name | File:line | Signature / content | Verdict for the paper hull log |
|---|---|---|---|
| `Convex` | `Mathlib/Analysis/Convex/Basic.lean:52` | `[Semiring k] [PartialOrder k] [AddCommMonoid E] [SMul k E]` | Reject: `Q_p` has no `PartialOrder` (probe). |
| `convexHull` | `Mathlib/Analysis/Convex/Hull.lean:46` | `[Semiring k] [PartialOrder k] [AddCommMonoid E] [Module k E]`, `ClosureOperator (Set E)` | Reject: the formal hull is `LocalFieldProductHull.hull` / closure of a lattice union, not `convexHull`. |
| `mem_convexHull_iff` | `.../Hull.lean:60` | membership via all convex supersets | Reject: no real module on the carrier. |
| `Convex.add` | `.../Basic.lean:190` | Minkowski sum of convex sets | Reject: no `Convex Q_p`; and Minkowski sum of lattice regions is not the paper operation. |
| `Convex.smul` | `.../Basic.lean:409` | scalar dilation of a convex set | Reject: same. |
| `ConvexBody` | `Mathlib/Analysis/Convex/Body.lean:44` | structure with `carrier`, `convex' : Convex Real carrier`, `isCompact'`, `nonempty'`; typeclass `[TopologicalSpace V] [AddCommMonoid V] [SMul Real V]` | Reject: no `SMul Real` on `Q_p` (probe). No generic `ConvexBody.volume`; the file's TODO says positive convex bodies and support sets are not defined (`:22-27`). |
| `ConvexBody.convex` / `ConvexBody.isCompact` | `.../Body.lean:69,72` | only structural projections | Reject: no instance; no measure theorem. |
| `convexBodyLT_volume` | `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/ConvexBody.lean:96` | volume of a specific product of real/complex balls: `volume (convexBodyLT K f) = convexBodyLTFactor K * prod w, (f w) ^ mult w` | Reject: number-field/real-specific ball-product formula; not the p-adic lattice region and not a general convex-body volume API. |
| `gauge` | `Mathlib/Analysis/Convex/Gauge.lean:56` | Minkowski functional, `[AddCommGroup E] [Module Real E]` | Reject: no real module; no volume. |
| `gaugeSeminorm` | `.../Gauge.lean:495` | seminorm from balanced convex absorbent real set | Reject: same. |
| `Convex.addHaar_frontier` | `Mathlib/Analysis/Convex/Measure.lean:35` | `mu (frontier s) = 0` for real finite-dimensional convex `s` | Reject for computation: only null frontier, no volume formula. |
| `Convex.nullMeasurableSet` | `.../Measure.lean:86` | convex real set is null measurable | Reject: measurability only. |
| `stdSimplex` | `Mathlib/Analysis/Convex/StdSimplex.lean:35` | standard simplex in `i -> k` | Reject: no general polytope, no volume/Ehrhart. |
| `IsSimplicial` | `Mathlib/Geometry/Convex/Cone/Simplicial.lean:43` | simplicial cone predicate | Reject: cones/fans, not the compact-open lattice region. |

### 2.2 Polytopes, Ehrhart, lattice-point counts

| Candidate | Status in pinned Mathlib | Verdict |
|---|---|---|
| `Polytope` | **No declaration.** `#check_failure Polytope` reports `Unknown identifier`; grep 0. The closest is `Convex.exists_subset_interior_convexHull_finset_of_isCompact` (`Mathlib/Analysis/Normed/Affine/Convex.lean:96`), which uses `convexHull Real u` of a `Finset` and calls it a "convex polytope" only in a docstring. | Reject: no vertex/facet API, no polytope volume. |
| `Ehrhart` | **No declaration.** `#check_failure Ehrhart` reports `Unknown identifier`; grep 0 in Mathlib and LeanFormal. GitHub PR search for "Ehrhart" in mathlib4 titles: 0 results (2026-10-30). | Reject: absent; and Ehrhart counts lattice points / leading covolume, not the fixed Haar log. No dilation parameter `t` in the target. |
| `ZLattice.covolume.tendsto_card_div_pow` | `Mathlib/Algebra/Module/ZLattice/Covolume.lean:311` | Only an asymptotic lattice-point count in a real `Z`-lattice: `#(s inter n^{-1} L) / n^d -> volume s / covolume L`. | Reject: asymptotic, real, and not the paper's exact finite Haar log. |
| `Polytope`/Ehrhart literature | Beck-Robins, *Computing the Continuous Discretely*; standard Ehrhart quasi-polynomial theory. | Not formalized in this checkout; not needed for a fixed Haar log. |

### 2.3 Minkowski / covolume / real Haar scaling

| Name | File:line | Signature / content | Verdict |
|---|---|---|---|
| `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` | `Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean:65` | Minkowski convex body theorem: a symmetric convex real set of large enough volume contains a nonzero lattice point | Reject: existence of a lattice point, not a volume identity. |
| `ZLattice.covolume` | `Mathlib/Algebra/Module/ZLattice/Covolume.lean:72` | covolume of a real `Z`-lattice as the volume of a fundamental domain | Reject: real-only; not the p-adic Haar mass. |
| `ZLattice.covolume_eq_measure_fundamentalDomain` | `.../Covolume.lean:84` | `covolume L mu = mu.real F` for a fundamental domain `F` | Reject: requires a real fundamental domain; the paper hull is not one. |
| `ZLattice.covolume_eq_det` | `.../Covolume.lean:125` | `covolume L volume = abs (det (basis matrix))` | Auxiliary only: computes a real determinant/covolume; no p-adic bridge. |
| `ZLattice.covolume_div_covolume_eq_relIndex` | `.../Covolume.lean:147` | `covolume L1 / covolume L2 = relIndex L1 L2` for `L1 <= L2` | Reject as a direct conversion: real covolume ratio is the **index**, while p-adic normalized Haar of the smaller lattice is the **inverse** index; the sign/normalization is opposite unless one explicitly reciprocates. |
| `ZLattice.volume_image_eq_volume_div_covolume` | `.../Covolume.lean:184` | volume of a linear image in coordinates = `volume s / covolume L` | Reject: real coordinate model; no p-adic identification. |
| `MeasureTheory.Measure.addHaar_smul` | `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:362` | `mu (r . s) = ofReal (abs (r ^ d)) * mu s` for real `r` | Reject: real scaling direction. |
| `MeasureTheory.Measure.addHaar_submodule` | `.../EqHaar.lean:172` | a strict real submodule has Haar measure 0 | Reject: in a real model the lattice is measure zero; the positive mass lives on a fundamental domain, not on the lattice. |

The real/p-adic scaling directions are opposite:
* real: `mu (r . s) = |r|^d * mu s` (`addHaar_smul`);
* p-adic: `mu (p . S) = (p^d)^{-1} * mu S`
  (`LeanFormal/IUT/Foundations/LocalFields/FinitePadicHaarScaling.lean:25-27`).
Mapping the p-adic `p` to a real `p` without an explicit reciprocal convention
produces the reciprocal scalar. This is a mathematical mismatch, not a missing
library lemma.

### 2.4 Newton polytope / tropical / toric

| Candidate | Status | Verdict |
|---|---|---|
| `NewtonPolygon` / `NewtonPolytope` | **No declaration in the pinned Mathlib.** `#check_failure NewtonPolygon` and `#check_failure NewtonPolytope` report `Unknown identifier`; grep 0. Upstream PR #38050 ("feat: Define Newton polygons", open, not merged in v4.32.2) defines p-adic Newton polygons as slope/length sequences, not convex Newton polytopes: <https://github.com/leanprover-community/mathlib4/pull/38050>. | Reject: not available; and a Newton polygon/polytope is the convex hull of exponent vectors of a polynomial, not the Theta hull. |
| `Tropical` | Only tropical algebra: `Mathlib/Algebra/Tropical/Basic.lean`, `Lattice.lean`, `BigOperators.lean`; `Tropical`, `Tropical.trop`, `Tropical.untrop` are present. | Reject: no tropical geometry, no tropicalization of varieties, no Newton/tropical correspondence. |
| Toric geometry | No `Mathlib/AlgebraicGeometry/Toric` directory; only convex cones (`Geometry/Convex/Cone/*`). `DualFinite.lean:21` mentions Minkowski-Weyl in a docstring. | Reject: no toric variety, fan, moment polytope, or toric volume. The Theta hull has no torus action. |

### 2.5 What the probe proved

`Q_CONVEX_TOOLING_PROBE.lean` (exit 0) confirms:
* all names/signatures in sections 2.1-2.3 elaborate;
* `#check_failure Polytope`, `Ehrhart`, `NewtonPolygon`, `NewtonPolytope` succeed
  (i.e. the identifiers are absent);
* `PartialOrder Q_p`, `SMul Real Q_p`, `Module Real Q_p`, `Algebra Real Q_p`,
  and `Convex Q_p Set.univ` all fail instance synthesis (as expected).
So the rejection is not a guess from filenames; it is checked in the pinned
environment.

## 3. The exact gaps and why convex volume cannot fill them

### 3.1 `PaperRootHullFormulaGap` (do not chase)

`PaperRootHullFormulaGap T b` contains:
* `data : ArithmeticTuplePureFractionalScalingData ... (paperRootCoefficientFamily T b)`;
* `hull_eq : paperRootThetaHull T b = F(paperRootCoefficientFamily T b) * O_hol`.

The formula then follows from the actual Haar theorem. The gap is a set equality
plus completion scaling data. The completion scaling data is impossible by S342
(`PAPER_THETA_NORMALIZATION_STATUS.md:78-102`), and the ledger marks the gap
obsolete (`TASK_LEDGER.md:96-102`). Convex geometry cannot supply either the
completion root or the p-adic set equality; a convex-volume identity for
`F(c) * O_hol` would still not prove `paperRootThetaHull = F(c) * O_hol`.

### 3.2 Current paper-faithful hull log

The current object is
`paperPerBThetaHullLog = rootThetaHullLog rootHalfCoefficient`
(`S716PaperThetaHullLogSourceAuditActual.lean:46-57`), the normalized Haar log of
`rootNormHull`; it is actual as a definition and nonpositive (S726). The signed
hull input is `S733CorrectedHullLog`, and S729 constructs an actual
`PaperSignedHull` with the matching signed log. These are Haar/log and
signed-hull statements; there is no convex-body volume in the chain.

### 3.3 The ledger's current paper hull equality

The ledger lists as exact missing:
* qPilot -> product hull comparison/containment on `RootExtensionProductCarrier`
  (`TASK_LEDGER.md:88`);
* paper hull equality `rootExtensionProductImageHull = paper holomorphic/lambda-O hull`
  (or actual log/measure equality) (`TASK_LEDGER.md:90`).
Both are set/containment or measure/log identities on p-adic/extension carriers.
Convex geometry has no theorem that proves a set equality of a p-adic lattice
region with a product hull; `convexHull` is a different operation.

### 3.4 `PaperHullVsS663ThetaAverageGap` is false

`paperPerBThetaHullLog = rootThetaMagnitudeProcession.average` is refuted:
the left side is `<= 0`, the right side is `> 0`
(`tmp/sheaf/xif/paper/S726PaperHullVsS663GapActual.lean:47-99`). Convexity
cannot repair a false equality; do not use this gap.

## 4. The project's existing convex-hull card (why it is not a solution)

`ConvexHullVertexSupReduction.iSup_ofReal_le_iSup_vertices_of_subset_convexHull`
(`LeanFormal/IUT/Foundations/Geometry/ConvexHullVertexSupReduction.lean:55-64`)
is actual and reusable **for sup-type volumes**:
if `S subset convexHull Real t` and `f` is convex on that convex hull, then
`iSup_{x in S} ofReal (f x) <= iSup_{i in t} ofReal (f i)`.
The equality form is `convexHull_iSup_ofReal_eq_iSup_vertices` (`:70-80`).

This is the mathlib-level maximum principle. It does **not** compute a Haar
measure or a convex-body volume. It is consumed by:

* `SourceHullConvexVertexData` (`HullVertexConvexityAssembly.lean:187-211`),
  a structure containing a real vector space `E`, a map `toE` from
  `ThetaPilotPoint`, a convex `g`, a finite vertex list, and the hypotheses
  `hull_image_subset_convexHull`, `convexOn_g`, `g_eq_logDegree_on_hull`,
  `g_le_logDegree_on_vertices`;
* `sourceHullVolume_le_vertices_of_convexVertexData` (`:217-256`) and
  `sourceHullVolume_eq_vertices_of_convexVertexData` (`:277-284`).

The audit note in the same file (`:291-321`) states explicitly:
* no datum of this shape is constructed anywhere in the tree;
* `ThetaPilotPoint` is a multiplicative value monoid, `sourceLocalLogDegree` is
  additive over `*` (`SourceImageHullVolume.lean:115-124`), and there is no
  `Real`-module structure to state convexity against;
* the paper claims no convex-hull identification of the holomorphic hull; the
  card is exactly that named gap.

Moreover, the "volume" here is sup-type:
`sourceSetVolume v S = iSup_{x in S} ofReal (sourceLocalLogDegree v x)`
(`SourceImageHullVolume.lean:188-195`), not the Haar measure
`arithmeticTupleNormalizedLogVolume`. So even a completed convexity card would
not compute `paperPerBThetaHullLog`.

`SourceOneCircUGeometry` (`LeanFormal/IUT/IUTIII/Theorem311/SourceOneCircUGeometry.lean:113-136`)
is the only place with an actual real normed space and `hull = closure (convexHull Real oneCircU)`
(`:147-150`); its header (`:37-53`) states it is a model, not the paper object
("no Haar measure", "hull is the topological closed convex hull, not the
arithmetic holomorphic hull", "not the paper's `1,circ U`"). It cannot be used as
a paper-faithful bridge.

## 5. The actual p-adic covolume/log tools to use instead

These are the ready-made tools that do the intended job at the correct level.

| Name | File:line | What it gives | Status |
|---|---|---|---|
| `intersectionIndex` | `LeanFormal/IUT/Foundations/MeasureTheory/CompactOpenAddSubgroupIndex.lean:25` | `Nat.card (H / (H inter K))` for additive subgroups | actual |
| `measure_eq_index_mul_intersection` | `.../CompactOpenAddSubgroupIndex.lean:46-49` | `mu H = index H K * mu (H inter K)` | actual |
| `relative_log_measure_eq_log_indices` | `.../CompactOpenAddSubgroupIndex.lean:80-102` | `log (mu H) - log (mu K) = log (index H K) - log (index K H)` for compact open `H,K` | actual, axioms `[propext, Classical.choice, Quot.sound]` (probe) |
| `arithmeticTupleLogTensorUnitLogVolume` | `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean:92-94` | log index difference for integral log-tensor lattice vs holomorphic lattice | actual |
| `arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog` | `.../FinitePlaceIntegralTensorCovolume.lean:128-141` | equals the relative Haar log | actual, axiom-clean (probe) |
| `arithmeticTupleLogTensorUnitLogVolume_le_hull` | `.../FinitePlaceIntegralTensorCovolume.lean:143-155` | lattice log <= product hull log | actual, axiom-clean (probe) |
| `arithmeticTupleLogTensorUnitLogVolume_eq_fieldLogVolume` | `.../FinitePlaceIntegralTensorCovolume.lean:157-184` | field-product normalized log transport | actual, axiom-clean (probe) |
| `arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic` | `LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedUnitScalingLogVolume.lean:379-390` | exact `- (sum c_i) log p` for `F(c) * O_hol` | actual, axiom-clean (probe) |
| `measure_prime_smul_finiteDimensional` | `LeanFormal/IUT/Foundations/LocalFields/FinitePadicHaarScaling.lean:25-27` | p-adic Haar p-scaling `p^{-d}` | actual |
| `log_measure_prime_smul_finiteDimensional` | `.../FinitePadicHaarScaling.lean:54-58` | log form of the same | actual |

This is the honest "covolume" analogue: compact-open index and Haar scaling, not
a convex body. The term "covolume" in LeanFormal is already used for this
(`FinitePlaceIntegralTensorCovolume.lean`), and it is independent of Mathlib's
real `ZLattice.covolume`.

## 6. Candidate reductions and final applicability table

| Reduction | What it would need | Mathlib support | Verdict |
|---|---|---|---|
| R1: take the convex hull of the fractional-lattice region and compute its volume | a real vector space/order on the p-adic carrier, a proof `rootThetaHull = convexHull ...` | `convexHull`, `ConvexBody` only over real/ordered scalars | **Reject.** No `PartialOrder Q_p`/`SMul Real Q_p`; the formal hull is not a convex hull; the convex hull of a spanning lattice in a real model is the whole ambient space, not a finite-volume body. |
| R2: use `ZLattice.covolume`/`covolume_eq_det` on a real lattice model | a real `Z`-lattice and an identification of its covolume with the p-adic Haar normalization | `ZLattice.covolume*` (real only) | **Reject for the exact gap; auxiliary only.** No p-adic/real bridge; covolume is the volume of a fundamental domain, while the paper log is a Haar/index log. |
| R3: Ehrhart/quasi-polynomial of a rational polytope | a rational polytope, a lattice, an integer dilation `t` | **absent** in Mathlib; no `Ehrhart` declaration | **Reject.** Wrong invariant (lattice-point count/leading covolume vs fixed Haar log); no `t` in the target. |
| R4: Newton polytope / tropical / toric | a polynomial or torus action/moment map; a Newton polytope volume | `NewtonPolygon` absent (open PR #38050 is p-adic slopes, not merged); tropical only algebra; no toric geometry | **Reject.** Wrong geometry; no formal objects; the Theta hull has no torus action. |
| R5: existing `SourceHullConvexVertexData` card | an actual real model, convex `g`, hull ⊆ convex hull of vertices | generic maximum principle `iSup_ofReal_le_iSup_vertices_of_subset_convexHull` | **Reject for the exact gap.** Card not constructed; `ThetaPilotPoint` has no `Real`-module; it concerns sup-type `sourceHullVolume`, not the Haar log. |
| R6: actual p-adic compact-open index/Haar route | compact open lattices, Haar scaling, the existing fractional-lattice scaling data | `relative_log_measure_eq_log_indices`, `measure_prime_smul_finiteDimensional`, `arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic` | **Use this.** Actual and axiom-clean; it computes the scalar exactly, without convexity. It still does not prove the paper hull equality; that is a separate set/root-carrier obligation. |

## 7. Exact answers to the task question

1. **Can the fractional-lattice scaled region/hull log be turned into a convex-body
   volume with Mathlib?** No. `Convex`/`ConvexBody`/`gauge` need real/ordered
   scalars; `Q_p` has neither. `ZLattice.covolume` is real-only and fundamental-
   domain based; there is no p-adic/real bridge. `Polytope`, `Ehrhart`,
   `NewtonPolytope`, and tropical geometry are absent. The project's "hull" is
   `LocalFieldProductHull.hull`, not `convexHull`.
2. **Is there any usable Mathlib theorem for the exact gap?** Not for the gap
   itself. The only reusable convexity theorem is the sup-type maximum principle
   `iSup_ofReal_le_iSup_vertices_of_subset_convexHull`, and its existing consumer
   is a conditional card for a different volume. It cannot prove
   `paperRootThetaHull = F(c) * O_hol`, the paper hull equality, or the
   qPilot/product-hull containment.
3. **What should be used instead?** The actual p-adic tools:
   `relative_log_measure_eq_log_indices`,
   `arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog`,
   `arithmeticTupleLogTensorUnitLogVolume_le_hull`,
   `arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic`,
   `measure_prime_smul_finiteDimensional`, and for the paper-level hull log
   `paperPerBThetaHullLog = rootThetaHullLog rootHalfCoefficient`.
   For `q[2u]`/root stack, keep `rootNormedElement`,
   `rootNormedExtension`, `rootNormedThetaValueInL`
   (`tmp/sheaf/xif/paper/PaperRootCompletionTensorActual.lean:54-60,72-75,143-149`)
   and the S709 closed form
   (`tmp/sheaf/xif/paper/S709RootImageRadiusFormulaActual.lean:145`);
   convex geometry has no bearing on these.
4. **Do not chase `PaperRootHullFormulaGap`.** It is a completion-carrier
   obstruction (S342), already marked obsolete in the ledger. A convexity card
   would not fix the missing `2l`-root.

## 8. Evidence / versions / probes

* Mathlib: `v4.32.2`, commit `905b95818eb32af7874a58b427f50c1711a5e96c`;
  source at `D:\lean\.lake\packages\mathlib\Mathlib`.
* LeanFormal: commit `9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee`; worktree
  modifications are unrelated to this memo.
* `Q_CONVEX_TOOLING_PROBE.lean`: imports the relevant Mathlib modules; exit 0;
  output in `Q_CONVEX_TOOLING_PROBE.log`. It prints the signatures and the
  absent-identifier/instance failures quoted above.
* `Q_HULL_LOG_AXIOM_PROBE.lean`: exit 0; `#print axioms` for
  `arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic` and
  `..._le_of_subset_fractionalLattice_mul` both `[propext, Classical.choice,
  Quot.sound]`.
* `Q_PADIC_COVOLUME_AXIOM_PROBE.lean`: exit 0; `#print axioms` for
  `relative_log_measure_eq_log_indices`,
  `arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog`,
  `..._le_hull`, and `..._eq_fieldLogVolume` all `[propext,
  Classical.choice, Quot.sound]`.
* Upstream status checked 2026-10-30: mathlib4 PR #38050 "feat: Define Newton
  polygons" is open, not merged; GitHub title search for "Ehrhart" in mathlib4
  returns 0. These are external facts, not used as proof.

## 9. Recommendation

Do not add Mathlib convex geometry, polytope, Ehrhart, Newton-polytope, tropical,
or toric imports to the paper-faithful chain. Keep the existing p-adic Haar/index
route. If a convexity route is ever pursued for a *different* sup-type volume, the
only honest precondition is an actual `SourceHullConvexVertexData` (real vector
space, convex `g`, hull ⊆ convex hull of vertices) with a paper-faithful
identification of the carrier; that datum is not in the tree, is not supplied by
Mathlib, and is not claimed by the paper. No fake convex-body volume, no target
change.
