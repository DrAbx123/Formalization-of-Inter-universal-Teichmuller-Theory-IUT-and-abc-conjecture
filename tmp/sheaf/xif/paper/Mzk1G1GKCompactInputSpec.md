# SPEC — G-K `GKCompactInput` (route §7.3 L671–705): fields vs existing declarations / gaps

Owner: henry (design). Target structure (already in `Mzk1G1DisjointFamilyActual`):

```lean
structure GKCompactInput (n r : ℕ) where
  X : Type                       -- the local tuple space
  top : TopologicalSpace X
  comp : CompactSpace X
  non : Nonempty X
  delta : Fin (r + 1) → X → ℝ    -- boundary-distance function of the i-th map
  delta_cont : ∀ i, Continuous (delta i)
  delta_cover : ∀ x, ∃ i, 0 < delta i x
```
and `GKCompactInput.exists_delta0` (DONE, `Mzk1G1DisjointFamilyActual`) already yields
`∃ δ₀ > 0, ∀ x, ∃ i, δ₀ ≤ delta i x` from compactness (via `uniform_positive_away`).
So the only missing content is the **inhabitant**: X, its compact topology, and the δ_i.

Route §7.3 prescribes: X = ∏_{v∈V} (Y_n(L_v))^d; for ξ ∈ X,
δ_i(ξ) = min_{v,k} dist_chordal(φ_i(ξ_{v,k}), {0,1,∞});  δ_cover holds because a tuple
has at most r points and (E1) some φ_i avoids them all; compactness gives a fixed δ₀.

## Field → existing declaration / gap table

| field | intended definition | existing DONE declarations | gap |
|---|---|---|---|
| `L_v` (local fields) | v = ∞: ℂ; v = p: finite normal L_p ⊇ all degree ≤ d extensions of ℚ_p | `Mzk1G1DisjointFamilyActual.UniversalLocalFieldExists p d` (statement only) · `ContainsBoundedExtensions` · `G1KvCompactActual.KvData/InKv/localValueSet_isCompact` · alan's `Mzk1G1UniversalAnalyticInputActual` (root-near/Krasner, partial §7.2) | **big gap**: producer of `UniversalLocalFieldExists p d` (alan, in progress) |
| `X` | `∏ v ∈ V, (Y_n(L_v))^d` | `fermatCurveScheme n` (G-A DONE) · `fermatCurveToSpec` · `fermatCurveToSpec_isProper_final` (grace, IsProper) | **gap**: no type of L_v-points of a scheme in the repo (`Scheme` points over a field are homs `Spec L_v ⟶ Y_n`; a concrete topological model is needed) |
| `top` (topology on `Y_n(L_v)`) | archimedean v: complex topology on the closed projective plane model; finite v: v-adic topology | Mathlib: `TopologicalSpace (Spec R)` (Zariski, not analytic) · `Padic`/`Valued` machinery (Mathlib) · no `ℂℙ²`-with-complex-topology in the repo | **big gap** (both cases): analytic/v-adic topology on L_v-points of the curve, and compactness of the projective plane model over L_v. This is the single largest missing piece of §7.3 |
| `comp` (`CompactSpace X`) | finite product of compact spaces: `Y_n(ℂ)` compact (closed subset of ℂℙ², normalized charts + compact unit balls), `Y_n(L_p)` compact (closed subset of ℙ²(L_p), compact) | Mathlib: `isCompact_univ_pi`, `IsCompact.pi`, `isCompact_closedBall`, Tychonoff for finite products | depends entirely on the previous row (topology); the product step itself is 3 lines once `CompactSpace (Y_n(L_v))` exists |
| `non` (`Nonempty X`) | each `Y_n(L_v)` has points: ℚ-points of `Y_n` exist (the protected points D_T / the Fermat chart points) and embed into every `L_v` | `protectedToZeroPolynomial`/chart points (D_T nonempty), ℚ ↪ L_v | small gap: needs the embedding ℚ → L_v (from §7.2 `Algebra (Padic p) L`) and `Nonempty (Y_n(ℚ))`; doable |
| `delta` | `min_{v,k} dist_chordal(φ_i(y), {0,1,∞})` with φ_i = the i-th member of the fixed G-K family (`Mzk1G1DisjointFamilyActual.HasGluedBelyiFamily`, via `hPoly`/`psiFixed`/`hPolyL`) | `Mzk1G1KvCompactActual.InKv` (chordal-style conditions `δ ≤ min a 1`, `δ * max 1 a ≤ 1`, `|a-1| ≥ δ` at an archimedean place) · `localValueSet` | **gap**: a definition of chordal distance on ℙ¹(L_v) for finite v (archimedean case: standard formula, could be built from `InKv`); and the chart formulas of φ_i on `Y_n(L_v)` (next row) |
| `delta_cont` | each `v ↦ dist_chordal(φ_i(y_v), {0,1,∞})` continuous, min of finitely many continuous functions | Mathlib: `Continuous.min`, `Continuous.max`, `continuous_finset_inf`-style | **gap**: continuity of φ_i on the analytic/v-adic topology (rational functions are continuous where denominators do not vanish; need the chart cover to handle poles). Requires the topology row first |
| `delta_cover` | a tuple has at most `r = d·|V|` points; (E1) gives an i with none of them in `E_i = φ_i⁻¹{0,1,∞}`; then δ_i > 0 since `E_i` is finite and closed and the tuple points avoid it | `G1DisjointFamilyActual.exists_boundary_avoiding` · `gk_boundary_avoids_points` · `HasGluedBelyiFamily` (E1 proven) · `Mzk1G1PsiB1Actual` reducer `boundaryPreimage_finite_of_each` · `Mzk1G1PsiFiniteFiberActual` | **small gap**: identify `E_i ∩ Y_n(L_v)` with the scheme-level boundary preimage (`φ_i.base ⁻¹' boundarySetGlued`) and use finiteness (from `b1FiniteProducer`, emmy ⑥) + positive distance in the metric topology. Combinatorics already DONE |

## Assembly plan (after the topology gap is closed)

1. `delta_cover` (combinatorial + finiteness + separation) — 1 batch, independent of the
   big topology gap only if we assume the metric/topological model; otherwise blocked.
2. `X`, `top`, `comp`, `non`, `delta`, `delta_cont` — requires the analytic/v-adic topology
   of `Y_n(L_v)`; **this is new infrastructure not present in Mathlib or in the repo**
   (the repo's `Spec` topology is Zariski). Recommended: a separate package `Mzk1G1GKLocalTopology`
   that, for each `v`, defines the set of `L_v`-points of the two Fermat charts as a
   topological space (archimedean: subspace of ℂ²; finite: the v-adic topology from `Valued`),
   glues the two chart topologies along the overlap, proves compactness via the normalized
   plane model, and then `delta`/`delta_cont` follow from the chart formulas of φ_i.
3. `GKCompactInput` inhabitant = tuple of the above; then immediately
   `GKCompactInput.exists_delta0` (already DONE) yields the fixed δ₀>0 of route §7.3.
   The rest of G-K (family via `hasGluedBelyiFamily_of_GC`, `K_V` via `KvData`) is DONE
   or reduces to `GCB1FiniteProducer` (emmy ⑥).

## Bottom line

The *combinatorial* part of §7.3 is complete and the compactness extraction
(`exists_delta0`) is proven. The remaining work is a single, self-contained
**analytic-topology package** for `L_v`-points of the curve (`top`/`comp`/`delta`/`delta_cont`),
plus the §7.2 local-field producer (alan). `non` and `delta_cover` are small.

