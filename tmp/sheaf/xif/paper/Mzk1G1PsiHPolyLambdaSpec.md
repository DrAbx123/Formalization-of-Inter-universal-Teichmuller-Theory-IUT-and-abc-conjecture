# SPEC — `hPoly` coordinate dictionary and the λ-coordinate morphism `hPolyL`

Owner: henry (hull). Status: design; companion of `Mzk1G1PsiM2AnalyticHANDOFF.md` and
`Mzk1G1PsiBranchSpec.md`. Non-Lean design document.

## 1. Actual chart dictionary of `hPoly` (`Mzk1G1PsiHPolyFinalActual`, DONE 22:12:58)

Cover `HIdx = {c0, c1, c2}`:

| piece | `hPolyPieceFun` | `hPolyPieceMap` | `hPolyChartOf` (target chart map) |
|---|---|---|---|
| c0 | `Spec ℚ[t]` | `localChartInf` (whole t-chart) | `chartMorphismInf (R := ℚ[t]) h`, i.e. **t' = h(t)** |
| c1 | `Spec (Away X)` (X = λ) | `Spec.map (algebraMap ℚ[λ] (Away X)) ≫ localChart0` | `chartMorphismInf (R := Away X) (hPolyT h)`, i.e. t' = λ^{-d}·hRev(λ) |
| c2 | `Spec (Away (hRev h))` | `Spec.map (algebraMap ℚ[λ] (Away (hRev h))) ≫ localChart0` | `chartMorphism0 (R := Away (hRev h)) (hPolyLam h)`, i.e. λ' = λ^d/hRev(λ) |

Definitions (`Mzk1G1PsiHPolyActual`):
- `hRev h = ∑_{i∈h.support} C (h.coeff i) * X^(h.natDegree - i)`; for `h ≠ 0`,
  `hRev h = h.reverse` (proved in `Mzk1G1PsiHPolyCoverAlgebraActual.hRev_eq_reverse`), so
  the reverse identity **`λ^d·h(1/λ) = hRev(λ)`** holds;
- `hPolyT h = invSelf(λ)^d · algebraMap (hRev h)` (in `Away X`);
- `hPolyLam h = algebraMap(X)^d · invSelf(hRev h)` (in `Away (hRev h)`).

**Action of `hPoly` as a map of P¹:** in the t-coordinate it is `t ↦ h(t)`
(piece c0). Equivalently, in the λ-coordinate, it is

    λ ↦ 1/h(1/λ) = λ^d / hRev(λ)      (piece c2; on piece c1 same value as t-coord).

Consequences (matters for B1/B2):
- `hPoly` sends the point λ = 0 to λ = 0 (since t = ∞ ↦ t' = h(∞) = ∞);
- `hPoly` sends the point t = 0 (λ = ∞) to t' = h(0), i.e. λ' = 1/h(0) (when h(0) ≠ 0);
- hence `hPoly(ψFixed(D_T)) = hPoly(λ = 0) = 0`, so `φFixed = ψFixed ≫ hPoly` gives
  `φFixed(D_T) = p1Zero ∈ boundary` — **this violates B1**; the λ-coordinate version
  `hPolyL` below is the correct partner of `ψFixed`.

## 2. The required morphism `hPolyL` (λ-coordinate: λ ↦ h(λ))

Desired chart dictionary (mirror of §1; note a polynomial has no denominator, so the
λ-chart needs no splitting):

| piece | scheme | chart map | coordinate action |
|---|---|---|---|
| A | `Spec ℚ[λ]` (whole λ-chart) | `chartMorphism0 (R := ℚ[λ]) h` | λ' = h(λ) |
| B | `Spec (Away (hRev h))` (the intersection `D(hRev)` in the t-chart) | `Spec.map (algebraMap ℚ[t] (Away (hRev h))) ≫ chartMorphismInf (…)` | t' = t^d/hRev(t) (i.e. 1/h(1/t)) |

Rationale for piece B's ring: `t' = 1/h(1/t) = t^d/hRev(t)` (using the reverse identity),
which is regular exactly where `hRev(t) ≠ 0`; at `t = 0` it equals 0 (regular). The two
pieces cover P¹ because the λ-chart covers all points with λ finite (in particular every
point with `hRev(t) = 0`), and piece B covers the rest of the t-chart.
Compatibility on the overlap (λ = 1/t): piece A gives λ' = h(λ); piece B gives
t' = 1/h(1/t) = 1/h(λ), i.e. the same point (`λ' = 1/t'`). Proof as in `hPoly`'s (c0, c2)
mixed pair (`Mzk1G1PsiHPolyFinalActual.compat_c0_c2` is the template; the P¹ gluing square
`isPullback_charts` is reusable).

**Cheaper equivalent (recommended first attempt):** let `ι : projectiveLineGlued ⟶
projectiveLineGlued` be the P¹ inversion (`λ ↦ λ⁻¹`). Then

    hPolyL = ι ≫ hPoly ≫ ι      (since (ι∘hPoly∘ι)(λ) = 1/(1/h(1/(1/λ))) = h(λ)).

`ι` is a 2-piece glue with chart maps (A) `chartMorphismInf (R := ℚ[λ]) X` on the λ-chart
(t' = λ) and (B) `chartMorphism0 (R := ℚ[t]) X` on the t-chart (λ' = t); the overlap
compatibility is exactly `chartMorphism_transition (R := Away X) (invSelf)`:
`chartMorphismInf X = chartMorphism0 (↑invSelf)` (mirror of `psiFixed`'s construction in
`Mzk1G1PsiFixedActual.glueMorphisms_compat_fixed`; `invAuto`/`invAutoEquiv` in
`Mzk1G1ProjectiveLineGluedActual` are the ring-level inversion on the overlap and
`invAuto_comp_self` is the involution law `ι ≫ ι = 𝟙`).

## 3. Composite with `psiFixed` (B1/B2 wiring)

- `psiFixed(D_T) = p1Zero` (λ = 0): D_T is the zero-fiber of `u = psiChart0Coord` in the
  **λ**-chart, and `psiFixed`'s piece `⟨false⟩` uses `chartMorphism0 psiChart0Coord`,
  so B2 holds with the λ = 0 point (Lead ruling 22:20).
- `φFixed := psiFixed ≫ hPolyL`; then `φFixed(D_T) = hPolyL(λ = 0) = h(0)` (piece A),
  hence **`φFixed(D_T) = P1Point.ofFinite (h 0)`** and the B1 T-avoidance is exactly
  `h(0) ∉ {0,1,∞}` (the `M2AnalyticTarget` conjunct).
- Chart formula for the composite on the λ-chart: `λ ↦ h(u)` where `u = psiChart0Coord`;
  on the t-chart of `psiFixed`: t-coordinate = hPolyL's piece B formula applied to
  `psiChartInfCoord`.

## 4. Effect on the branch spec

`Branch(ψFixed) = inv '' Branch(ψ)` (as in `Mzk1G1PsiBranchSpec.md`) is unchanged: it is a
property of `ψ`/`psiFixed`, not of `hPoly`. What changes is only the **consumer**:
`h := hλ` is the λ-coordinate polynomial, so
- `M2AnalyticTarget Branch` with `Branch := inv '' criticalValuesOverC u` and the produced
  `q` is exactly `h` in the λ-coordinate: the second conjunct is
  `∀ z ∈ Branch, aeval z q ∈ {0,1}` = `q(Branch(ψFixed)) ⊆ {0,1}`;
- the scheme-level morphism for B1 is `phi := psiFixed ≫ hPolyL q` (NOT `≫ hPoly q`);
- `hPolyL`'s critical values in the λ-coordinate are `criticalValuesOverC q` (finite part);
  this is consistent by construction, so no extra branch statements are needed for `hPolyL`.

## 5. Deliverables / next steps

1. `Mzk1G1PsiHPolyLambdaActual.lean` (new file): `p1Inv` (ι) as a 2-piece glue +
   `p1Inv_comp_self`; then `hPolyL := p1Inv ≫ hPoly ≫ p1Inv`; then
   `hPolyL_ι_*` (chart lemmas) via `hPoly_ι_c0/c1/c2`;
2. `hPolyL_chart_lambda : ` λ-chart formula `λ ↦ h(λ)` (from piece A);
3. `phiFixed := psiFixed ≫ hPolyL` and `phiFixed_DT : phiFixed(D_T) = ofFinite (h 0)`;
4. BranchSpec update (done above): consume `M2AnalyticTarget (inv '' Branch ψ)` with `q = hλ`.
Each Lean file: watchdog + `#print axioms` = [propext, Classical.choice, Quot.sound].
