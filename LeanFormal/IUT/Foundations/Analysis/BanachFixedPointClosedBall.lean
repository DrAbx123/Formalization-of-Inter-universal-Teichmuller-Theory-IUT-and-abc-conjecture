/-
Scratch: Banach fixed point theorem on an invariant closed ball.

Contents:
* `exists_fixedPoint_of_mapsTo_closedBall`: a `c`-contraction (`c < 1`) of a
  closed ball `B = {x | dist x x₀ ≤ r}` (`r ≥ 0`) into itself has a fixed
  point in `B`, for a complete normed additive group.  Norm form:
  `exists_fixedPoint_of_mapsTo_closedBall_norm`.
* `existsUnique_fixedPoint_of_mapsTo_closedBall`: uniqueness inside `B`.
* `exists_fixedPoint_of_ultrametric_closedBall`: in an ultrametric space the
  invariance of `B` follows from `dist (T x₀) x₀ ≤ r`, which is the genuinely
  nonarchimedean input.
* nonarchimedean specializations over a complete nonarchimedean normed field,
  including the case where the space is the field itself.

No `sorry`/`axiom` is used; the proofs rest on Mathlib's Banach fixed point
theorem for complete subsets (`ContractingWith.exists_fixedPoint'`).  All
theorems depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set Metric
open scoped NNReal

namespace ABCBridge.BanachFixedPointClosedBall

/-! ## The general complete normed setting -/

/-- **Banach fixed point theorem on an invariant closed ball.**

Let `E` be a complete normed additive group, `x₀ : E`, `r ≥ 0`, and
`T : E → E`.  If `T` maps the closed ball `B = {x | dist x x₀ ≤ r}` into
itself and is a `c`-contraction on `B` with `c < 1`, then `T` has a fixed
point in `B`. -/
theorem exists_fixedPoint_of_mapsTo_closedBall
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (x₀ : E) {r : ℝ} (hr : 0 ≤ r) (T : E → E) {c : ℝ≥0} (hc : c < 1)
    (hTmaps : MapsTo T (closedBall x₀ r) (closedBall x₀ r))
    (hTcontract : ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
      dist (T x) (T y) ≤ (c : ℝ) * dist x y) :
    ∃ x ∈ closedBall x₀ r, T x = x := by
  have hcomplete : IsComplete (closedBall x₀ r) := Metric.isClosed_closedBall.isComplete
  have hcontract :
      ContractingWith c (hTmaps.restrict T (closedBall x₀ r) (closedBall x₀ r)) := by
    refine ⟨hc, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simpa only [Subtype.dist_eq, Set.MapsTo.restrict, Subtype.map] using
      hTcontract x x.2 y y.2
  obtain ⟨x, hx, hfix, -⟩ :=
    hcontract.exists_fixedPoint' hcomplete hTmaps
      (Metric.mem_closedBall_self hr) (edist_ne_top x₀ (T x₀))
  exact ⟨x, hx, hfix.eq⟩

/-- **Norm form of the invariant-closed-ball Banach theorem.**

This is the statement with `B = {x | ‖x - x₀‖ ≤ r}` written using the norm
instead of `dist`; it is the form used in the nonarchimedean applications. -/
theorem exists_fixedPoint_of_mapsTo_closedBall_norm
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (x₀ : E) {r : ℝ} (hr : 0 ≤ r) (T : E → E) {c : ℝ≥0} (hc : c < 1)
    (hTmaps : ∀ x : E, ‖x - x₀‖ ≤ r → ‖T x - x₀‖ ≤ r)
    (hTcontract : ∀ x : E, ‖x - x₀‖ ≤ r → ∀ y : E, ‖y - x₀‖ ≤ r →
      ‖T x - T y‖ ≤ (c : ℝ) * ‖x - y‖) :
    ∃ x : E, ‖x - x₀‖ ≤ r ∧ T x = x := by
  have hTmaps' : MapsTo T (closedBall x₀ r) (closedBall x₀ r) := by
    intro x hx
    have hx' : ‖x - x₀‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    have hTx' : ‖T x - x₀‖ ≤ r := hTmaps x hx'
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hTx'
  have hTcontract' : ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
      dist (T x) (T y) ≤ (c : ℝ) * dist x y := by
    intro x hx y hy
    have hx' : ‖x - x₀‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    have hy' : ‖y - x₀‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
    simpa only [dist_eq_norm] using hTcontract x hx' y hy'
  obtain ⟨x, hx, hfix⟩ :=
    exists_fixedPoint_of_mapsTo_closedBall x₀ hr T hc hTmaps' hTcontract'
  exact ⟨x, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx, hfix⟩

/-- Fixed points of a contraction on a closed ball are unique inside that ball. -/
theorem eq_of_fixedPoints_of_mem_closedBall
    {E : Type*} [NormedAddCommGroup E]
    (x₀ : E) {r : ℝ} {T : E → E} {c : ℝ≥0} (hc : c < 1)
    (hTcontract : ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
      dist (T x) (T y) ≤ (c : ℝ) * dist x y)
    {x y : E} (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r)
    (hxT : T x = x) (hyT : T y = y) : x = y := by
  have h : dist x y ≤ (c : ℝ) * dist x y := by
    calc dist x y = dist (T x) (T y) := by rw [hxT, hyT]
      _ ≤ (c : ℝ) * dist x y := hTcontract x hx y hy
  have hc' : (0 : ℝ) < 1 - (c : ℝ) := by
    have : (c : ℝ) < 1 := by exact_mod_cast hc
    linarith
  have hle : (1 - (c : ℝ)) * dist x y ≤ 0 := by
    nlinarith [dist_nonneg (x := x) (y := y)]
  have hd : dist x y = 0 := by
    by_contra hne
    have hdpos : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
    have hpos : 0 < (1 - (c : ℝ)) * dist x y := mul_pos hc' hdpos
    linarith
  exact eq_of_dist_eq_zero hd

/-- **Uniqueness form of the invariant-closed-ball Banach theorem.** -/
theorem existsUnique_fixedPoint_of_mapsTo_closedBall
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (x₀ : E) {r : ℝ} (hr : 0 ≤ r) (T : E → E) {c : ℝ≥0} (hc : c < 1)
    (hTmaps : MapsTo T (closedBall x₀ r) (closedBall x₀ r))
    (hTcontract : ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
      dist (T x) (T y) ≤ (c : ℝ) * dist x y) :
    ∃! x : E, x ∈ closedBall x₀ r ∧ T x = x := by
  obtain ⟨x, hx, hfix⟩ :=
    exists_fixedPoint_of_mapsTo_closedBall x₀ hr T hc hTmaps hTcontract
  refine ⟨x, ⟨hx, hfix⟩, ?_⟩
  rintro y ⟨hy, hyfix⟩
  exact eq_of_fixedPoints_of_mem_closedBall x₀ hc hTcontract hy hx hyfix hfix

/-! ## The nonarchimedean (ultrametric) refinement

In an ultrametric space the hypothesis that the ball is mapped into itself can
be derived from the single condition `dist (T x₀) x₀ ≤ r` together with the
contraction property on the ball.  This is the genuinely nonarchimedean input:
it fails for the usual archimedean norm on `ℝ`. -/

section Ultrametric

variable {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E]

/-- In an ultrametric space, a contraction of the ball that moves the centre by
at most `r` maps the whole closed ball of radius `r` into itself. -/
theorem mapsTo_closedBall_of_ultrametric
    (x₀ : E) {r : ℝ} (hr : 0 ≤ r) {T : E → E} {c : ℝ≥0} (hc : c < 1)
    (hx₀ : dist (T x₀) x₀ ≤ r)
    (hTcontract : ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
      dist (T x) (T y) ≤ (c : ℝ) * dist x y) :
    MapsTo T (closedBall x₀ r) (closedBall x₀ r) := by
  intro x hx
  have hxdist : dist x x₀ ≤ r := hx
  rw [Metric.mem_closedBall]
  have hx₀mem : x₀ ∈ closedBall x₀ r := Metric.mem_closedBall_self hr
  have hcontr : dist (T x) (T x₀) ≤ (c : ℝ) * dist x x₀ := hTcontract x hx x₀ hx₀mem
  have hcx : (c : ℝ) * dist x x₀ ≤ r := by
    calc (c : ℝ) * dist x x₀ ≤ 1 * dist x x₀ :=
          mul_le_mul_of_nonneg_right hc.le dist_nonneg
      _ = dist x x₀ := one_mul _
      _ ≤ r := hxdist
  calc dist (T x) x₀
      ≤ max (dist (T x) (T x₀)) (dist (T x₀) x₀) :=
        IsUltrametricDist.dist_triangle_max (T x) (T x₀) x₀
    _ ≤ max r r := max_le_max (hcontr.trans hcx) hx₀
    _ = r := max_self r

/-- **Nonarchimedean invariant-closed-ball Banach theorem.**

Let `E` be a complete ultrametric normed additive group (for instance a
complete nonarchimedean normed vector space), `x₀ : E`, `r ≥ 0`, and
`T : E → E`.  If `T` contracts distances on `B = {x | dist x x₀ ≤ r}` by a
factor `c < 1` and moves `x₀` by at most `r`, then `T` has a fixed point
in `B`.  The invariance of `B` is automatic here, by the ultrametric
inequality. -/
theorem exists_fixedPoint_of_ultrametric_closedBall
    [CompleteSpace E]
    (x₀ : E) {r : ℝ} (hr : 0 ≤ r) (T : E → E) {c : ℝ≥0} (hc : c < 1)
    (hx₀ : dist (T x₀) x₀ ≤ r)
    (hTcontract : ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
      dist (T x) (T y) ≤ (c : ℝ) * dist x y) :
    ∃ x ∈ closedBall x₀ r, T x = x :=
  exists_fixedPoint_of_mapsTo_closedBall x₀ hr T hc
    (mapsTo_closedBall_of_ultrametric x₀ hr hc hx₀ hTcontract) hTcontract

end Ultrametric

/-! ## Complete nonarchimedean normed fields and vector spaces -/

section NonarchimedeanField

/-- **Banach fixed point theorem on an invariant closed ball over a complete
nonarchimedean normed field.**

Here `E` is a finite-dimensional normed `𝕜`-vector space over a complete
nonarchimedean normed field; completeness of `E` is deduced from completeness
of `𝕜` and finite dimensionality. -/
theorem exists_fixedPoint_of_mapsTo_closedBall_nonarchimedean
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [IsUltrametricDist 𝕜] [IsUltrametricDist E]
    (x₀ : E) {r : ℝ} (hr : 0 ≤ r) (T : E → E) {c : ℝ≥0} (hc : c < 1)
    (hTmaps : MapsTo T (closedBall x₀ r) (closedBall x₀ r))
    (hTcontract : ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
      dist (T x) (T y) ≤ (c : ℝ) * dist x y) :
    ∃ x ∈ closedBall x₀ r, T x = x := by
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  exact exists_fixedPoint_of_mapsTo_closedBall x₀ hr T hc hTmaps hTcontract

/-- **Nonarchimedean invariant-closed-ball Banach theorem over a complete
nonarchimedean field**, with ball invariance derived from `dist (T x₀) x₀ ≤ r`. -/
theorem exists_fixedPoint_of_ultrametric_closedBall_nonarchimedean
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [IsUltrametricDist 𝕜] [IsUltrametricDist E]
    (x₀ : E) {r : ℝ} (hr : 0 ≤ r) (T : E → E) {c : ℝ≥0} (hc : c < 1)
    (hx₀ : dist (T x₀) x₀ ≤ r)
    (hTcontract : ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
      dist (T x) (T y) ≤ (c : ℝ) * dist x y) :
    ∃ x ∈ closedBall x₀ r, T x = x := by
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  exact exists_fixedPoint_of_ultrametric_closedBall x₀ hr T hc hx₀ hTcontract

end NonarchimedeanField

/-- **The same theorem for a complete nonarchimedean normed field itself**:
a contraction of a closed ball of `𝕜` that moves the centre by at most `r`
has a fixed point in that ball. -/
theorem exists_fixedPoint_closedBall_self_nonarchimedean
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [IsUltrametricDist 𝕜]
    (x₀ : 𝕜) {r : ℝ} (hr : 0 ≤ r) (T : 𝕜 → 𝕜) {c : ℝ≥0} (hc : c < 1)
    (hx₀ : dist (T x₀) x₀ ≤ r)
    (hTcontract : ∀ x ∈ closedBall x₀ r, ∀ y ∈ closedBall x₀ r,
      dist (T x) (T y) ≤ (c : ℝ) * dist x y) :
    ∃ x ∈ closedBall x₀ r, T x = x := by
  haveI : FiniteDimensional 𝕜 𝕜 := inferInstance
  exact exists_fixedPoint_of_ultrametric_closedBall_nonarchimedean (𝕜 := 𝕜) (E := 𝕜)
    x₀ hr T hc hx₀ hTcontract

end ABCBridge.BanachFixedPointClosedBall
