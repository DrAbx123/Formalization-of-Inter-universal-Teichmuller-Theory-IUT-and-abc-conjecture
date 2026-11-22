import tmp.sheaf.xif.paper.Node09TateLaurentExpansionActual
import LeanFormal.IUT.Foundations.Geometry.TateCoordinatePeriodicity
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open LeanFormal.IUT
open scoped BigOperators NNReal

namespace LeanFormal.IUT.XiFPaper.Node09TateNewtonPolygonActual

universe u

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- X is invariant under inversion of the parameter (x-coordinate evenness). -/
theorem tateWeierstrassX_inv (q u : K) :
    TateCurve.tateWeierstrassX q u⁻¹ = TateCurve.tateWeierstrassX q u := by
  rw [TateCurve.tateWeierstrassX, TateCurve.tateWeierstrassX,
    TateCurve.coordinateSeries_inv]

/-- Norm bound on the positive-index tail of the X Laurent series. -/
theorem xPositiveTail_norm_le
    (P : RigidTate.Parameter (K := K)) (u : RigidTate.FundamentalDomain P) :
    ‖∑' n : ℕ, RigidTate.xPositiveTerm P u (n + 1)‖ ≤
      ‖u.1‖ * (‖P.q‖ / (1 - ‖P.q‖)) := by
  have hq : ‖P.q‖ < 1 := P.q_norm_lt_one
  have hq0 : 0 ≤ ‖P.q‖ := norm_nonneg _
  have hden : 0 < 1 - ‖P.q‖ := by linarith
  have hqR : ‖(‖P.q‖ : ℝ)‖ < 1 := by simpa using hq
  have hgeom : HasSum (fun n : ℕ => ‖P.q‖ ^ n) (1 - ‖P.q‖)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hqR
  have hshift : HasSum (fun n : ℕ => ‖u.1‖ * (‖P.q‖ ^ (n + 1)))
      (‖u.1‖ * (‖P.q‖ / (1 - ‖P.q‖))) := by
    have h : HasSum (fun n : ℕ => ‖P.q‖ * ‖P.q‖ ^ n)
        (‖P.q‖ * (1 - ‖P.q‖)⁻¹) := hgeom.mul_left ‖P.q‖
    have h2 : (fun n : ℕ => ‖P.q‖ * ‖P.q‖ ^ n) =
        (fun n : ℕ => ‖P.q‖ ^ (n + 1)) := by
      funext n
      rw [pow_succ, mul_comm]
    rw [h2] at h
    have h3 : HasSum (fun n : ℕ => ‖u.1‖ * ‖P.q‖ ^ (n + 1))
        (‖u.1‖ * (‖P.q‖ * (1 - ‖P.q‖)⁻¹)) := h.mul_left ‖u.1‖
    simpa [div_eq_mul_inv] using h3
  refine tsum_of_norm_bounded hshift ?_
  intro n
  have hle := RigidTate.Term.xPositiveTerm_norm_le P u (n + 1)
  have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  rw [hcast] at hle
  have hcast2 : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  have hpow : ‖P.q‖ ^ ((n : ℤ) + 1) = ‖P.q‖ ^ (n + 1) := by
    rw [hcast2, zpow_natCast]
  calc ‖RigidTate.xPositiveTerm P u (n + 1)‖
      ≤ ‖P.q‖ ^ ((n : ℤ) + 1) * ‖u.1‖ := hle
    _ = ‖u.1‖ * ‖P.q‖ ^ (n + 1) := by rw [hpow]; ring

/-- Norm bound on the negative half of the X Laurent series. -/
theorem xNegativeSeries_norm_le
    (P : RigidTate.Parameter (K := K)) (u : RigidTate.FundamentalDomain P) :
    ‖RigidTate.xNegativeSeries P u‖ ≤
      ‖u.1‖⁻¹ * (‖P.q‖ / (1 - ‖P.q‖)) := by
  have hq : ‖P.q‖ < 1 := P.q_norm_lt_one
  have hden : 0 < 1 - ‖P.q‖ := by linarith [norm_nonneg P.q]
  have hqR : ‖(‖P.q‖ : ℝ)‖ < 1 := by simpa using hq
  have hgeom : HasSum (fun n : ℕ => ‖P.q‖ ^ n) (1 - ‖P.q‖)⁻¹ :=
    hasSum_geometric_of_norm_lt_one hqR
  have hshift : HasSum (fun n : ℕ => ‖u.1‖⁻¹ * (‖P.q‖ ^ (n + 1)))
      (‖u.1‖⁻¹ * (‖P.q‖ / (1 - ‖P.q‖))) := by
    have h : HasSum (fun n : ℕ => ‖P.q‖ * ‖P.q‖ ^ n)
        (‖P.q‖ * (1 - ‖P.q‖)⁻¹) := hgeom.mul_left ‖P.q‖
    have h2 : (fun n : ℕ => ‖P.q‖ * ‖P.q‖ ^ n) =
        (fun n : ℕ => ‖P.q‖ ^ (n + 1)) := by
      funext n
      rw [pow_succ, mul_comm]
    rw [h2] at h
    have h3 : HasSum (fun n : ℕ => ‖u.1‖⁻¹ * ‖P.q‖ ^ (n + 1))
        (‖u.1‖⁻¹ * (‖P.q‖ * (1 - ‖P.q‖)⁻¹)) := h.mul_left ‖u.1‖⁻¹
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using h3
  rw [RigidTate.xNegativeSeries]
  refine tsum_of_norm_bounded hshift ?_
  intro n
  have hle := RigidTate.Term.xNegativeTerm_norm P u n
  have hcast2 : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  have hpow : ‖P.q‖ ^ ((n : ℤ) + 1) = ‖P.q‖ ^ (n + 1) := by
    rw [hcast2, zpow_natCast]
  have heq : ‖RigidTate.xNegativeTerm P u n‖ =
      ‖u.1‖⁻¹ * ‖P.q‖ ^ (n + 1) := by
    rw [hle, hpow]
    ring
  exact le_of_eq heq


def Node09TateNewtonPolygonStatus : List String :=
  [ "actual: tateWeierstrassX is inversion-even, X(u^{-1})=X(u), so the zero count of X(u)=x automatically pairs u with u^{-1}",
    "actual: positive tail bound ||sum_{n>=1} xPositiveTerm|| <= ||u||*(||q||/(1-||q||)) and negative half bound ||xNegativeSeries|| <= (||q||/(1-||q||))*||u||^{-1}",
    "missing Newton-polygon/zero-count lemma: on the fundamental annulus compare the principal term u/(1-u)^2 with the two remainder bounds to prove X(u)=x has at most the two branches u,u^{-1} modulo q^Z; no zero-count or Rouché-type theorem for these Lambert series exists in the tree",
    "missing Y inversion branch lemma: select the branch with Y(u)=y using the twisted inversion law yCoordinateSeries_inv / yCoordinateSeriesTwisted",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateNewtonPolygonActual