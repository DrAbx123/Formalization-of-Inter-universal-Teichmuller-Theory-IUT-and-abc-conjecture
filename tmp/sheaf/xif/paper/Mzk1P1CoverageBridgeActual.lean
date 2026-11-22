import LeanFormal.IUT.Foundations.Geometry.TateWeierstrassPointEquation
import LeanFormal.IUT.Foundations.Analysis.BanachFixedPointClosedBall
import Mathlib.Tactic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.TateCurve

namespace LeanFormal.IUT.XiFPaper.Mzk1P1CoverageBridgeActual

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero L]

/-- Over a field L containing a square root s of 4x+1, the principal equation
u/(1-u)^2 = x has the explicit root u=(s-1)/(s+1). -/
theorem principal_quadratic_root_in_extension
    (x : K) (hx : x ≠ 0) (s : L)
    (hs : s ^ 2 = algebraMap K L (4 * x + 1)) :
    ∃ u : L, u / (1 - u) ^ 2 = algebraMap K L x := by
  have hsL : s ^ 2 = 4 * algebraMap K L x + 1 := by
    calc s ^ 2 = algebraMap K L (4 * x + 1) := hs
      _ = algebraMap K L (4 * x) + algebraMap K L 1 := by rw [map_add]
      _ = algebraMap K L 4 * algebraMap K L x + 1 := by rw [map_mul, map_one]
      _ = 4 * algebraMap K L x + 1 := by rw [map_ofNat]
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hsneg : s = -1 := eq_neg_of_add_eq_zero_left h
    have h1 : algebraMap K L (4 * x + 1) = 1 := by
      rw [← hs, hsneg]
      norm_num
    have h1' : algebraMap K L (4 * x + 1) = algebraMap K L 1 := by
      simpa using h1
    have hK : 4 * x + 1 = 1 := (algebraMap K L).injective h1'
    have h4x : 4 * x = 0 := by linear_combination hK
    have h4nz : (4 : K) ≠ 0 := by
      intro h0
      have hmap : (4 : L) = 0 := by
        rw [← map_ofNat (algebraMap K L) 4, h0, map_zero]
      norm_num at hmap
    have hx0 : x = 0 := (mul_eq_zero.mp h4x).resolve_left h4nz
    exact hx hx0
  refine ⟨(s - 1) / (s + 1), ?_⟩
  have h1u : 1 - (s - 1) / (s + 1) = 2 / (s + 1) := by
    field_simp [hs1]
    ring
  have hfirst : ((s - 1) / (s + 1)) / (2 / (s + 1)) ^ 2 =
      (s - 1) * (s + 1) / 4 := by
    field_simp [hs1]
    ring
  rw [h1u]
  calc ((s - 1) / (s + 1)) / (2 / (s + 1)) ^ 2
      = (s - 1) * (s + 1) / 4 := hfirst
    _ = (s ^ 2 - 1) / 4 := by ring
    _ = algebraMap K L x := by rw [hsL]; ring


def Node09P1CoverageBridgeStatus : List String :=
  [ "actual: principal_quadratic_root_in_extension gives the explicit root u=(s-1)/(s+1) of the principal equation u/(1-u)^2=x in a quadratic extension containing sqrt(4x+1)",
    "remaining: derivative unit and tail Lipschitz/contraction estimates, Galois descent to the actual root field",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Mzk1P1CoverageBridgeActual