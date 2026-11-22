import LeanFormal.IUT.Foundations.Geometry.TateWeierstrassPointEquation
import Mathlib.Tactic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.TateCurve

namespace LeanFormal.IUT.XiFPaper.Node09TateRootGaloisActual

universe u v
variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L] [CharZero L]

/-- Actual principal root in a quadratic extension: u=(s-1)/(s+1) solves
u/(1-u)^2 = x when s^2=4x+1. -/
theorem principalRoot_in_quadratic_extension
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
    have h1' : algebraMap K L (4 * x + 1) = algebraMap K L 1 := by simpa using h1
    have hK : 4 * x + 1 = 1 := (algebraMap K L).injective h1'
    have h4x : 4 * x = 0 := by linear_combination hK
    have h4nz : (4 : K) ≠ 0 := by
      intro h0
      have hmap : (4 : L) = 0 := by rw [← map_ofNat (algebraMap K L) 4, h0, map_zero]
      exact (by norm_num : (4 : L) ≠ 0) hmap
    exact hx ((mul_eq_zero.mp h4x).resolve_left h4nz)
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

def Node09TateRootGaloisStatus : List String :=
  [ "actual: principalRoot_in_quadratic_extension gives u=(s-1)/(s+1) with u/(1-u)^2=x when s^2=4x+1",
    "remaining: Galois descent to the actual root field and the hTmaps/P1CoverageContractionData instantiation",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateRootGaloisActual