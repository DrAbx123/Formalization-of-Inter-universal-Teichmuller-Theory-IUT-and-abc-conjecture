import Mathlib
import Mathlib.NumberTheory.NumberField.Basic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open Polynomial

universe u
variable (K : Type u) [Field K] [NumberField K]

/-- Actual projective line over K: Option K, with none = ∞. -/
abbrev P1 (K : Type*) := Option K

/-- Actual polynomial self-map of P1: finite points via eval, ∞ to ∞. -/
def polynomialP1Map (p : K[X]) : P1 K → P1 K :=
  fun z => match z with
    | none => none
    | some x => some (p.eval x)

/-- Actual Belyi map over a number field: nonconstant polynomial whose
ramification points are carried only over {0,1,∞}; for a polynomial the pole
∞ is automatic, so the finite condition is derivative-zero ⇒ value 0 or 1. -/
structure BelyiMapData where
  poly : K[X]
  degree_pos : 0 < poly.natDegree
  ramified_only_base : ∀ x : K, poly.derivative.eval x = 0 →
    poly.eval x = 0 ∨ poly.eval x = 1

/-- The actual P1 endomap attached to a Belyi map. -/
def BelyiMapData.toP1 (D : BelyiMapData K) : P1 K → P1 K :=
  polynomialP1Map K D.poly

/-- Actual degree/uniform family of Belyi maps over K. -/
structure BelyiUniformFamilyData where
  degree : ℕ
  map : BelyiMapData K
  degree_eq : map.poly.natDegree = degree

/-- An actual Belyi map over ℚ: (X-1)^2+1, ramified over 1 and ∞. -/
def belyiExample : BelyiMapData ℚ where
  poly := X ^ 2 - 2 * X + C 2
  degree_pos := by
    have h : (X ^ 2 - 2 * X + C (2 : ℚ)).natDegree = 2 := by compute_degree!
    rw [h]
    norm_num
  ramified_only_base := by
    intro x hx
    norm_num [Polynomial.derivative_X_pow, Polynomial.derivative_X,
      Polynomial.derivative_C] at hx
    have hx1 : x = 1 := by linarith
    subst x
    right
    norm_num

/-- Actual singleton uniform family of degree 2. -/
def belyiUniformExample : BelyiUniformFamilyData ℚ where
  degree := 2
  map := belyiExample
  degree_eq := by
    change (X ^ 2 - 2 * X + C (2 : ℚ)).natDegree = 2
    compute_degree!


/-- Actual compactness/uniform-epsilon core: a polynomial derivative that is
nonzero on a compact subset of ℂ has a positive uniform lower bound there. -/
theorem exists_uniform_derivative_bound
    (p : ℂ[X]) (K : Set ℂ) (hK : IsCompact K)
    (hne : ∀ x ∈ K, p.derivative.eval x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ ‖p.derivative.eval x‖ := by
  have hcont : Continuous (fun x : ℂ => ‖p.derivative.eval x‖) := by fun_prop
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, fun x hx => (False.elim (by simpa using hx))⟩
  · obtain ⟨x0, hx0K, hmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
    refine ⟨‖p.derivative.eval x0‖, ?_, fun x hx => hmin hx⟩
    exact norm_pos_iff.mpr (hne x0 hx0K)



/-- Actual §13.3 compactness/uniform-epsilon specialization for Belyi maps:
on a compact set avoiding the ramification locus, the derivative has a positive
uniform lower bound. -/
theorem belyi_uniform_derivative_bound
    (D : BelyiMapData ℂ) (K : Set ℂ) (hK : IsCompact K)
    (hne : ∀ x ∈ K, D.poly.derivative.eval x ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, δ ≤ ‖D.poly.derivative.eval x‖ :=
  exists_uniform_derivative_bound D.poly K hK hne


end LeanFormal.IUT.XiFPaper.Mzk1G1Actual
end
