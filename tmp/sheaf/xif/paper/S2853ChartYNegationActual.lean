import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure
import tmp.sheaf.xif.paper.S2820E37TransitionActual
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2853ChartYNegationActual

open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual

variable (K : Type) [Field K]

/-- The chart-Y coordinate t = Z/Y. -/
abbrev S2853ChartYT : E37ChartYRing K :=
  Ideal.Quotient.mk (E37ChartYIdeal K) (MvPolynomial.X 1)

/-- The chart-Y coordinate s = X/Y. -/
abbrev S2853ChartYS : E37ChartYRing K :=
  Ideal.Quotient.mk (E37ChartYIdeal K) (MvPolynomial.X 0)

/-- Localization at 1 + t. -/
abbrev S2853ChartYNegRing : Type :=
  Localization.Away (1 + S2853ChartYT K)

/-- The unit 1 + t in the localization. -/
noncomputable def S2853ChartYNegUnit : (S2853ChartYNegRing K)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (x := 1 + S2853ChartYT K) (S := S2853ChartYNegRing K)).unit

/-- Negation formula on chart Y: s' = -s / (1+t). -/
noncomputable def S2853ChartYNegS : S2853ChartYNegRing K :=
  algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (-(S2853ChartYS K)) *
    ↑((S2853ChartYNegUnit K)⁻¹)

/-- Negation formula on chart Y: t' = -t / (1+t). -/
noncomputable def S2853ChartYNegT : S2853ChartYNegRing K :=
  algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (-(S2853ChartYT K)) *
    ↑((S2853ChartYNegUnit K)⁻¹)


/-- Evaluation values for the chart-Y negation on D(1+t). -/
noncomputable def S2853G0Vals : Fin 2 → S2853ChartYNegRing K
  | ⟨0, _⟩ => S2853ChartYNegS K
  | ⟨1, _⟩ => S2853ChartYNegT K
  | ⟨n + 2, h⟩ => absurd h (by omega)

/-- Polynomial evaluation map for the chart-Y negation. -/
noncomputable def S2853G0Poly :
    MvPolynomial (Fin 2) K →+* S2853ChartYNegRing K :=
  MvPolynomial.eval₂Hom (algebraMap K (S2853ChartYNegRing K)) (S2853G0Vals K)

/-- Coordinate X maps to -s/(1+t). -/
theorem S2853_hX0 :
    S2853G0Poly K (MvPolynomial.X 0) = S2853ChartYNegS K := by
  simp [S2853G0Poly, S2853G0Vals]

/-- Coordinate Y maps to -t/(1+t). -/
theorem S2853_hX1 :
    S2853G0Poly K (MvPolynomial.X 1) = S2853ChartYNegT K := by
  simp [S2853G0Poly, S2853G0Vals]

/-- The chart-Y relation in the localization away from 1+t. -/
theorem S2853_hrel :
    algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
      ((S2853ChartYS K) ^ 3 - S2853ChartYS K * (S2853ChartYT K) ^ 2 -
        S2853ChartYT K - (S2853ChartYT K) ^ 2) = 0 := by
  have h : (S2853ChartYS K) ^ 3 - S2853ChartYS K * (S2853ChartYT K) ^ 2 -
      S2853ChartYT K - (S2853ChartYT K) ^ 2 = 0 := by
    simpa [S2853ChartYS, S2853ChartYT, E37ChartYPolynomial] using
      chartYRelation_quotient K
  rw [h, map_zero]



/-- Scaling identity: multiplying the negation substitution by (1+t)^3
clears all denominators and gives minus the original polynomial. -/
theorem S2853G0Poly_scale :
    (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K)^3 *
      S2853G0Poly K (E37ChartYPolynomial K) =
      -algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
        (E37ChartYPolynomial K) := by
  let u : S2853ChartYNegRing K := ↑(S2853ChartYNegUnit K)
  let v : S2853ChartYNegRing K := ↑((S2853ChartYNegUnit K)⁻¹)
  let A : S2853ChartYNegRing K := algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYS K)
  let B : S2853ChartYNegRing K := algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (S2853ChartYT K)
  have huv : u * v = 1 := Units.mul_inv (S2853ChartYNegUnit K)
  have hS : S2853ChartYNegS K = -A * v := by simp [S2853ChartYNegS, A, v]
  have hT : S2853ChartYNegT K = -B * v := by simp [S2853ChartYNegT, B, v]
  have hrep : S2853G0Poly K (E37ChartYPolynomial K) =
      (S2853ChartYNegS K)^3 - S2853ChartYNegS K * (S2853ChartYNegT K)^2 -
        S2853ChartYNegT K - (S2853ChartYNegT K)^2 := by
    simp only [S2853G0Poly, S2853G0Vals, E37ChartYPolynomial,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C,
      map_add, map_mul, map_pow, map_sub]
  have h1 : u^3 * (S2853ChartYNegS K)^3 = -(A^3) := by
    rw [hS]
    calc
      u^3 * (-A * v)^3 = -(A^3) * (u*v)^3 := by ring
      _ = -(A^3) := by rw [huv]; ring
  have h2 : u^3 * (S2853ChartYNegS K * (S2853ChartYNegT K)^2) = -(A * B^2) := by
    rw [hS, hT]
    calc
      u^3 * ((-A * v) * (-B * v)^2) = -(A * B^2) * (u*v)^3 := by ring
      _ = -(A*B^2) := by rw [huv]; ring
  have h3 : u^3 * (S2853ChartYNegT K) = -(B * u^2) := by
    rw [hT]
    calc
      u^3 * (-B * v) = -(B) * u^2 * (u*v) := by ring
      _ = -(B*u^2) := by rw [huv]; ring
  have h4 : u^3 * (S2853ChartYNegT K)^2 = B^2 * u := by
    rw [hT]
    calc
      u^3 * (-B * v)^2 = B^2 * u * (u*v)^2 := by ring
      _ = B^2 * u := by rw [huv]; ring
  calc
    u^3 * S2853G0Poly K (E37ChartYPolynomial K)
        = u^3 * ((S2853ChartYNegS K)^3 - S2853ChartYNegS K * (S2853ChartYNegT K)^2 -
            S2853ChartYNegT K - (S2853ChartYNegT K)^2) := by rw [hrep]
    _ = u^3*(S2853ChartYNegS K)^3 - u^3*(S2853ChartYNegS K*(S2853ChartYNegT K)^2)
          - u^3*(S2853ChartYNegT K) - u^3*(S2853ChartYNegT K)^2 := by ring
    _ = -A^3 + A*B^2 + B*u^2 - B^2*u := by rw [h1,h2,h3,h4]; ring
    _ = -A^3 + A*B^2 + B + B^2 := by
      have hu : u = 1 + B := by
        change (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K) = 1 + B
        rw [show (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K) =
          algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (1 + S2853ChartYT K) from
          IsUnit.unit_spec _]
        simp [B]
      rw [hu]; ring
    _ = -algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (E37ChartYPolynomial K) := by
      rw [show algebraMap (E37ChartYRing K) (S2853ChartYNegRing K) (E37ChartYPolynomial K)
        = A^3 - A*B^2 - B - B^2 by simp [E37ChartYPolynomial, A, B, map_sub, map_mul, map_pow]]
      ring

/-- The chart-Y polynomial relation vanishes under the negation substitution. -/
theorem S2853G0Poly_relation :
    S2853G0Poly K (E37ChartYPolynomial K) = 0 := by
  have hscale := S2853G0Poly_scale (K := K)
  have hu : IsUnit (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K) :=
    ⟨S2853ChartYNegUnit K, rfl⟩
  have hF : algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
      (Ideal.Quotient.mk (E37ChartYIdeal K) (E37ChartYPolynomial K)) =
      algebraMap (E37ChartYRing K) (S2853ChartYNegRing K)
        ((S2853ChartYS K)^3 - S2853ChartYS K*(S2853ChartYT K)^2
          - S2853ChartYT K - (S2853ChartYT K)^2) := by
    simp [E37ChartYPolynomial, map_sub, map_mul, map_pow]
  have hzero : (↑(S2853ChartYNegUnit K) : S2853ChartYNegRing K)^3 *
      S2853G0Poly K (E37ChartYPolynomial K) = 0 := by
    rw [hscale, hF, S2853_hrel]
    simp
  exact (IsUnit.mul_right_inj (hu.pow 3)).mp (by simpa using hzero)

#check S2853ChartYT
#check S2853ChartYS
#check S2853ChartYNegRing
#check S2853ChartYNegUnit
#check S2853ChartYNegS
#check S2853ChartYNegT

end LeanFormal.IUT.XiFPaper.S2853ChartYNegationActual
end
