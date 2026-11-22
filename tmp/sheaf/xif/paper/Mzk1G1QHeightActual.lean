import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1QHeightActual
open LeanFormal.IUT

/-- The actual Legendre j-invariant rational function
j(lam) = 2^8 (1 - lam + lam^2)^3 / (lam^2 (1 - lam)^2) over an arbitrary field.
This definition is reusable; note that j has poles at lam = 0 and lam = 1, so
no value statements at those points are made here. -/
def legendreJ {K : Type*} [Field K] (lam : K) : K :=
  256 * (1 - lam + lam ^ 2) ^ 3 / (lam ^ 2 * (1 - lam) ^ 2)

/-- The actual standard logarithmic height h_{O(1)}(lam) of lam, i.e. the
Mathlib number-field height Height.logHeight₁. -/
def lambdaHeight {K : Type*} [Field K] [NumberField K] (lam : K) : ℝ :=
  Height.logHeight₁ lam

/-- The actual standard logarithmic height of the Legendre j-invariant j(lam). -/
def jHeight {K : Type*} [Field K] [NumberField K] (lam : K) : ℝ :=
  Height.logHeight₁ (legendreJ lam)

theorem lambdaHeight_nonneg {K : Type*} [Field K] [NumberField K] (lam : K) :
    0 ≤ lambdaHeight lam :=
  Height.zero_le_logHeight₁ lam

theorem jHeight_nonneg {K : Type*} [Field K] [NumberField K] (lam : K) :
    0 ≤ jHeight lam :=
  Height.zero_le_logHeight₁ (legendreJ lam)

/-- The height dictionary interface (route section 6.3, (D3)): a q-height h
supplied by the P7 data of the U-R lane and the standard height differ by the
fixed constant B on the actual local domain K_V.

INTERFACE, NO INHABITANT: the actual q-height is constructed in the U-R lane
from the Tate parameter; this file only records the precise statement. -/
def HeightDictionaryInterface {K : Type*} [Field K] [NumberField K]
    (qHeight : K → ℝ) (B : ℝ) : Prop :=
  ∀ lam : K, |lambdaHeight lam - qHeight lam / 6| ≤ B

/-! ### The Legendre j-invariant as a degree 6 morphism and its height bound -/

section HeightBounds

variable {K : Type*} [Field K] [NumberField K]

/-- Homogenized numerator of the Legendre j-invariant:
256 * (X0^2 - X0 * X1 + X1^2)^3, homogeneous of degree 6. -/
def jNum : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (256 : K) * (MvPolynomial.X 0 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 1
    + MvPolynomial.X 1 ^ 2) ^ 3

/-- Homogenized denominator of the Legendre j-invariant:
X0^2 * X1^2 * (X1 - X0)^2, homogeneous of degree 6. -/
def jDen : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2 * (MvPolynomial.X 1 - MvPolynomial.X 0) ^ 2

theorem jNum_isHomogeneous : (jNum (K := K)).IsHomogeneous 6 := by
  unfold jNum
  have hX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) K).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X (σ := Fin 2) (R := K) 0
  have hX1 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) K).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X (σ := Fin 2) (R := K) 1
  have hX0sq : (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 2) K).IsHomogeneous 2 :=
    MvPolynomial.isHomogeneous_X_pow (σ := Fin 2) (R := K) 0 2
  have hX1sq : (MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) K).IsHomogeneous 2 :=
    MvPolynomial.isHomogeneous_X_pow (σ := Fin 2) (R := K) 1 2
  have h : (MvPolynomial.X 0 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 1
      + MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) K).IsHomogeneous 2 :=
    (hX0sq.sub (hX0.mul hX1)).add hX1sq
  simpa using (MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := K) (256 : K)).mul (h.pow 3)

theorem jDen_isHomogeneous : (jDen (K := K)).IsHomogeneous 6 := by
  unfold jDen
  have h1 : (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 2) K).IsHomogeneous 2 :=
    MvPolynomial.isHomogeneous_X_pow 0 2
  have h2 : (MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) K).IsHomogeneous 2 :=
    MvPolynomial.isHomogeneous_X_pow 1 2
  have h3 : ((MvPolynomial.X 1 - MvPolynomial.X 0 : MvPolynomial (Fin 2) K) ^ 2).IsHomogeneous 2 :=
    ((MvPolynomial.isHomogeneous_X (σ := Fin 2) (R := K) 1).sub
      (MvPolynomial.isHomogeneous_X (σ := Fin 2) (R := K) 0)).pow 2
  have := (h1.mul h2).mul h3
  simpa using this

/-- The two homogeneous coordinates of the degree 6 j-map P^1 -> P^1. -/
def jMap : Fin 2 → MvPolynomial (Fin 2) K := ![jNum (K := K), jDen (K := K)]

theorem jMap_isHomogeneous : ∀ i : Fin 2, (jMap (K := K) i).IsHomogeneous 6 := by
  intro i
  fin_cases i
  · simpa [jMap] using jNum_isHomogeneous (K := K)
  · simpa [jMap] using jDen_isHomogeneous (K := K)

theorem jNum_eval (lam : K) :
    (jNum (K := K)).eval ![lam, 1] = 256 * (1 - lam + lam ^ 2) ^ 3 := by
  simp [jNum]
  ring

theorem jDen_eval (lam : K) :
    (jDen (K := K)).eval ![lam, 1] = lam ^ 2 * (1 - lam) ^ 2 := by
  simp [jDen]

/-- The Legendre j-invariant is the quotient of the two homogeneous degree 6
coordinates evaluated at (lam, 1). -/
theorem legendreJ_eq_div (lam : K) :
    legendreJ lam = (jNum (K := K)).eval ![lam, 1] / (jDen (K := K)).eval ![lam, 1] := by
  rw [jNum_eval, jDen_eval]
  unfold legendreJ
  ring

/-- Upper height bound for the j-map (route section 6.3): the height of j(lam)
is at most 6 times the height of lam plus an absolute constant. -/
theorem logHeight_jHeight_le :
    ∃ C : ℝ, ∀ lam : K, jHeight lam ≤ C + 6 * lambdaHeight lam := by
  obtain ⟨C, hC⟩ := Height.logHeight_eval_le' (K := K) (p := jMap (K := K))
    (N := 6) jMap_isHomogeneous
  refine ⟨C, fun lam => ?_⟩
  have hx : (![lam, 1] : Fin 2 → K) = ![lam, 1] := rfl
  have hLe := hC (![lam, 1] : Fin 2 → K)
  have hleft : Height.logHeight (fun j : Fin 2 => (jMap (K := K) j).eval ![lam, 1])
      = jHeight lam := by
    have hfun : (fun j : Fin 2 => (jMap (K := K) j).eval ![lam, 1])
        = ![(jNum (K := K)).eval ![lam, 1], (jDen (K := K)).eval ![lam, 1]] := by
      funext j
      fin_cases j <;> simp [jMap]
    rw [hfun, jHeight, legendreJ_eq_div, Height.logHeight₁_div_eq_logHeight]
  have hright : Height.logHeight (![lam, 1] : Fin 2 → K) = lambdaHeight lam :=
    (Height.logHeight₁_eq_logHeight lam).symm
  rw [hleft, hright] at hLe
  exact hLe

end HeightBounds

#print axioms jNum_isHomogeneous
#print axioms jDen_isHomogeneous
#print axioms legendreJ_eq_div
#print axioms logHeight_jHeight_le
#print axioms lambdaHeight_nonneg
#print axioms jHeight_nonneg

end LeanFormal.IUT.XiFPaper.G1QHeightActual
end