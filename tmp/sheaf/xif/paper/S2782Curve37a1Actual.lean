import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

noncomputable section
open LeanFormal.IUT
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2782Curve37a1Actual

/-- 37a1: y² + y = x³ - x over Q. -/
def E37 : WeierstrassCurve ℚ :=
  WeierstrassCurve.mk 0 0 1 (-1) 0

@[simp] theorem E37_a1 : E37.a₁ = 0 := rfl
@[simp] theorem E37_a2 : E37.a₂ = 0 := rfl
@[simp] theorem E37_a3 : E37.a₃ = 1 := rfl
@[simp] theorem E37_a4 : E37.a₄ = -1 := rfl
@[simp] theorem E37_a6 : E37.a₆ = 0 := rfl

theorem E37_discriminant : E37.Δ = (37 : ℚ) := by
  norm_num [E37, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem E37_c4 : E37.c₄ = (48 : ℚ) := by
  norm_num [E37, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]

theorem E37_discriminant_ne_zero : E37.Δ ≠ 0 := by
  rw [E37_discriminant]; norm_num

instance E37_isElliptic : E37.IsElliptic :=
  ⟨by rw [isUnit_iff_ne_zero]; exact E37_discriminant_ne_zero⟩

theorem E37_j : E37.j = (110592 / 37 : ℚ) := by
  rw [WeierstrassCurve.j]
  have hΔ : E37.Δ' = Units.mk0 (37 : ℚ) (by norm_num) := Units.ext E37_discriminant
  rw [hΔ, E37_c4]
  norm_num

/-- The Gaussian base change of 37a1. -/
noncomputable def E37Qi : WeierstrassCurve GaussianField :=
  E37.baseChange GaussianField

theorem E37Qi_discriminant : E37Qi.Δ = (37 : GaussianField) := by
  rw [E37Qi, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, E37_discriminant]
  exact map_natCast (algebraMap ℚ GaussianField) 37

theorem E37Qi_c4 : E37Qi.c₄ = (48 : GaussianField) := by
  rw [E37Qi, WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, E37_c4]
  exact map_natCast (algebraMap ℚ GaussianField) 48

/-- Numerical semistable data for 37a1: discriminant 37, c4 = 48, good away
from 37, and the 37-adic discriminant has exact valuation one.  This is a
numerical interface; the stronger Mathlib `HasGoodReduction` /
`HasMultiplicativeReduction` classes additionally require minimality over
`Z_[p]` and are not asserted here. -/
structure S2782SemistableData where
  discr : ℚ
  discr_eq : discr = 37
  badPrime : ℕ
  badPrime_eq : badPrime = 37
  c4 : ℚ
  c4_eq : c4 = 48
  good_away : ∀ p : ℕ, p.Prime → p ≠ 37 → ¬ (p : ℤ) ∣ (37 : ℤ)
  mult_at_37 : (37 : ℤ) ∣ (37 : ℤ) ∧ ¬ ((37 : ℤ) ^ 2 ∣ (37 : ℤ))

/-- The actual numerical semistable data of 37a1. -/
def S2782semistableData : S2782SemistableData where
  discr := E37.Δ
  discr_eq := E37_discriminant
  badPrime := 37
  badPrime_eq := rfl
  c4 := E37.c₄
  c4_eq := E37_c4
  good_away := by
    intro p hp hne hdiv
    have hp37 : p ∣ 37 := by exact_mod_cast hdiv
    have h37 : Nat.Prime 37 := by norm_num
    rcases (Nat.dvd_prime h37).mp hp37 with h1 | h37eq
    · exact hp.ne_one h1
    · exact hne h37eq
  mult_at_37 := by norm_num

theorem S2782semistableData_discr :
    S2782semistableData.discr = 37 :=
  S2782semistableData.discr_eq

#check E37
#check E37_discriminant
#check E37_j
#check E37Qi
#print axioms E37_discriminant
#print axioms E37_j

end LeanFormal.IUT.XiFPaper.S2782Curve37a1Actual
end
