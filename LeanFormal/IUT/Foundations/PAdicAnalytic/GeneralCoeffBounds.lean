import LeanFormal.IUT.Foundations.PAdicAnalytic.TateQSeriesGeneral

open PowerSeries

set_option linter.unusedSectionVars false
noncomputable section

/-!
# Coefficient integrality for the general Tate q-series C4K, C6K, DK

Task: for a complete nonarchimedean field K with K containing the needed
integer denominators, the formal series C4K, C6K and DK of qside's
TateQSeriesGeneral have all power-series coefficients of norm at most one:

  forall n, ||(C4K).coeff n|| <= 1,
  forall n, ||(C6K).coeff n|| <= 1,
  forall n, ||(DK).coeff n|| <= 1.

The proofs are direct instantiations of qside's PowerSeriesIntegral closure
lemmas (integral_C4K, integral_C6K, integral_DK); PowerSeriesIntegral f is
definitionally forall n, ||coeff n f|| <= 1.  The input is the integer-cast
integrality hint and the unit norm of 1728.  No production edit, no card.
-/

namespace LeanFormal.IUT.PAdicAnalytic.General

universe u

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  [CharZero K] [IsUltrametricDist K]

/-- Every coefficient of the formal series C4K has norm at most one. -/
theorem C4K_coeff_norm_le_one
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (n : ℕ) :
    ‖PowerSeries.coeff n (C4K (K := K))‖ ≤ 1 :=
  integral_C4K hint n

/-- Every coefficient of the formal series C6K has norm at most one. -/
theorem C6K_coeff_norm_le_one
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (n : ℕ) :
    ‖PowerSeries.coeff n (C6K (K := K))‖ ≤ 1 :=
  integral_C6K hint n

/-- Every coefficient of the formal discriminant series DK has norm at most
one; the inverse 1728 is used and its norm is required to be one. -/
theorem DK_coeff_norm_le_one
    (hint : ∀ n : ℕ, ‖(n : K)‖ ≤ 1) (h1728 : ‖(1728 : K)‖ = 1) (n : ℕ) :
    ‖PowerSeries.coeff n (DK (K := K))‖ ≤ 1 :=
  integral_DK hint h1728 n

end LeanFormal.IUT.PAdicAnalytic.General
