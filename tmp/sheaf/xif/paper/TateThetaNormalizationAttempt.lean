import tmp.sheaf.xif.paper.TateThetaOddCoefficientAttempt

noncomputable section
open LeanFormal.IUT.TateCurve
open LeanFormal.IUT.XiFPaper.TateThetaOddCoefficientAttempt
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.TateThetaNormalizationAttempt

universe u

variable {K : Type u} [NormedField K]

/-- The correction series s(q) of the Tate normalization erratum. -/
noncomputable def tateS (q : K) : K :=
  ∑' n : Nat, q ^ (n + 1) / (1 - q ^ (n + 1)) ^ 2

/-- Canonical normalized X coordinate. -/
noncomputable def tateXnorm (q u : K) : K :=
  coordinateSeries q u - 2 * tateS q

/-- Canonical normalized Y coordinate. -/
noncomputable def tateYnorm (q u : K) : K :=
  yCoordinateSeries q u + tateS q

/-- Canonical odd coordinate O = 2Y + X; the correction cancels. -/
noncomputable def tateOnorm (q u : K) : K :=
  2 * tateYnorm q u + tateXnorm q u

theorem tateOnorm_eq_two_mul_y_add_x (q u : K) :
    tateOnorm q u = 2 * yCoordinateSeries q u + coordinateSeries q u := by
  unfold tateOnorm tateYnorm tateXnorm
  ring

def normalizedQ0X (u : K) : K := oddIdentityQ0X u
def normalizedQ0O (u : K) : K := oddIdentityQ0O u
def normalizedQ1X (u : K) : K := u + u⁻¹ - 2
def normalizedQ1O (u : K) : K := u - u⁻¹

theorem S3129_normalized_q0 (u : K) (hu : 1 - u ≠ 0) :
    normalizedQ0O u ^ 2 = 4 * normalizedQ0X u ^ 3 + normalizedQ0X u ^ 2 :=
  S3128_oddIdentity_q0 u hu

def normalizedQ1LHS (u : K) : K :=
  2 * normalizedQ0O u * normalizedQ1O u

/-- q^1 RHS with the OLD raw a4/a6 coefficients (-5, -1). -/
def normalizedQ1RHS_oldCoeffs (u : K) : K :=
  12 * normalizedQ0X u ^ 2 * normalizedQ1X u +
    2 * normalizedQ0X u * normalizedQ1X u -
    20 * normalizedQ0X u - 4

theorem S3129_normalized_q1 (u : K) (hu : u ≠ 0) (h1 : 1 - u ≠ 0) :
    normalizedQ1LHS u = normalizedQ1RHS_oldCoeffs u := by
  unfold normalizedQ1LHS normalizedQ1RHS_oldCoeffs
    normalizedQ0X normalizedQ0O normalizedQ1X normalizedQ1O
    oddIdentityQ0X oddIdentityQ0O
  field_simp [hu, h1]
  ring

/-- Parameterized corrected normalized target; the corrected a4/a6 are NOT
chosen by this file. -/
def TateThetaOddIdentityNormalizedTarget (a4n a6n : K) (q u : K) : Prop :=
  tateOnorm q u ^ 2 =
    4 * tateXnorm q u ^ 3 + tateXnorm q u ^ 2 +
      4 * a4n * tateXnorm q u + 4 * a6n


def normalizedQ2X (u : K) : K :=
  2 * u ^ 2 + 2 * u⁻¹ ^ 2 + u + u⁻¹ - 6

def normalizedQ2O (u : K) : K :=
  4 * u ^ 2 - 4 * u⁻¹ ^ 2 + u - u⁻¹

def normalizedQ2LHS (u : K) : K :=
  normalizedQ1O u ^ 2 + 2 * normalizedQ0O u * normalizedQ2O u

def normalizedQ2RHS (u : K) : K :=
  12 * normalizedQ0X u ^ 2 * normalizedQ2X u +
    12 * normalizedQ0X u * normalizedQ1X u ^ 2 +
    normalizedQ1X u ^ 2 +
    2 * normalizedQ0X u * normalizedQ2X u -
    180 * normalizedQ0X u -
    20 * normalizedQ1X u - 92

theorem S3129_normalized_q2 (u : K) (hu : u ≠ 0) (h1 : 1 - u ≠ 0) :
    normalizedQ2LHS u = normalizedQ2RHS u := by
  unfold normalizedQ2LHS normalizedQ2RHS
    normalizedQ0X normalizedQ0O normalizedQ1X normalizedQ1O
    normalizedQ2X normalizedQ2O oddIdentityQ0X oddIdentityQ0O
  field_simp [hu, h1]
  ring


def normalizedQ3X (u : K) : K :=
  3 * u ^ 3 + 3 * u⁻¹ ^ 3 + u + u⁻¹ - 8

def normalizedQ3O (u : K) : K :=
  9 * u ^ 3 - 9 * u⁻¹ ^ 3 + u - u⁻¹

def normalizedQ3LHS (u : K) : K :=
  2 * normalizedQ0O u * normalizedQ3O u +
    2 * normalizedQ1O u * normalizedQ2O u

def normalizedQ3RHS (u : K) : K :=
  12 * normalizedQ0X u ^ 2 * normalizedQ3X u +
    24 * normalizedQ0X u * normalizedQ1X u * normalizedQ2X u +
    4 * normalizedQ1X u ^ 3 +
    2 * normalizedQ1X u * normalizedQ2X u +
    2 * normalizedQ0X u * normalizedQ3X u -
    20 * normalizedQ2X u -
    180 * normalizedQ1X u -
    560 * normalizedQ0X u - 616

theorem S3129_normalized_q3 (u : K) (hu : u ≠ 0) (h1 : 1 - u ≠ 0) :
    normalizedQ3LHS u = normalizedQ3RHS u := by
  unfold normalizedQ3LHS normalizedQ3RHS
    normalizedQ0X normalizedQ0O normalizedQ1X normalizedQ1O
    normalizedQ2X normalizedQ2O normalizedQ3X normalizedQ3O
    oddIdentityQ0X oddIdentityQ0O
  field_simp [hu, h1]
  ring

#check tateS
#check tateXnorm
#check tateYnorm
#check tateOnorm
#check tateOnorm_eq_two_mul_y_add_x
#check S3129_normalized_q0
#check S3129_normalized_q1
#check TateThetaOddIdentityNormalizedTarget
#print axioms S3129_normalized_q0
#print axioms S3129_normalized_q1

end LeanFormal.IUT.XiFPaper.TateThetaNormalizationAttempt
end