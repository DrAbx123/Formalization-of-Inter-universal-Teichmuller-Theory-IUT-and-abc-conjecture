import tmp.sheaf.xif.paper.QVFamThetaImageActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-! # Actual same-source qVFamily scaling lambda

For each native bad place b, the actual qVFamily q is a nonzero completion
element.  Its completion unit

  qVFamilyCompletionUnit b = Units.mk0 (qVFamily T b).q (q_ne_zero)

is the actual same-source scaling lambda.  It is a non-integral unit:
the qVFamily candidate is contracting, so its valuation is < 1 and its norm is
< 1; hence the unit is not 1 and the multiplicative log ratio is nonzero.

The product carrier lambda is

  qVFamilyScalingLambda b = ofAdd (log ||unit_b||),

with actual log ratio

  log ||unit_b|| = localSignedLog (qVFamily T b),

i.e. exactly the q-pilot signed scalar at b.  No lambda = 1 assumption, no
cross-theater equality, no fake.  No sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamThetaScalingActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.QVFamThetaImageActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual qVFamily q completion unit. -/
noncomputable def qVFamilyCompletionUnit :
    (Completion ((nativeBadLift T).lift b))ˣ :=
  Units.mk0 (qVFamily T b).q (qVFamily T b).q_ne_zero

/-- The qVFamily completion unit is the actual qVFamily q. -/
theorem qVFamilyCompletionUnit_apply :
    (qVFamilyCompletionUnit T b : Completion ((nativeBadLift T).lift b)) =
      (qVFamily T b).q := rfl

/-- The actual qVFamily q has valuation < 1 (contracting, non-integral unit). -/
theorem qVFamily_valuation_lt_one :
    Valued.v (qVFamily T b).q < 1 :=
  (qVFamily T b).valuation_lt_one

/-- The qVFamily completion unit has norm < 1. -/
theorem qVFamilyCompletionUnit_norm_lt_one :
    ‖(qVFamilyCompletionUnit T b : Completion ((nativeBadLift T).lift b))‖ < 1 := by
  rw [qVFamilyCompletionUnit_apply]
  exact qNorm_lt_one (qVFamily T b)

/-- The qVFamily completion unit is not the identity unit. -/
theorem qVFamilyCompletionUnit_ne_one :
    qVFamilyCompletionUnit T b ≠ 1 := by
  intro h
  have hnorm : ‖(qVFamilyCompletionUnit T b :
      Completion ((nativeBadLift T).lift b))‖ = 1 := by
    rw [h]
    simp
  linarith [qVFamilyCompletionUnit_norm_lt_one T b]

/-- The actual log ratio of the qVFamily completion unit is the qVFamily local
signed log. -/
theorem log_norm_qVFamilyCompletionUnit_eq_localSignedLog :
    Real.log ‖(qVFamilyCompletionUnit T b :
      Completion ((nativeBadLift T).lift b))‖ =
      localSignedLog (qVFamily T b) := by
  rw [qVFamilyCompletionUnit_apply]
  rfl

/-- The log ratio is nonzero: the qVFamily unit is contracting. -/
theorem log_norm_qVFamilyCompletionUnit_ne_zero :
    Real.log ‖(qVFamilyCompletionUnit T b :
      Completion ((nativeBadLift T).lift b))‖ ≠ 0 := by
  rw [log_norm_qVFamilyCompletionUnit_eq_localSignedLog]
  exact ne_of_lt (localSignedLog_neg (qVFamily T b))

/-- The actual same-source product scaling lambda in the product value carrier. -/
noncomputable def qVFamilyScalingLambda : QVFamProductPoint T :=
  fun b => Multiplicative.ofAdd
    (Real.log ‖(qVFamilyCompletionUnit T b :
      Completion ((nativeBadLift T).lift b))‖)

/-- Each component of the scaling lambda has additive log equal to the qVFamily
local signed log. -/
theorem qVFamilyScalingLambda_toAdd :
    (qVFamilyScalingLambda T b).toAdd =
      localSignedLog (qVFamily T b) := by
  unfold qVFamilyScalingLambda
  rw [qVFamilyCompletionUnit_apply]
  rfl

/-- Each component of the scaling lambda is nontrivial. -/
theorem qVFamilyScalingLambda_ne_one_at (b : Bad (nativePlaceSelection T)) :
    qVFamilyScalingLambda T b ≠ 1 := by
  intro h
  have hzero : (qVFamilyScalingLambda T b).toAdd = 0 := by
    rw [h]
    rfl
  rw [qVFamilyScalingLambda_toAdd] at hzero
  exact (ne_of_lt (localSignedLog_neg (qVFamily T b))) hzero

/-- The actual q-pilot signed scalar equals the scaling lambda log component. -/
theorem qVFamilySignedLog_eq_scalingLambda_toAdd :
    qVFamilySignedLog T b = (qVFamilyScalingLambda T b).toAdd := by
  unfold qVFamilySignedLog
  rw [qVFamilyScalingLambda_toAdd]

/-- The actual scaling data from the qVFamily completion unit. -/
structure QVFamScalingData where
  unit : (Completion ((nativeBadLift T).lift b))ˣ
  unit_eq : unit = qVFamilyCompletionUnit T b
  lambda : QVFamProductPoint T
  lambda_eq : lambda = qVFamilyScalingLambda T
  logRatio : Real
  logRatio_eq : logRatio =
    Real.log ‖(qVFamilyCompletionUnit T b :
      Completion ((nativeBadLift T).lift b))‖
  logRatio_eq_localSignedLog : logRatio = localSignedLog (qVFamily T b)

/-- The actual scaling data constructor. -/
noncomputable def qvFamScalingData :
    QVFamScalingData T b where
  unit := qVFamilyCompletionUnit T b
  unit_eq := rfl
  lambda := qVFamilyScalingLambda T
  lambda_eq := rfl
  logRatio := Real.log ‖(qVFamilyCompletionUnit T b :
    Completion ((nativeBadLift T).lift b))‖
  logRatio_eq := rfl
  logRatio_eq_localSignedLog :=
    log_norm_qVFamilyCompletionUnit_eq_localSignedLog T b

end LeanFormal.IUT.XiFPaper.QVFamThetaScalingActualAdapted

end
