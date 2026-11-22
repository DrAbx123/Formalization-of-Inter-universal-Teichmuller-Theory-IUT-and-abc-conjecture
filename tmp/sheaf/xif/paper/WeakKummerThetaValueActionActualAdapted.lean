import tmp.sheaf.xif.paper.GlobalThetaPilotLogVolumeActual
import tmp.sheaf.xif.paper.FlUnitsThetaPilotActionActual

-- Weak Kummer action on Theta values and its log-magnitude effect
--
-- This is NOT a proof of Kummer group action equivalence. It constructs the
-- actual action of the finite-field unit group on the signed-label index of
-- the actual Theta values, proves its unit/multiplication laws, and proves the
-- resulting log-magnitude formula from the actual thetaValueFromQ/log_pow
-- identity. This is enough for direct log-magnitude inequalities; no group
-- action equivalence or full Kummer compatibility is claimed.
-- WRITE-ONLY: no local lake/lean.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.WeakKummerThetaValueActionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.FlUnitsThetaPilotActionActual
open LeanFormal.IUT.Foundations.Theta

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- Actual Theta-value action: act on the signed-label index by the actual
-- finite-field unit multiplication.
noncomputable def kummerThetaValueAction
    (u : (Fl l.value)ˣ) (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) : Real :=
  thetaValueFromQ T b (flUnitsSmulLabel u j)

theorem kummerThetaValueAction_pos
    (u : (Fl l.value)ˣ) (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    0 < kummerThetaValueAction T u b j :=
  thetaValueFromQ_pos T b (flUnitsSmulLabel u j)

theorem kummerThetaValueAction_one
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    kummerThetaValueAction T 1 b j = thetaValueFromQ T b j := by
  unfold kummerThetaValueAction
  rw [flUnitsSmulLabel_one]

theorem kummerThetaValueAction_mul
    (u v : (Fl l.value)ˣ) (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    kummerThetaValueAction T (u * v) b j =
      kummerThetaValueAction T u b (flUnitsSmulLabel v j) := by
  unfold kummerThetaValueAction
  rw [flUnitsSmulLabel_mul]

-- Actual log-magnitude effect: the log of the acted theta value is the actual
-- gauss exponent times the log of the actual base q real.
theorem log_kummerThetaValueAction
    (u : (Fl l.value)ˣ) (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    Real.log (kummerThetaValueAction T u b j) =
      ((gaussExponent (flUnitsSmulLabel u j).1).toNat : Real) *
        Real.log (baseQReal T b) :=
  log_thetaValueFromQ T b (flUnitsSmulLabel u j)

-- The acted theta value has the same base-q log form as the original theta
-- value, with the acted signed label.
theorem kummerThetaValueAction_log_eq
    (u : (Fl l.value)ˣ) (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    Real.log (kummerThetaValueAction T u b j) =
      ((gaussExponent (flUnitsSmulLabel u j).1).toNat : Real) *
        Real.log (baseQReal T b) := by
  rw [log_kummerThetaValueAction]

#check kummerThetaValueAction
#check kummerThetaValueAction_pos
#check kummerThetaValueAction_one
#check kummerThetaValueAction_mul
#check log_kummerThetaValueAction
#check kummerThetaValueAction_log_eq

end LeanFormal.IUT.XiFPaper.WeakKummerThetaValueActionActualAdapted

end