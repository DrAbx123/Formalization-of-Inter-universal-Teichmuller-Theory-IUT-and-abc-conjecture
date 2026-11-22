import tmp.sheaf.xif.paper.BaseQFamilyActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# Actual log-volume / valuation data for the native base q family

Uses the actual V_bad-indexed q family BaseQFamilyActual.nativeBaseQFamily, whose
q candidates live at the actual section lifts of the base bad places.  Defines
the pointwise log-magnitude, signed log, valuation object, and the finite total
signed log-volume (conditional on the source finiteness of V_bad), and proves
the actual formulas from the existing local q-log and order identities.

No inequality is asserted beyond the actual FinitePlaceQCandidate valuation
field.  No Missing-only structure.  No toy/True/PUnit/axiom/sorry.
WRITE-ONLY; no local compile; queued.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual base q candidate for a native bad place. -/
noncomputable def baseQ
    (b : Bad (nativePlaceSelection T)) :
    FinitePlaceQCandidate (nativeBaseSectionPlace T b) :=
  nativeBaseQFamily T b

/-- The actual local log-magnitude |log q| of the base q candidate. -/
noncomputable def baseQLogMagnitude
    (b : Bad (nativePlaceSelection T)) : Real :=
  localLogMagnitude (baseQ T b)

/-- The actual signed local log-volume log q of the base q candidate. -/
noncomputable def baseQSignedLog
    (b : Bad (nativePlaceSelection T)) : Real :=
  localSignedLog (baseQ T b)

/-- The actual valuation object of the base q candidate. -/
noncomputable def baseQValuation
    (b : Bad (nativePlaceSelection T)) :
    WithZero (Multiplicative Int) :=
  Valued.v (baseQ T b).q

/-- The base q candidate's actual norm formula, in terms of its exponent at the
section place. -/
theorem baseQ_qNorm_eq
    (b : Bad (nativePlaceSelection T)) :
    ‖(baseQ T b).q‖ =
      residueNormBase (nativeBaseSectionPlace T b) ^
        (-(baseQ T b).exponent : Int) :=
  qNorm_eq_residueNormBase_zpow (baseQ T b)

/-- The actual log-magnitude formula: order times the log residue norm. -/
theorem baseQLogMagnitude_eq_order_mul_log
    (b : Bad (nativePlaceSelection T)) :
    baseQLogMagnitude T b =
      ((baseQ T b).order : Real) *
        Real.log (residueNormBase (nativeBaseSectionPlace T b)) :=
  localLogMagnitude_eq_order_mul_log (baseQ T b)

/-- The base q log-magnitude is positive. -/
theorem baseQLogMagnitude_pos
    (b : Bad (nativePlaceSelection T)) :
    0 < baseQLogMagnitude T b :=
  localLogMagnitude_pos (baseQ T b)

/-- The signed base q log-volume is the negative log-magnitude. -/
theorem baseQSignedLog_eq_neg_logMagnitude
    (b : Bad (nativePlaceSelection T)) :
    baseQSignedLog T b = -baseQLogMagnitude T b :=
  localSignedLog_eq_neg_magnitude (baseQ T b)

/-- The valuation object is exactly the actual q valuation. -/
theorem baseQValuation_eq
    (b : Bad (nativePlaceSelection T)) :
    baseQValuation T b = Valued.v (baseQ T b).q := rfl

/-- The actual valuation of the base q candidate is < 1, from the actual
FinitePlaceQCandidate field. -/
theorem baseQValuation_lt_one
    (b : Bad (nativePlaceSelection T)) :
    baseQValuation T b < 1 :=
  (baseQ T b).valuation_lt_one

/-- The base q's order is the actual positive order of the source candidate. -/
theorem baseQ_order_pos
    (b : Bad (nativePlaceSelection T)) :
    0 < (baseQ T b).order :=
  (baseQ T b).order_pos

/-- The finite total signed log-volume of the base q family, conditional on the
source finiteness of V_bad. -/
noncomputable def baseQTotalSignedLog
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  ∑ b : Bad (nativePlaceSelection T), baseQSignedLog T b

/-- The finite total log-magnitude of the base q family, conditional on the
source finiteness of V_bad. -/
noncomputable def baseQTotalLogMagnitude
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  ∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b

/-- The total signed log-volume is the sum of the pointwise signed logs. -/
theorem baseQTotalSignedLog_eq_sum
    [Fintype (Bad (nativePlaceSelection T))] :
    baseQTotalSignedLog T =
      ∑ b : Bad (nativePlaceSelection T), baseQSignedLog T b := rfl

/-- The total log-magnitude is the sum of the pointwise magnitudes. -/
theorem baseQTotalLogMagnitude_eq_sum
    [Fintype (Bad (nativePlaceSelection T))] :
    baseQTotalLogMagnitude T =
      ∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b := rfl

/-- The actual total signed log-volume is the negative total log-magnitude. -/
theorem baseQTotalSignedLog_eq_neg_totalLogMagnitude
    [Fintype (Bad (nativePlaceSelection T))] :
    baseQTotalSignedLog T = -baseQTotalLogMagnitude T := by
  simp only [baseQTotalSignedLog, baseQTotalLogMagnitude,
    baseQSignedLog_eq_neg_logMagnitude, Finset.sum_neg_distrib]

end LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
