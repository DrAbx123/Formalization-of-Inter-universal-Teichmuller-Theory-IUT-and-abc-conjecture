import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-! # Native q norm / xi-f bound

The actual native q is LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X.  Its magnitude is
ArithmeticQPilotLogVolume.localLogMagnitude, and the production theorem
localLogMagnitude_eq_order_mul_log gives

  magnitude = order * log (LeanFormal.IUT.ArithmeticQPilotBaseChange.residueNormBase (LeanFormal.IUT.N8Closure.NativeC3.nativeFPlaceOverBad X)).

The required xi-f bound for l = 5 is

  2 * log 5 <= magnitude.

Neither order > 0 nor residueNormBase > 1 gives a factor 2 bound.  This file
records the actual reduction and the conditional consumer; it does not assert
the missing bound.  No arbitrary bound/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.NativeQNormActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe ua uv upi umon ui

variable {l : PrimeGeFive}

/-- The actual native q magnitude. -/
def nativeQLogMagnitude (X : N8NativeInput l) : Real :=
  ArithmeticQPilotLogVolume.localLogMagnitude (LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X)

/-- The actual native q norm. -/
def nativeQNorm (X : N8NativeInput l) : Real :=
  ‖(LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X).q‖

/-- The signed native q log is the negative magnitude. -/
theorem nativeQSignedLog_eq_neg_magnitude (X : N8NativeInput l) :
    ArithmeticQPilotLogVolume.localSignedLog (LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X) =
      -nativeQLogMagnitude X := by
  unfold nativeQLogMagnitude
  exact ArithmeticQPilotLogVolume.localSignedLog_eq_neg_magnitude
    (LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X)

/-- The actual magnitude is the order times the log of the actual residue norm
base. -/
theorem nativeQLogMagnitude_eq_order_mul_log (X : N8NativeInput l) :
    nativeQLogMagnitude X =
      ((LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X).order : Real) *
        Real.log (LeanFormal.IUT.ArithmeticQPilotBaseChange.residueNormBase (LeanFormal.IUT.N8Closure.NativeC3.nativeFPlaceOverBad X)) := by
  unfold nativeQLogMagnitude
  exact LeanFormal.IUT.ArithmeticQPilotBaseChange.localLogMagnitude_eq_order_mul_log (parameter := LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X)

/-- The exact missing Tate comparison q-norm theorem for xi-f at l = 5. -/
def NativeQTateNormBound (X : N8NativeInput l) : Prop :=
  2 * Real.log 5 ≤ nativeQLogMagnitude X

/-- The equivalent norm form of the missing bound. -/
def NativeQNormLeTwentyFifth (X : N8NativeInput l) : Prop :=
  nativeQNorm X ≤ (1 / 25 : Real)

/-- The missing Tate bound is exactly the required lower bound on the actual
q-pilot magnitude. -/
theorem nativeQTateNormBound_iff (X : N8NativeInput l) :
    NativeQTateNormBound X ↔
      2 * Real.log 5 ≤ nativeQLogMagnitude X := Iff.rfl

/-- Conditional consumer: once the missing Tate bound is supplied, the
q-pilot magnitude is at least 2 log 5. -/
theorem nativeQLogMagnitude_ge_two_log_five (X : N8NativeInput l)
    (h : NativeQTateNormBound X) :
    2 * Real.log 5 ≤ nativeQLogMagnitude X :=
  h

/-- Conditional norm consumer: the norm form is a separate missing analytic
evaluation; if supplied, it is consumed directly. -/
theorem nativeQNorm_le_twentyFifth_of_normBound (X : N8NativeInput l)
    (h : NativeQNormLeTwentyFifth X) :
    nativeQNorm X ≤ (1 / 25 : Real) :=
  h

end LeanFormal.IUT.XiFPaper.NativeQNormActual

end
