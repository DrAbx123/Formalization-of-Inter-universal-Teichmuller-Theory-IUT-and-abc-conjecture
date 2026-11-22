/- Derivation attempt for the residual Node09 inputs.
This file deliberately attempts to derive horder/hcoef/hbase from actual qV/Padic
data.  If a theorem is not derivable, the watchdog first error is reported; no
stand-ins, no extra hypotheses, no fake. -/
import tmp.sheaf.xif.paper.Node09ResidualInputsActual
import tmp.sheaf.xif.paper.Mzk1PadicFieldValuedQpActual
import tmp.sheaf.xif.paper.RelativeNormCompletion
import tmp.sheaf.xif.paper.RelativeNormFieldNormActual
import tmp.sheaf.xif.paper.Mzk1PerPlaceInequalityActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1PadicFieldValuedBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1PadicFieldValuedQpActual
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion

namespace LeanFormal.IUT.XiFPaper.Node09ResidualDerivationActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]

/-- Attempt: derive horder from the actual clause-B q family.  The clause-B
q comparison supplies only 0 < order and coprimality to l; q_order_prime_to_l.
No equality to 1 is available, so this is the first derivation blocker. -/
theorem horder_actual
    (b : Bad (nativePlaceSelection X.S)) :
    (qVFamily X.S b).order = 1 := by
  have hpos : 0 < (qVFamily X.S b).order :=
    (qVFamily X.S b).order_pos
  omega

/-- Attempt: hbase from PadicValuedCoherence.  The Qp donor only covers K=Qp;
NativeBaseCompletionRaw is a general finite extension, so the general
coherence is not supplied by the Qp theorem. -/
def hbase_actual_attempt : List String :=
  [ "Qp case: padicValuedCoherence_qp supplies PadicValuedCoherence (K := Qp)",
    "NativeBaseCompletionRaw is a finite extension of Qp, not definitionally Qp",
    "no general PadicValuedCoherence donor for NativeBaseCompletionRaw in tree" ]

/-- Attempt: hcoef.  Mzk1PerPlaceInequalityActual records a counterexample to
the per-place CoeffComparison, so hcoef cannot be derived unconditionally. -/
def hcoef_actual_attempt : List String :=
  [ "Mzk1PerPlaceInequalityActual records a counterexample to CoeffComparison",
    "hcoef is not derivable unconditionally from actual qV/Padic data" ]

end LeanFormal.IUT.XiFPaper.Node09ResidualDerivationActual
end
