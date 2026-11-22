import tmp.sheaf.xif.paper.Mzk1P3DictCEquivUnderL7Actual
import tmp.sheaf.xif.paper.Mzk1DExactActual
import Mathlib.Tactic

/-! # CONDITIONAL: DICT-C box <=> L6 for actual nativeDExact -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictCReverseNativeDExactActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P3DictCEquivUnderL7Actual
open LeanFormal.IUT.XiFPaper.Mzk1DExactActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- With D=nativeDExact T arch and L7, boxSlack>=0 is equivalent to L6. -/
theorem boxSlack_iff_L6_nativeDExact_of_L7
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (lNat : Nat) (L : ThetaDataLegality C lNat)
    (arch D Q S Tstar : Real)
    (hD : D = nativeDExact T arch)
    (hL7 : DExactLowerTarget C (lNat : Real) (nativeDExact T arch))
    (hlogp : 0 <= Real.log (C.p : Real))
    (hl : 5 <= (lNat : Real)) (hS : 0 <= S) (hT : 0 <= Tstar) :
    0 <= boxSlack (lNat : Real) D Q S Tstar <->
      L6ReducedInequality C (lNat : Real) D := by
  have h := boxSlack_iff_L6_of_L7 hMO C lNat L D
    (nativeDExact T arch) Q S Tstar hD hL7 hlogp hl hS hT
  exact h

#check boxSlack_iff_L6_nativeDExact_of_L7
end LeanFormal.IUT.XiFPaper.Mzk1P3DictCReverseNativeDExactActual
end
