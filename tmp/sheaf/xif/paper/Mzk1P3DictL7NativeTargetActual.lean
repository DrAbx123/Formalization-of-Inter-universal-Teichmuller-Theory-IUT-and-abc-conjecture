import tmp.sheaf.xif.paper.Mzk1DExactActual
import tmp.sheaf.xif.paper.Mzk1P3DictCReverseNativeDExactActual
import Mathlib.Tactic

/-! # CONDITIONAL: nativeDExact L7 target -> L6 -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictL7NativeTargetActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1DExactActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- L7 target for the actual nativeDExact. -/
def nativeDExactL7Target (C : PrimeConductorCurve) (lNat : Nat) (arch : Real) : Prop :=
  DExactLowerTarget C (lNat : Real) (nativeDExact T arch)

/-- The target gives L6 for nativeDExact. -/
theorem nativeDExact_L6_of_target
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (lNat : Nat) (L : ThetaDataLegality C lNat) (arch : Real)
    (hD : nativeDExactL7Target (l := l) T C lNat arch)
    (hlogp : 0 <= Real.log (C.p : Real)) :
    L6ReducedInequality C (lNat : Real) (nativeDExact T arch) :=
  nativeDExact_l6_of_l7 (T := T) hMO C lNat L arch hD hlogp

#check nativeDExactL7Target
#check nativeDExact_L6_of_target
end LeanFormal.IUT.XiFPaper.Mzk1P3DictL7NativeTargetActual
end
