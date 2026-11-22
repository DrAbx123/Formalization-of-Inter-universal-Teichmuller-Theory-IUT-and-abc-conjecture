import tmp.sheaf.xif.paper.Mzk1DExactActual
import tmp.sheaf.xif.paper.Mzk1DExactLowerActual
import tmp.sheaf.xif.paper.Mzk1P3DictL7ArchMonotoneActual
import Mathlib.Tactic

/-! # CONDITIONAL: L7 + arch monotonicity => SSIneqExplicit -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictL7SSIneqArchActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1DExactActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictL7ArchMonotoneActual
open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- L7 at arch0 + arch0<=arch gives SSIneqExplicit at arch. -/
theorem ssIneqExplicit_nativeDExact_of_arch_le
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (lNat : Nat) (L : ThetaDataLegality C lNat) {arch0 arch : Real}
    (hle : arch0 <= arch)
    (hD : DExactLowerTarget C (lNat : Real) (nativeDExact T arch0))
    (hlogp : 0 <= Real.log (C.p : Real)) :
    SSIneqExplicit (sL (lNat : Real)) ((C.e : Real) * Real.log (C.p : Real))
      (lNat : Real) ((((lNat : Real) + 5) / 4) * nativeDExact T arch) := by
  have hD' : DExactLowerTarget C (lNat : Real) (nativeDExact T arch) :=
    DExactLowerTarget_nativeDExact_of_arch_le T C lNat hle hD
  exact ssIneqExplicit_of_dExactLower hMO C lNat L (nativeDExact T arch) hD' hlogp

#check ssIneqExplicit_nativeDExact_of_arch_le
end LeanFormal.IUT.XiFPaper.Mzk1P3DictL7SSIneqArchActual
end
