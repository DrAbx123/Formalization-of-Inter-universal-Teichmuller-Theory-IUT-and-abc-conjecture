import tmp.sheaf.xif.paper.Mzk1DExactActual
import tmp.sheaf.xif.paper.Mzk1DExactLowerActual
import Mathlib.Tactic

/-! # CONDITIONAL: L7 for nativeDExact is exactly a lower bound on arch -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictL7ArchLowerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1DExactActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- L7 for nativeDExact is equivalent to an explicit lower bound on arch. -/
theorem DExactLowerTarget_nativeDExact_iff_arch_ge
    (C : PrimeConductorCurve) (lNat : Nat) (arch : Real) :
    DExactLowerTarget C (lNat : Real) (nativeDExact T arch) ↔
      (1 - 1 / (lNat : Real)) * Real.log (C.p : Real) -
          nativeGlobalQPilotNormalizedLogMagnitude T <= arch := by
  unfold DExactLowerTarget nativeDExact
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Sufficient arch lower bound gives L7. -/
theorem DExactLowerTarget_nativeDExact_of_arch_ge
    (C : PrimeConductorCurve) (lNat : Nat) (arch : Real)
    (h : (1 - 1 / (lNat : Real)) * Real.log (C.p : Real) -
          nativeGlobalQPilotNormalizedLogMagnitude T <= arch) :
    DExactLowerTarget C (lNat : Real) (nativeDExact T arch) :=
  (DExactLowerTarget_nativeDExact_iff_arch_ge (l := l) T C lNat arch).mpr h

#check DExactLowerTarget_nativeDExact_iff_arch_ge
#check DExactLowerTarget_nativeDExact_of_arch_ge
end LeanFormal.IUT.XiFPaper.Mzk1P3DictL7ArchLowerActual
end
