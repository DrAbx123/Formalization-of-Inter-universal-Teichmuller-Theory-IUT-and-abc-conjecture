import tmp.sheaf.xif.paper.Mzk1DExactActual
import Mathlib.Tactic

/-! # CONDITIONAL: L7 for nativeDExact is monotone in the arch parameter -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictL7ArchMonotoneActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1DExactActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Arch monotonicity: a lower target at arch0 transfers to any larger arch. -/
theorem DExactLowerTarget_nativeDExact_of_arch_le
    (C : PrimeConductorCurve) (lNat : Nat) {arch0 arch : Real}
    (hle : arch0 <= arch)
    (h : DExactLowerTarget C (lNat : Real) (nativeDExact T arch0)) :
    DExactLowerTarget C (lNat : Real) (nativeDExact T arch) := by
  unfold DExactLowerTarget nativeDExact at *
  linarith

#check DExactLowerTarget_nativeDExact_of_arch_le
end LeanFormal.IUT.XiFPaper.Mzk1P3DictL7ArchMonotoneActual
end
