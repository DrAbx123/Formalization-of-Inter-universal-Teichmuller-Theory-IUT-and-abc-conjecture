import tmp.sheaf.xif.paper.Mzk1DExactLowerActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import Mathlib.Tactic

/-!
# Mzk1DExactActual

Task-111: actual D_exact candidate and its L7 -> L6 interface.

Definition:
  nativeDExact T arch := nativeGlobalQPilotNormalizedLogMagnitude T + arch
                       = sum_b nativeBadLocalWeight T b * baseQLogMagnitude T b + arch.

This is the actual weighted local q log-magnitude plus an explicit arch parameter.
The arch parameter is NOT constructed here; it is an explicit input (missing arch
term in the tree).  The L7 lower target
  DExactLowerTarget C l D := (1 - 1/l) * log(C.p) <= D
is NOT proved from the actual data; it is the explicit conditional input hD.

The file proves the exact L7 -> L6 assembly for this actual D_exact:
  DExactLowerTarget + MestreOesterle + ThetaDataLegality + 0<=logp
    => L6ReducedInequality C l (nativeDExact T arch).

No sorry/axiom/True/PUnit/toy.  New file: report to Lead for extra-targets.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1DExactActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual weighted native q-pilot log-magnitude plus an explicit arch term. -/
noncomputable def nativeDExact (arch : Real) : Real :=
  nativeGlobalQPilotNormalizedLogMagnitude T + arch

/-- Exact expansion of nativeDExact as the weighted base-q log sum. -/
theorem nativeDExact_eq_weighted_sum (arch : Real) :
    nativeDExact T arch =
      (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * baseQLogMagnitude T b) + arch := by
  unfold nativeDExact
  rw [nativeGlobalQPilotNormalizedLogMagnitude_eq]

/-- The L7 -> L6 assembly for the actual D_exact, with the L7 target as an
explicit conditional input. -/
theorem nativeDExact_l6_of_l7
    (hMO : MestreOesterleBound)
    (C : PrimeConductorCurve)
    (lNat : Nat) (L : ThetaDataLegality C lNat)
    (arch : Real)
    (hD : DExactLowerTarget C (lNat : Real) (nativeDExact T arch))
    (hlogp : 0 <= Real.log (C.p : Real)) :
    L6ReducedInequality C (lNat : Real) (nativeDExact T arch) :=
  l6Reduced_of_dExactLower hMO C lNat L (nativeDExact T arch) hD hlogp

/-- The exact remaining L7 gap, stated without asserting it:
the actual D_exact must dominate (1 - 1/l) * log(C.p). -/
def NativeDExactL7Gap (C : PrimeConductorCurve) (lNat : Nat) (arch : Real) : Prop :=
  DExactLowerTarget C (lNat : Real) (nativeDExact T arch)

#check nativeDExact
#check nativeDExact_eq_weighted_sum
#check nativeDExact_l6_of_l7
#check NativeDExactL7Gap

end LeanFormal.IUT.XiFPaper.Mzk1DExactActual

end
