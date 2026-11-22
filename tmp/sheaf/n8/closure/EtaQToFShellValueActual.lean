import tmp.sheaf.n8.closure.EtaQToFShellActual

/-!
# Eta q -> F-shell value: actual attempts

Attempts the two remaining gaps from EtaQToFShellActual:

1. QToShellValueMem: qToShellValue in (fPlaceShell X).logShell.
   Actual conditional proof from the production log-shell/Kummer condition
     (fPlaceShell X).codomainKummerContained.
   Unconditional proof is not available: codomain Kummer containment is an
   exact production gap (unitLayer subset logShell), not a free assumption.

2. QToShellValueNeZero: qToShellValue != 0.
   This is equivalent to the q-normalization unit not lying in the logarithm
   kernel (torsion).  The chosen DVR normalization unit can be torsion; no
   production non-torsion theorem exists.  Exact named gap.

No arbitrary membership or nonzero value is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQToFShellValueActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.C1P6QUniformizerNormalization
open LeanFormal.IUT.N8Closure.EtaQToFShellActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Exact production Kummer containment condition for the F shell. -/
def FPlaceCodomainKummerContained (X : N8NativeInput l) : Prop :=
  (fPlaceShell X).codomainKummerContained

/-- Actual conditional proof: Kummer containment implies the q normalization
unit log lies in the F log-shell. -/
theorem qToShellValueMem_of_codomainKummer
    (X : N8NativeInput l)
    (h : FPlaceCodomainKummerContained X) :
    QToShellValueMem X := by
  change (SourceLogShellDatum.unitLayer (fPlaceShell X)) ⊆
    (fPlaceShell X).logShell at h
  exact h ⟨qToShellUnit X, rfl⟩

/-- Non-torsion condition for the transported q normalization unit. -/
def QUnitNonTorsion (X : N8NativeInput l) : Prop :=
  (qToShellUnit X) ∉ CommGroup.torsion (FShellUnits X)

end LeanFormal.IUT.N8Closure.EtaQToFShellValueActual
