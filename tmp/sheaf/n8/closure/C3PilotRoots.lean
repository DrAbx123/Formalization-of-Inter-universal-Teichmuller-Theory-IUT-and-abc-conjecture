import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.n8.closure.C3Roots

/-!
# C3 pilot roots in the algebraic closure

For the actual C3 q-unit in a finite-place completion, construct the natural
root system in the algebraic closure of the completion.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C3PilotRoots

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : Theorem311Source.OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual C3 q-unit mapped into the algebraic closure of its completion. -/
noncomputable def qUnitAlgClosed :=
  unitToAlgClosed C3.qUnit

/-- Correct-domain natural root system of the actual C3 q-unit. -/
noncomputable def qRootSystem :=
  algClosedRootSystem C3.qUnit

theorem qRootSystem_pow_self (n : Nat) (hn : n ≠ 0) :
    (qRootSystem C3).root n ^ n = qUnitAlgClosed C3 :=
  NatRootSystem.pow_self (qRootSystem C3) n hn

end LeanFormal.IUT.N8Closure.C3PilotRoots