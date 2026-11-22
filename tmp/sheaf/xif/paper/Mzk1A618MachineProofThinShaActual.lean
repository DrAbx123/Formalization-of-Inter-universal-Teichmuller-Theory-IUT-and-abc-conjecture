import tmp.sheaf.xif.paper.Mzk1A618ScalingObstructionActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual

/-!
# shehdd A645 A618 machine-proof thin re-export (Sha, green)

Thin read-only re-export of the GREEN machine-checked A618 obstruction
(`Mzk1A618ScalingObstructionActual.identity_scaleShift_obstruction`): with the
actual S1902 hull interface (`scaleShift = id`) and the triple-independent unit
region, no height comparison holds.

Note: the mainline-owned `Mzk1A618MachineProofActual` is currently red (see
`Mzk1A618MachineProofAuditShaActual`: it references the non-existent
`comparisonRegion_eq_hull` and applies the hull-region obstruction to a
unit-region∪{point} region).  This file is the thin re-export of the green result,
not a proof of the mainline file's statement.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1A618MachineProofThinShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open Mzk1A618ScalingObstructionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Thin re-export: the id-scaleShift interface cannot support the height comparison
with the triple-independent unit region (machine-checked A618 obstruction). -/
theorem a618_machine_obstruction_thin (epsilon : Real) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * (s1902LogVolume T (s1902UnitRegion T)).toReal) :=
  identity_scaleShift_obstruction T epsilon

end LeanFormal.IUT.XiFPaper.Mzk1A618MachineProofThinShaActual

/-! ### Axiom gate -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1A618MachineProofThinShaActual.a618_machine_obstruction_thin
