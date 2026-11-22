/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A618ScalingObstructionActual

/-!
# A645 CANONICAL A618-obstruction thin re-export (mainline)

`Mzk1A618MachineProofActual` (abc lane) is superseded as canonical by
`Mzk1A618ScalingObstructionActual.identity_scaleShift_obstruction` (unit-region form,
gate trio).  This file is a thin, read-only re-export of that canonical obstruction for
downstream consumers that should not rebuild the geometric argument.

No new mathematics; no object changed; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1A618CanonicalObstructionReexportActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open Mzk1A618ScalingObstructionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **Canonical A618 obstruction (re-export)**: with the actual hull interface
  (`scaleShift = id`) and the triple-independent unit region, the height comparison is
  false for every `ε`. -/
theorem canonical_obstruction (epsilon : ℝ) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * (s1902LogVolume T (s1902UnitRegion T)).toReal) :=
  identity_scaleShift_obstruction T epsilon

end LeanFormal.IUT.XiFPaper.Mzk1A618CanonicalObstructionReexportActual

end

/-! ### Axiom gate (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1A618CanonicalObstructionReexportActual.canonical_obstruction