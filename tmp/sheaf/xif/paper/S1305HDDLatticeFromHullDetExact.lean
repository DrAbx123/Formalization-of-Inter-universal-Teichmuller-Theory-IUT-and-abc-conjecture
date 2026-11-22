import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume

-- S1305: audit actual hull+det source versus S1215HDDLocalLattice.
-- Actual hull+det sources are finite packet determinant identities, matrix
-- log-det, source value-monoid hull and its log-volume; none produces a
-- local-field lattice family.  Therefore the first field stays exact; the
-- S1262/S1286/S1295 Fin-1 unit-section surrogate is NOT used.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1305HDDLatticeFromHullDetExact

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

/-- Exact type of the first HDD field.  No inhabitant is supplied. -/
abbrev S1305HDDLocalLatticeExactType : Type (v + 1) :=
  S1215HDDLocalLattice (I := I)

#check S1305HDDLocalLatticeExactType
#check HullDeterminantLogVolumeFrozenSpec
#check hullDeterminantLogVolumeFrozenSpec_holds
#check DetTensorPowerLogVolumeBookkeeping
#check Cor312ComparisonData
#check Theorem311Source.OriginalInput.sourceHolomorphicHull
#check Theorem311Source.OriginalInput.sourceHullVolume
#check Theorem311Source.OriginalInput.SourceCompactBound

end LeanFormal.IUT.XiFPaper.S1305HDDLatticeFromHullDetExact

end