import tmp.sheaf.xif.paper.S2229RangeTransitivityActual
import tmp.sheaf.xif.paper.S2236GaloisPairTransitiveActual
import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2243RangeCompatibilityActual

open LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S2236GaloisPairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- The transported GL map is the identity: the `ZMod` transport is the
identity after `S1987Five.value = 5`. -/
theorem S2243GLMap_eq_id :
    S2229GLMap = MonoidHom.id (GL (Fin 2) (ZMod S1987Five.value)) := by
  ext g
  rfl

/-- The transferred range is exactly the original actual mod-5 range. -/
theorem S2243TransferredRange_eq
    (b : S1725TorsionBasis S1987Five) :
    S2229TransferredRange b =
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range := by
  unfold S2229TransferredRange
  rw [S2243GLMap_eq_id]
  exact Subgroup.map_id _

/-- The transferred-range / S2203 compatibility target is actual. -/
theorem S2243TransferredPairCompatibilityRequired_actual :
    S2229TransferredPairCompatibilityRequired := by
  unfold S2229TransferredPairCompatibilityRequired
    S2203RangePairTransitiveRequired
  rw [S2243TransferredRange_eq]
  exact S2218AffinePairTransitive_iff _

/-- The corresponding S2236 compatibility target is actual. -/
theorem S2243S2236RangeCompatibilityRequired_actual :
    S2236RangeCompatibilityRequired :=
  S2243TransferredPairCompatibilityRequired_actual

/-- Conditional D5 from the remaining Galois transitivity and cycle type;
the compatibility half is now actual. -/
theorem S2243D5LargeImageFive_of_galois
    (h : S2236GaloisTransitivityRequired)
    (hcycle : S2203RangeCycleTypeRequired S1982Basis) :
    S1987D5LargeImageFive :=
  S2229D5LargeImageFive_of_transferred h
    S2243TransferredPairCompatibilityRequired_actual hcycle

end LeanFormal.IUT.XiFPaper.S2243RangeCompatibilityActual

end
