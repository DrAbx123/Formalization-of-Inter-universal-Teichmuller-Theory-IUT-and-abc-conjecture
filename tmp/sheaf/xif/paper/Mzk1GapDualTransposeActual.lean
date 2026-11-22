import tmp.sheaf.xif.paper.Mzk1GeneralDualVolumeActual
/-! GAP-DUAL-TRANSPOSE status -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GapDualTransposeActual
def dualTransposeDonors : List String :=
  [ "integralTraceDualLattice_antitone", "coeSubmodule_differentIdeal_eq_inv_traceDual" ]
theorem dualTransposeDonors_length : dualTransposeDonors.length = 2 := rfl
def dualTransposeMissing : List String :=
  [ "B^{-T} O# formula", "SNF dual coefficient inversion" ]
theorem dualTransposeMissing_length : dualTransposeMissing.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1GapDualTransposeActual
end
