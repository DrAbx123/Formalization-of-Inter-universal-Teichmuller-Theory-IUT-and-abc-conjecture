import tmp.sheaf.xif.paper.S2520RootCycleTransferActual
import tmp.sheaf.xif.paper.S2501MatrixPairEquivActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S2004RootTransferActual

open LeanFormal.IUT.XiFPaper.S2520RootCycleTransferActual
open LeanFormal.IUT.XiFPaper.S2501MatrixPairEquivActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual

/-- Actual splitting-field-to-closure root transfer: the cycle type of a
splitting-field root permutation is realised by an algebraic-closure
automorphism. -/
theorem S2004RootCycleTransfer : S2501RootCycleTransferRequired :=
  S2520RootCycleTransferRequired

/-- Consequently the S2132 root-cycle-type target implies the absolute
closure root-cycle target. -/
theorem S2004S2132ToS2480FirstMissing
    (h : S2132FrobInducesPairCycleType) :
    S2480FirstMissing :=
  S2501S2480FirstMissing_of_S2132_and_transfer h S2004RootCycleTransfer

#check S2004RootCycleTransfer
#check S2004S2132ToS2480FirstMissing
#print axioms S2004RootCycleTransfer
#print axioms S2004S2132ToS2480FirstMissing
end LeanFormal.IUT.XiFPaper.S2004RootTransferActual
end