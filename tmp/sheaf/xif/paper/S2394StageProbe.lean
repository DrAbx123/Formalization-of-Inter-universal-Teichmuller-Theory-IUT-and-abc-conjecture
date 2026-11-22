import tmp.sheaf.xif.paper.S2200TransferNaturalityActual
import tmp.sheaf.xif.paper.S2179StageConjEquivActual

noncomputable section
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual
open LeanFormal.IUT.XiFPaper.S2173StageConjugationActual

namespace TestStage
variable (p : Nat) [Fact (Nat.Prime p)]

example (g : Gv p) (H : Index p) :
    S2179StageConj p g H =
      (torsionCongr (abelianizationCongr (S2200ConjEquiv p g H))).toAdditive := by
  unfold S2179StageConj S2200ConjEquiv
  rfl

end TestStage
