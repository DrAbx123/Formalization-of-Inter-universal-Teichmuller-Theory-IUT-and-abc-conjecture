import tmp.sheaf.xif.paper.TateThetaProductAttempt

noncomputable section
open LeanFormal.IUT.XiFPaper.TateThetaProductAttempt
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.TateThetaAdditionAttempt

universe u

variable {K : Type u} [NormedField K]

/-- Abstract addition target: the caller must supply the actual theta addition
coefficient.  No coefficient is chosen by the library. -/
def TateThetaAdditionTarget (q : K) (coeff : K -> K -> K) : Prop :=
  forall u v : K,
    tateThetaProduct q (u * v) * tateThetaProduct q (u / v) =
      coeff u v * tateThetaProduct q u ^ 2 * tateThetaProduct q v ^ 2

/-- Duplication target, parameterized by the actual duplication coefficient. -/
def TateThetaDuplicationTarget (q : K) (coeff : K -> K) : Prop :=
  forall u : K,
    tateThetaProduct q (u ^ 2) = coeff u * tateThetaProduct q u ^ 2

#check TateThetaAdditionTarget
#check TateThetaDuplicationTarget

end LeanFormal.IUT.XiFPaper.TateThetaAdditionAttempt
end