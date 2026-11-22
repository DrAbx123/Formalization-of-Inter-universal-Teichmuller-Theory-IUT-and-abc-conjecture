import tmp.sheaf.xif.paper.S442DvCoverNormPullbackActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S449NormPullbackGroupActual

open LeanFormal.IUT.XiFPaper.S442DvCoverNormPullbackActual

universe u

variable {K : Type u} [Field K]
variable (L : Type u) [Field L] [Algebra K L]

/-- Exact obstruction data for using normPullback as the model rational-function
pullback: identity is proved, but composition/injectivity/FSM bijectivity still
require genuine norm-tower and norm-injectivity results. -/
structure NormPullbackGroupLaws (K : Type u) [Field K]
    (L : Type u) [Field L] [Algebra K L] where
  norm_comp : Prop
  norm_injective : Prop
  norm_fsm_bijective : Prop

def NormPullbackGroupLawsRequired : Prop :=
  Nonempty (NormPullbackGroupLaws (K := K) L)

end LeanFormal.IUT.XiFPaper.S449NormPullbackGroupActual
end
