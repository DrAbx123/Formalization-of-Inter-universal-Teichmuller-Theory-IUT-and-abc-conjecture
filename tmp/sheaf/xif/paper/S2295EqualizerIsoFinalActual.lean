import tmp.sheaf.xif.paper.S2285RMapNatActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2285RMapNatActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2295EqualizerIsoFinalActual

variable (S : Iut.SchemeOverField S1726K)

-- The pointwise limit comparison was attempted as
-- limitObjIsoLimitCompEvaluation (parallelPair (S2285f S M) (S2285g S N)) T,
-- but its codomain is the limit of the evaluated functor diagram
-- (parallelPair f g) ⋙ evaluation T, not the pointwise parallelPair
-- (f.app T) (g.app T).  The required diagram comparison is missing.
#check S2285R_map_apply
#check S2285f
#check S2285g
#check S2285f_natural
#check S2285g_natural

end LeanFormal.IUT.XiFPaper.S2295EqualizerIsoFinalActual

end
