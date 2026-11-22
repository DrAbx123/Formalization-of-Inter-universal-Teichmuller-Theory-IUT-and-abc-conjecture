import tmp.sheaf.xif.paper.S2322NatIsoDirectActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2322NatIsoDirectActual
open LeanFormal.IUT.XiFPaper.S2285RMapNatActual
open LeanFormal.IUT.XiFPaper.S2278QHomNaturalityActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2326SubtypePresheafActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))

-- The naive pointwise subtype presheaf
--   T |-> {g // g • P_T = Q_T}
-- with restriction g |-> g is not well-defined from S2278PT_natural/QT_natural:
-- for p : T1 → T2 in (Over S)^op, the available relations are
--   p.unop.left ≫ P_T1 = P_T2
--   p.unop.left ≫ Q_T1 = Q_T2.
-- From the condition at T2, one gets
--   p.unop.left ≫ (g • P_T1) = p.unop.left ≫ Q_T1,
-- and cancelling p.unop.left is not possible (slice projections are not mono).
-- From the condition at T1 one gets the condition at T2, i.e. the naive map is
-- covariant, not a presheaf map.  Hence this route needs either a different
-- restriction (not g |-> g), or an extra mono/epi hypothesis on p.unop.left.
#check S2278PT_natural
#check S2278QT_natural
#check S2322Comp
#check S2271QHomObj_eq_subtype

end LeanFormal.IUT.XiFPaper.S2326SubtypePresheafActual

end
