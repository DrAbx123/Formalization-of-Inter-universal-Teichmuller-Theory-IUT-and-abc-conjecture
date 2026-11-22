import tmp.sheaf.xif.paper.S1982D5FiveActual
import tmp.sheaf.xif.paper.S1467FunctionFieldPullbackActual

noncomputable section
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual

namespace Probe2056

#check (inferInstance : Field S1906K)
#check (inferInstance : AddCommGroup (WeierstrassCurve.Affine.Point S1906W))
#check (inferInstance : Field (AlgebraicClosure S1720Field))

abbrev K : Type := S1906K
abbrev W : WeierstrassCurve.Affine K := S1906W

#check (inferInstance : Field K)
#check (inferInstance : AddCommGroup W.Point)

end Probe2056
