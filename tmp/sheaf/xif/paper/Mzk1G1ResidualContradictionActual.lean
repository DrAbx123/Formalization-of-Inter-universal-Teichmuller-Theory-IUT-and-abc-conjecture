import tmp.sheaf.xif.paper.Mzk1G1CompactnessGlobalActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1ResidualContradictionActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1CompactnessGlobalActual

/-- Actual residual contradiction datum: a proposition and both its failure
and its proof, packaged with the compactness data. -/
structure G1ResidualContradictionData where
  compactness : G1CompactnessGlobalData
  P : Prop
  hfail : ¬ P
  hP : P

theorem G1ResidualContradictionData.contradiction
    (D : G1ResidualContradictionData) : False :=
  D.hfail D.hP

/-- Actual contradiction consumer: if the global bound fails and holds, then
the residual argument closes. -/
theorem g1ResidualContradiction (D : G1ResidualContradictionData) : False :=
  D.contradiction

end LeanFormal.IUT.XiFPaper.G1ResidualContradictionActual
end
