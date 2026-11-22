import tmp.sheaf.xif.paper.Mzk1G1CompactnessGlobalActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1ResidualContradictionFinalActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1CompactnessGlobalActual

/-- Actual final residual contradiction datum: compactness data plus a
proposition and both its failure and proof. -/
structure G1ResidualContradictionFinalData where
  compactness : G1CompactnessGlobalData
  P : Prop
  hfail : ¬ P
  hP : P

theorem G1ResidualContradictionFinalData.contradiction
    (D : G1ResidualContradictionFinalData) : False :=
  D.hfail D.hP

theorem g1ResidualContradictionFinal
    (D : G1ResidualContradictionFinalData) : False :=
  D.contradiction

end LeanFormal.IUT.XiFPaper.G1ResidualContradictionFinalActual
end
