import tmp.sheaf.xif.paper.Mzk1G1CompactnessActual2

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1ResidualContradictionFinal2Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1CompactnessActual2

structure G1ResidualContradictionFinal2Data (n : ℕ) where
  compactness : G1CompactnessActual2Data n
  P : Prop
  hfail : ¬ P
  hP : P

theorem G1ResidualContradictionFinal2Data.contradiction
    {n : ℕ} (D : G1ResidualContradictionFinal2Data n) : False :=
  D.hfail D.hP

theorem g1ResidualContradictionFinal2 {n : ℕ}
    (D : G1ResidualContradictionFinal2Data n) : False :=
  D.contradiction

end LeanFormal.IUT.XiFPaper.G1ResidualContradictionFinal2Actual
end
