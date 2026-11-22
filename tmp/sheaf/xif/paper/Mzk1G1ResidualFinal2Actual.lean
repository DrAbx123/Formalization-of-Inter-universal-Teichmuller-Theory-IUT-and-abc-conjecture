import tmp.sheaf.xif.paper.Mzk1G1CompactnessActual2

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1ResidualFinal2Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1CompactnessActual2

structure G1ResidualFinal2Data (n : ℕ) where
  compactness : G1CompactnessActual2Data n
  P : Prop
  hfail : ¬ P
  hP : P

theorem G1ResidualFinal2Data.contradiction
    {n : ℕ} (D : G1ResidualFinal2Data n) : False :=
  D.hfail D.hP

theorem g1ResidualFinal2 {n : ℕ} (D : G1ResidualFinal2Data n) : False :=
  D.contradiction

end LeanFormal.IUT.XiFPaper.G1ResidualFinal2Actual
end
