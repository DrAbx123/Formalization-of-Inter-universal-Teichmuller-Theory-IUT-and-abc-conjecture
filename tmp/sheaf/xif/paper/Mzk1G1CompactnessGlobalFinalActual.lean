import tmp.sheaf.xif.paper.Mzk1G1CompactnessGlobalActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1CompactnessGlobalFinalActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1CompactnessGlobalActual

/-- Actual final compactness global data: re-export of the constructed
compactness datum. -/
noncomputable def g1CompactnessGlobalFinal : G1CompactnessGlobalData :=
  g1CompactnessGlobalData

theorem g1CompactnessGlobalFinal_nonempty :
    Nonempty G1CompactnessGlobalData :=
  ⟨g1CompactnessGlobalFinal⟩

end LeanFormal.IUT.XiFPaper.G1CompactnessGlobalFinalActual
end
