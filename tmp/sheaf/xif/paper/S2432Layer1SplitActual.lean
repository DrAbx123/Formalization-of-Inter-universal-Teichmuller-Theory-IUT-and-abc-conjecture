import tmp.sheaf.xif.paper.S2195Layer1InstanceActual
import tmp.sheaf.xif.paper.S2040QVPlaceSplitActual
import tmp.sheaf.xif.paper.S2232Layer1PrimeAlignmentActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2432Layer1SplitActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1712OddResidueActual
open LeanFormal.IUT.XiFPaper.S1717PlaceSevenD5Actual
open LeanFormal.IUT.XiFPaper.S1729FullBadPlaceActual
open LeanFormal.IUT.XiFPaper.S1730BadSetWithoutLActual
open LeanFormal.IUT.XiFPaper.S1729FullBadPlaceActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.S2040QVPlaceSplitActual
open LeanFormal.IUT.XiFPaper.S2195Layer1InstanceActual
open LeanFormal.IUT.XiFPaper.S2232Layer1PrimeAlignmentActual

universe u

variable {l : PrimeGeFive}
  (T : LeanFormal.IUT.InitialThetaSource.SourceNativeInitialThetaData.{0} l)
  (b : Bad (nativePlaceSelection T))

theorem S2432Layer1Split_of_paperConditions
    (h : S2232PaperArithmeticConditions T b) :
    S2040QVPlaceSplitPackage T b := by
  obtain ⟨P⟩ := s2232_package_of_paperArithmeticConditions (T := T) (b := b) h
  exact s2135_toPackage (T := T) (b := b) P
#print axioms S2432Layer1Split_of_paperConditions

end LeanFormal.IUT.XiFPaper.S2432Layer1SplitActual
end