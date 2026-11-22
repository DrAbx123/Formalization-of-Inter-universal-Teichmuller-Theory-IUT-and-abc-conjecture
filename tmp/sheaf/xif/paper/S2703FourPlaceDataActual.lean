import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2698Two2161ResidueActual
import tmp.sheaf.xif.paper.S2699TwoFivePlacesActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2697Two2161PlacesActual
open LeanFormal.IUT.XiFPaper.S2698Two2161ResidueActual
open LeanFormal.IUT.XiFPaper.S2699TwoFivePlacesActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2703FourPlaceDataActual

noncomputable def S2703FourPlaceData : S2696FourPlaceData where
  p5a := S2699GaussianPlaceFivePlus
  p5b := S2699GaussianPlaceFiveMinus
  p2161a := S2697GaussianPlacePlus
  p2161b := S2697GaussianPlaceMinus
  odd5a := S2699OddPlus
  odd5b := S2699OddMinus
  odd2161a := S2698OddPlus
  odd2161b := S2698OddMinus

#check S2703FourPlaceData
#print axioms S2703FourPlaceData

end LeanFormal.IUT.XiFPaper.S2703FourPlaceDataActual
end
