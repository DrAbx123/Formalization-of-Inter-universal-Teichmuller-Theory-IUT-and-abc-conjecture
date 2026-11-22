import tmp.sheaf.xif.paper.S1764ActualFiberFunctorActual

noncomputable section
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1795Probe1

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1764ActualFiberFunctorActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual

#check @CostructuredArrow.map₂_obj
#print CostructuredArrow.map₂_obj
#check @Comma.ext
#check @Comma.mk
#check @CategoryTheory.Comma.ext
#check @CostructuredArrow.mk
#check @Comma.eqToHom_left
#check @CommaMorphism.ext

end LeanFormal.IUT.XiFPaper.S1795Probe1
