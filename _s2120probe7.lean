import tmp.sheaf.xif.paper.S2118PastedComparisonTwistActual

noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace Probe

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2118PastedComparisonTwistActual

universe u

variable {P X Y Z : EtaleStackPseudofunctor S1726K}
variable (sq : EtalePseudofunctorSquare P X Y Z)
variable {W : EtaleStackPseudofunctor S1726K}
variable (f : Pseudofunctor.StrongTrans W P)

#check @Pseudofunctor.StrongTrans.Hom
#check @Pseudofunctor.StrongTrans.Modification
#check (show Pseudofunctor.StrongTrans.Hom f f from 𝟙 f)
#check (show Pseudofunctor.StrongTrans.Hom (Pseudofunctor.StrongTrans.vcomp f sq.toX)
      (Pseudofunctor.StrongTrans.vcomp f sq.toX) from 𝟙 _)
#print Pseudofunctor.StrongTrans.vcomp
#check Pseudofunctor.StrongTrans.comp_app
#check Pseudofunctor.StrongTrans.id

end Probe
