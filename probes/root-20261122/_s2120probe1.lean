import tmp.sheaf.xif.paper.S2118PastedComparisonTwistActual
import tmp.sheaf.xif.paper.S1827CloseRetractionActual
import tmp.sheaf.xif.paper.S1801LiftEssSurjActual

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
open LeanFormal.IUT.XiFPaper.S1801LiftEssSurjActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S2107RightCancelActual
open LeanFormal.IUT.XiFPaper.S2118PastedComparisonTwistActual

universe u

variable {P X Y Z : EtaleStackPseudofunctor S1726K}
variable (sq : EtalePseudofunctorSquare P X Y Z)
variable {W : EtaleStackPseudofunctor S1726K}
variable (f : Pseudofunctor.StrongTrans W P)

#check @S1801TwoCellSurjTo
#check @S2107ConeComparisonFull
#check @S2107ImageCone
#check @S1827SubsingletonModRep
#check @Bicategory.whisker_exchange
#check @Bicategory.id_whiskerRight
#check @Bicategory.whisker_assoc
#check @Bicategory.comp_whiskerRight

example : Pseudofunctor.StrongTrans.whiskerRight (𝟙 f) sq.toX = 𝟙 (Pseudofunctor.StrongTrans.vcomp f sq.toX) := by
  rfl

example : Pseudofunctor.StrongTrans.whiskerRight (𝟙 f) sq.toX = 𝟙 (Pseudofunctor.StrongTrans.vcomp f sq.toX) := by
  simp

-- subsingleton instance check
example (a b : Pseudofunctor.StrongTrans W (schemeRepresentableEtalePseudofunctor S1726K S1726AffineOver)) : Subsingleton (a ⟶ b) := inferInstance

end Probe
