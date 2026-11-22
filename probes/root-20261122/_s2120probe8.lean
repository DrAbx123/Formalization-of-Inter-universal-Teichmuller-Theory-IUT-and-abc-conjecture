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

theorem whiskerRight_id_strong_aux (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.whiskerRight (𝟙 f) sq.toX).as.app U =
      (𝟙 (Pseudofunctor.StrongTrans.vcomp f sq.toX)).as.app U := by
  show ((𝟙 f).as.app U ▷ sq.toX.app U) = 𝟙 ((f.app U) ≫ (sq.toX.app U))
  change (𝟙 (f.app U) ▷ sq.toX.app U) = 𝟙 (f.app U ≫ sq.toX.app U)
  rw [id_whiskerRight]

theorem whiskerRight_id_strong :
    Pseudofunctor.StrongTrans.whiskerRight (𝟙 f) sq.toX =
      𝟙 (Pseudofunctor.StrongTrans.vcomp f sq.toX) := by
  apply Pseudofunctor.StrongTrans.Hom.ext
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext U
  exact whiskerRight_id_strong_aux sq f U

end Probe
