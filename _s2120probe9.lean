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
  have h1 : Pseudofunctor.StrongTrans.Hom f f := 𝟙 f
  have h2 : Pseudofunctor.StrongTrans.Hom (Pseudofunctor.StrongTrans.vcomp f sq.toX)
      (Pseudofunctor.StrongTrans.vcomp f sq.toX) := 𝟙 _
  change (h1.as.app U ▷ sq.toX.app U) = h2.as.app U
  have hh1 : h1.as.app U = 𝟙 (f.app U) := rfl
  have hh2 : h2.as.app U = 𝟙 (f.app U ≫ sq.toX.app U) := rfl
  rw [hh1, hh2, id_whiskerRight]

theorem whiskerRight_id_strong :
    Pseudofunctor.StrongTrans.whiskerRight (𝟙 f) sq.toX =
      𝟙 (Pseudofunctor.StrongTrans.vcomp f sq.toX) := by
  apply Pseudofunctor.StrongTrans.Hom.ext
  apply Pseudofunctor.StrongTrans.Modification.ext
  funext U
  exact whiskerRight_id_strong_aux sq f U

end Probe
