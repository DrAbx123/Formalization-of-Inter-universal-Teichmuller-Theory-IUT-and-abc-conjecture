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
variable {W : EtaleStackPseudofunctor S1726K}

theorem whiskerRight_ident_aux (l : Pseudofunctor.StrongTrans W P)
    (F : Pseudofunctor.StrongTrans P X)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.whiskerRight (𝟙 l) F).as.app U
      = 𝟙 (l.app U ≫ F.app U) := by
  have hid : (𝟙 l : Pseudofunctor.StrongTrans.Hom l l)
      = ⟨Pseudofunctor.StrongTrans.Modification.id l⟩ := rfl
  rw [hid]
  change (((⟨Pseudofunctor.StrongTrans.Modification.id l⟩ :
    Pseudofunctor.StrongTrans.Hom l l).as.app U) ▷ (F.app U))
      = 𝟙 (l.app U ≫ F.app U)
  rw [show ((⟨Pseudofunctor.StrongTrans.Modification.id l⟩ :
    Pseudofunctor.StrongTrans.Hom l l).as.app U) = 𝟙 (l.app U) from rfl]
  rw [id_whiskerRight]

end Probe
