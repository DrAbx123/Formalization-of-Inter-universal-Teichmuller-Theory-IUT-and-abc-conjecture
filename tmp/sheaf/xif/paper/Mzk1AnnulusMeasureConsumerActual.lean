import tmp.sheaf.xif.paper.Mzk1AnnulusMeasureActual

/-! # Consumer: annulus measure data -> Cor 3.12 -/

namespace LeanFormal.IUT.XiFPaper.Mzk1AnnulusMeasureConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1AnnulusMeasureActual

variable {α : Type*} {vol : Set α → Real}

/-- Annulus measure data (positive hull annulus) yields `Cor312Conclusion`. -/
theorem cor312Conclusion_of_annulus (D : XiEAnnulusData (vol := vol))
    (hadd : forall s t : Set α, Disjoint s t -> vol (s ∪ t) = vol s + vol t)
    (hqneg : requirementSignedQ (requirementOfAnnulus D hadd) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (requirementOfAnnulus D hadd) hqneg
        ipl hipl she hshe apt hapt) :=
  requirement_cor312 (requirementOfAnnulus D hadd) hqneg ipl hipl she hshe apt hapt

/-- The annulus instantiation has strict signed inequality. -/
theorem annulus_strict_signed (D : XiEAnnulusData (vol := vol))
    (hadd : forall s t : Set α, Disjoint s t -> vol (s ∪ t) = vol s + vol t) :
    requirementSignedQ (requirementOfAnnulus D hadd) <
      requirementSignedTheta (requirementOfAnnulus D hadd) :=
  requirementOfAnnulus_strict D hadd

end LeanFormal.IUT.XiFPaper.Mzk1AnnulusMeasureConsumerActual
