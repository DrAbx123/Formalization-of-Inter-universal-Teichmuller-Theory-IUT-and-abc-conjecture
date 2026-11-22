import tmp.sheaf.xif.paper.Mzk1StrictMeasurePositiveMeasureActual

/-! # Consumer: positive-measure xi-e data -> Cor 3.12 -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StrictMeasurePositiveMeasureConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1StrictMeasurePositiveMeasureActual

variable {α : Type*} {vol : Set α → Real}

/-- The positive-measure instantiation gives `Cor312Conclusion` through the
green StepXI requirement consumer. -/
theorem cor312Conclusion_of_volumeData (D : XiEVolumeData (vol := vol))
    (hqneg : requirementSignedQ (requirementOfVolumeData D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (requirementOfVolumeData D) hqneg
        ipl hipl she hshe apt hapt) :=
  requirement_cor312 (requirementOfVolumeData D) hqneg ipl hipl she hshe apt hapt

end LeanFormal.IUT.XiFPaper.Mzk1StrictMeasurePositiveMeasureConsumerActual
