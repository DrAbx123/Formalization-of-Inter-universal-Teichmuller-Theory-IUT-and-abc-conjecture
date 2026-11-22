import tmp.sheaf.n8.closure.PaperKfQOScalingGeneral
import tmp.sheaf.n8.closure.PaperKfHaarNormClosed

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

theorem paperKfQORegionScaling_actual :
    ∀ q : (LeanFormal.IUT.N8Closure.PaperKfQOScalingGeneral.PaperKf S)ˣ,
      LeanFormal.IUT.N8Closure.PaperKfQOScalingGeneral.PaperKfQORegionScaling S q :=
  LeanFormal.IUT.N8Closure.PaperKfQOScalingGeneral.paperKfQORegionScaling_of_haarNorm S
    (LeanFormal.IUT.N8Closure.PaperKfHaarNormClosed.paperKf_haarNormIdentificationTarget S)

end
