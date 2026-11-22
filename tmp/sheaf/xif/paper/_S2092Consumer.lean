import tmp.sheaf.xif.paper.S2092PaperOtriActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2092PaperOtriActual
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual

namespace S2092Consumer

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (N8Closure.nativePlaceSelection T))

#check paperOtri
#check paperQV
#check paperOUnitsMu
#check paperRootRatio_mem_mu
#check paperOtriRootMissing
#check paperOtriRootMissing_iff
#check paperOtriAttachment
#check no_completionMonoidEval_of_Fside_qVFamily

example : (paperQV T b : paperKv T b) = completionMapSection T b (shadowQ T b).q :=
  paperQV_eq_completionMap T b

example : paperOtriRootMissing T b ↔ paperOtriRootInCompletion T b :=
  paperOtriRootMissing_iff T b

end S2092Consumer
