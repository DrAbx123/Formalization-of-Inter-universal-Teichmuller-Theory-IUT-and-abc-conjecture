import tmp.sheaf.n8.closure.PaperNormalizedValueBridge
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open MeasureTheory
variable {l : PrimeGeFive} (S : SourceInitialThetaData l)
example : (LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu.Regular := by infer_instance
example : NeZero (LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu := by infer_instance
