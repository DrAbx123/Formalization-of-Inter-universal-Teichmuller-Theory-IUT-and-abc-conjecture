import tmp.sheaf.n8.closure.PaperNormalizedValueBridge
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open MeasureTheory
variable {l : PrimeGeFive} (S : SourceInitialThetaData l)
local instance : MeasurableSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) := (rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) := (rawData (places S) (tuple S)).borelSpace
example : (rawData (places S) (tuple S)).mu.Regular := by infer_instance
