import tmp.sheaf.n8.closure.PaperNormalizedValueBridge
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open MeasureTheory
noncomputable section
variable {l : PrimeGeFive} (S : SourceInitialThetaData l)
local instance : MeasurableSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) := (rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) := (rawData (places S) (tuple S)).borelSpace
local instance : LocallyCompactSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) := locallyCompact_of_proper
local instance : (rawData (places S) (tuple S)).mu.IsAddHaarMeasure := (rawData (places S) (tuple S)).addHaar
example : (rawData (places S) (tuple S)).mu.IsOpenPosMeasure := by infer_instance
example : (rawData (places S) (tuple S)).mu.Regular := by infer_instance
