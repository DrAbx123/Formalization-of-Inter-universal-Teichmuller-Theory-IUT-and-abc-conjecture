import tmp.sheaf.n8.closure.PaperNormalizedValueBridge
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual

noncomputable section
set_option maxHeartbeats 4000000
variable {l : PrimeGeFive} (S : SourceInitialThetaData l)
#check (LeanFormal.IUT.N8Closure.C7QPilotRegionActual.e S).toContinuousLinearEquiv
#check (LeanFormal.IUT.N8Closure.C7QPilotRegionActual.e S).symm.toContinuousLinearEquiv
