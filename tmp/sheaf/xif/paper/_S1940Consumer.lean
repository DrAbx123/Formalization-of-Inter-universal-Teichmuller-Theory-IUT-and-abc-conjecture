import tmp.sheaf.xif.paper.S1940PaperLStarDeterminantActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S1940ConsumerProbe

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual
open LeanFormal.IUT.XiFPaper.S1940PaperLStarDeterminantActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

#check s1940PaperLStarDeterminant T
#check s1940_s1904_bridge T
#check s1940PaperLStarDeterminant_processionNormalized T
#check s1940_average_eq_radii T
#check s1940_average_ne_s1930PaperLStarAverage T

#print axioms s1940_s1904_bridge
#print axioms s1940PaperLStarDeterminant
#print axioms s1940PaperLStarDeterminant_processionNormalized

end LeanFormal.IUT.XiFPaper.S1940ConsumerProbe
