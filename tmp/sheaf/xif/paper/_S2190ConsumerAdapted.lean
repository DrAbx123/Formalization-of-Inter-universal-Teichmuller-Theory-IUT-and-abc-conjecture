import tmp.sheaf.xif.paper.S2190RootSourceConditionsActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S2190RootSourceConditionsActual
open LeanFormal.IUT.XiFPaper.S2129RootNecessaryActual

namespace LeanFormal.IUT.XiFPaper.S2190Consumer

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

#check S2190QSquareSource
#check S2190QLthPowerSource
#check S2190KernelFieldToQLthPowerBridge
#check rootNecessary_of_source_bridges
#check rootNecessary_of_halfRootSource
#check twoLDivOrder_of_halfRootSource
#check s2032_q5_square_iff

theorem consumer_test
    (h2 : S2190TwoTorsionToQSqrtBridge T b)
    (hl : S2190KernelFieldToQLthPowerBridge T b) :
    S2129RootNecessary T b :=
  rootNecessary_of_source_bridges T b h2 hl

#print axioms consumer_test

end LeanFormal.IUT.XiFPaper.S2190Consumer
end
