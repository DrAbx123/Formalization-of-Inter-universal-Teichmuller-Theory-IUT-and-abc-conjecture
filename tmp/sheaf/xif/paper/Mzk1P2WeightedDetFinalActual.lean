import tmp.sheaf.xif.paper.Mzk1P2DetWeightedNonnegActual
/-! P2 weighted det final status -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P2WeightedDetFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
def weightedDetFinalRows : List String :=
  [ "weightedDetLog_nonpos", "p2WeightedDetLog_nonpos", "p2R13Exact = -p2WeightedDetLog" ]
theorem weightedDetFinalRows_length : weightedDetFinalRows.length = 3 := rfl

/-- Actual weighted determinant nonpositivity, re-exported. -/
theorem weightedDetFinal_nonpos {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    Mzk1P2DetWeightedNonnegActual.p2WeightedDetLog T <= 0 :=
  Mzk1P2DetWeightedNonnegActual.p2WeightedDetLog_nonpos T
end LeanFormal.IUT.XiFPaper.Mzk1P2WeightedDetFinalActual
end
