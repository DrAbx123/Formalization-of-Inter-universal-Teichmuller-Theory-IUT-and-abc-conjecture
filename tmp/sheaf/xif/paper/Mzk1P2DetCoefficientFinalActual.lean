import tmp.sheaf.xif.paper.Mzk1P2DetCoefficientActual
/-! P2 det coefficient final status -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P2DetCoefficientFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
def detCoeffFinalRows : List String :=
  [ "detCoefficientNorm = product local norms", "norm_prod_le_one", "log_norm_prod_eq_sum" ]
theorem detCoeffFinalRows_length : detCoeffFinalRows.length = 3 := rfl

/-- Actual det coefficient bound, re-exported. -/
theorem detCoeffFinal_le_one {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    Mzk1P2DetCoefficientActual.detCoefficientNorm T
        (Mzk1P2DetCoefficientActual.p2PureTensorCoefficient T) <= 1 :=
  Mzk1P2DetCoefficientActual.p2DetCoefficientNorm_le_one T
end LeanFormal.IUT.XiFPaper.Mzk1P2DetCoefficientFinalActual
end
