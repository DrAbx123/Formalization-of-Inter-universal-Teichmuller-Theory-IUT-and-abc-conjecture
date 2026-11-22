import tmp.sheaf.xif.paper.Mzk1P2RankOneChainActual
/-! P2 rank-one no-det complete status -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P2NoDetRankOneActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P2RankOneChainActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S720OneFactorTensorNormReductionActual
open LeanFormal.IUT.XiFPaper.S757QVFamBlockIsometryActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
open LeanFormal.IUT.XiFPaper.Mzk1P2ArchLogSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1P2R12WeightBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P2TensorDetFactorActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
def noDetRankOneRows : List String :=
  [ "rank-one block isometry reduces to QVFamBlockNormPreserving",
    "no det factor in rank one", "rankOneComparisonCandidate" ]
theorem noDetRankOneRows_length : noDetRankOneRows.length = 3 := rfl

/-- Conditional rank-one isometry (no det factor). -/
theorem noDetRankOne_isometry {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    (hpres : QVFamBlockNormPreserving (l := l) T b) :
    qVFamTensorBlock T b ≃ₗᵢ[ℚ_[qVFamTensorP T b]] rootBase T b :=
  p2RankOneBlockIsometry T b hpres
end LeanFormal.IUT.XiFPaper.Mzk1P2NoDetRankOneActual
end
