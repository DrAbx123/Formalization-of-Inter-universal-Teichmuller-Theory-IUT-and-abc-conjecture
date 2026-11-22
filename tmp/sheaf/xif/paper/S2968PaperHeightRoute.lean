import LeanFormal.IUT.ABCBridge.Bridge.ThetaBoundToHeightWeight
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantHeight
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardAMPLThetaBoundSupply
import tmp.sheaf.xif.paper.S2922ThetaLinkUpperAssemblyActual
import tmp.sheaf.xif.paper.S2838HeightComparisonReductionActual
noncomputable section
open LeanFormal.IUT
namespace LeanFormal.IUT.XiFPaper.S2968PaperHeightRoute

/-- Paper theta-link height route: exact reusable lemmas from theta-hull to
J/point height. -/
def S2968ThetaHullToHeightLemmas : List String :=
  [ "ThetaBoundToHeightWeight.heightWeightBound_of_normalizedVolumeComparison："
  , "  height ≤ (1+δ) volumeδ 且 volumeδ ≤ (1+δ) weight + thetaBound + Dδ"
  , "  ⇒ height ≤ (1+ε) weight + A（factor absorption）"
  , "exists_oneAdd_sq_le_oneAdd：δ = min 1 (ε/3) 吸收 (1+δ)^2"
  , "CardAMPLThetaBoundSupply.realVolume_le：iqHullRealVolume W ≤ theta"
  , "CardAMPLThetaBoundSupply.certificate_thetaSigned：certificate.thetaSigned = theta"
  , "S2922_to_S2838ThetaUpperGap：theta upper certificate ⇒ S2838ThetaUpperGap"
  , "S2838_height_le_Jlog：abcRationalPoint height ≤ abcJInvariant logHeight（point→J）"
  , "abcJInvariant_logHeight_bounds_abcRationalPoint：J/point 高度双向界"
  ]

/-- Exact missing steps from theta-hull to J/point height. -/
def S2968ThetaHullToHeightGaps : List String :=
  [ "缺 theta-hull 到 volumeδ 的解析比较（paper Step XI 的 θ-pilot log-volume）"
  , "缺 volumeδ 到 arithmeticWeight 的比较（thetaBound + Dδ 的显式来源）"
  , "缺 thetaSigned（hull certificate）到 volumeδ 的识别"
  , "CardAMPLThetaBoundSupply 是 supplied interface，不是从 theta-hull 导出"
  , "S2922 的 qPilot/procession 数据仍是显式输入；无 theta-link 自动导出"
  , "无统一的 theta-hull → J-height 直接引理"
  ]

#check S2968ThetaHullToHeightLemmas
#check S2968ThetaHullToHeightGaps
#check LeanFormal.IUT.heightWeightBound_of_normalizedVolumeComparison
#check LeanFormal.IUT.exists_oneAdd_sq_le_oneAdd
#check LeanFormal.IUT.CardAMPLThetaBoundSupply.realVolume_le
#check LeanFormal.IUT.CardAMPLThetaBoundSupply.certificate_thetaSigned
#check LeanFormal.IUT.XiFPaper.S2922ThetaLinkUpperAssembly.S2922_to_S2838ThetaUpperGap
#check LeanFormal.IUT.XiFPaper.S2838HeightComparisonReductionActual.S2838_height_le_Jlog
#check LeanFormal.IUT.abcJInvariant_logHeight_bounds_abcRationalPoint

end LeanFormal.IUT.XiFPaper.S2968PaperHeightRoute