import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardAMPLThetaBoundSupply
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CertificateCThetaTransfer
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CertificateComparisonBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeometryGapCards
noncomputable section
open LeanFormal.IUT
namespace LeanFormal.IUT.XiFPaper.S2954ThetaBridgeInventory

/-- Concrete fields of the StepXI finite certificate. -/
def S2954CertificateFields : List String :=
  [ "hull : FiniteHull label"
  , "hull.volume : label → Real"
  , "hull.hullVolume : Real"
  , "hull.contains : ∀ i, volume i ≤ hullVolume"
  , "weighted : WeightedValues label"
  , "weighted_matches_hull : ∀ i, weighted.value i = hull.volume i"
  , "weights_nonnegative : ∀ i, 0 ≤ weighted.weight i"
  , "qSigned : Real"
  , "thetaSigned : Real"
  , "q_le_hull : qSigned ≤ hull.hullVolume"
  , "hull_le_theta : hull.hullVolume ≤ thetaSigned"
  , "q_negative : qSigned < 0"
  ]

/-- Concrete fields of the Card-AMPL theta supply. -/
def S2954CardAMPLFields : List String :=
  [ "theta : Real"
  , "theta_nonneg : 0 ≤ theta"
  , "hull_logVolume_le : W.logVolume W.hull ≤ ENNReal.ofReal theta"
  , "certificate_thetaSigned : certificate.thetaSigned = theta"
  , "realVolume_le : iqHullRealVolume W ≤ theta"
  ]

/-- Exact remaining gaps for a source-level thetaSigned/hull certificate. -/
def S2954ThetaBridgeGaps : List String :=
  [ "IQ carrier topology/O-module structure：CardHullRealGeometryGapCards gap card"
  , "literal IQ(S; n, D) carrier 不存在（只有 Q_p/normed-space 模型层）"
  , "缺少从 SourceHull/原 source 构造 StepXIFiniteCertificate 的 glue"
  , "缺少 thetaSigned 与 source signed hull log-volume 的 identification"
  , "CardAMPLThetaBoundSupply 是 supplied interface，不是从 source 导出"
  , "CardHullRealSignedLogVolume 只给 sigma=0/signed-hull 特例证书"
  , "无 hull 测度/IQ 归一化与 thetaSigned 的最终比较定理"
  ]

#check S2954CertificateFields
#check S2954CardAMPLFields
#check S2954ThetaBridgeGaps
#check LeanFormal.IUT.StepXIFiniteCertificate
#check LeanFormal.IUT.StepXIFiniteCertificate.q_le_theta
#check LeanFormal.IUT.CardAMPLThetaBoundSupply
#check LeanFormal.IUT.CardAMPLThetaBoundSupply.certificate_thetaSigned

end LeanFormal.IUT.XiFPaper.S2954ThetaBridgeInventory