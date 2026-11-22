import LeanFormal.IUT.IUTIV.Estimates.Section2
import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import LeanFormal.IUT.IUTIV.Estimates.DifferentDegreeUpperBound
noncomputable section
open LeanFormal.IUT
namespace LeanFormal.IUT.XiFPaper.S2950IUTIVUpperAudit

/-- Constructible actual objects in IUT IV Estimates relevant to thetaSigned upper bounds. -/
def S2950ConstructibleObjects : List String :=
  [ "Section2: iutIVProp21i_log_le_self（log x ≤ x）"
  , "Section2: iutIVProp21ii_theta_two_sided_eventually（θ 双侧显式界）"
  , "Section2: iutIVProp21ii_exists_prime_notMem_le_two_mul"
  , "StepVProcessionAverage: collectionBound / sum_collectionBound"
  , "StepVProcessionAverage: processionAverage_eq / processionAverage_le"
  , "DifferentDegreeUpperBound: not_map_dvd_differentIdeal_of_degree_not_mem"
  , "DifferentDegreeUpperBound: DVR factorCount/degree 局部估计"
  ]

/-- Exact gaps for a thetaSigned upper estimate. -/
def S2950ThetaSignedUpperGaps : List String :=
  [ "IUTIV/Estimates 中没有 thetaSigned 定义或 log-volume 载体"
  , "Section2 Cor 2.2/2.3 仍是 machine-gap 卡片，无形式化"
  , "StepVProcessionAverage 只给 D/Q/S/T 的实数平均不等式，无 theta/J height 语义"
  , "DifferentDegreeUpperBound 只给 different/DVR 的代数上界，无 thetaSigned 比较"
  , "缺少 thetaSigned ≤ collectionBound/procession 的解析桥"
  , "缺少 S2935 heightLeProcession 与 IUTIV Estimates 的接口"
  ]

#check S2950ConstructibleObjects
#check S2950ThetaSignedUpperGaps
#check LeanFormal.IUT.IUTIV.Estimates.iutIVProp21i_log_le_self
#check LeanFormal.IUT.IUTIV.Estimates.iutIVProp21ii_theta_two_sided_eventually
#check LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
#check LeanFormal.IUT.IUTIV.StepVProcessionAverage.processionAverage_le
#check LeanFormal.IUT.IUTIV.Estimates.not_map_dvd_differentIdeal_of_degree_not_mem

end LeanFormal.IUT.XiFPaper.S2950IUTIVUpperAudit