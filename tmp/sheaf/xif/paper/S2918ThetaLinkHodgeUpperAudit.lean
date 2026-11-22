import tmp.sheaf.xif.paper.S2917ThetaUpperObjectInventory
import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import LeanFormal.IUT.IUTI.HodgeTheater.LinkVolumeTransport
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardAMPLThetaBoundSupply
import LeanFormal.IUTDispute
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2917ThetaUpperObjectInventory
namespace LeanFormal.IUT.XiFPaper.S2918ThetaLinkHodgeUpperAudit

/-- Inventory entries for theta-link / Hodge-theater upper-bound objects. -/
def S2918ThetaLinkHodgeUpperInventory : List String :=
  [ "HodgeTheater.thetaPacket : q, scale, logVolume（只有 theta packet，无 J height 上界）"
  , "HodgeTheaterLink : theta_q_eq, theta_scale_eq（theta-link 等式，无上界）"
  , "LinkVolumeTransport.log_volume_eq（log volume 等式）"
  , "CardAMPLThetaBoundSupply : theta 上界（supplied interface，不是 theta-link/Hodge-theater 对象）"
  , "IUTDispute.ReceiverBound.cTheta/hull_upper_bound（抽象 order-theoretic audit，不是 IUT theta link）"
  , "S2714_sourceSignedHull_upper_zero（local signed hull 上界 0）"
  , "S2780HeightGap / S2838ThetaUpperGap（point/J height 上界目标，未证）"
  ]

#check LeanFormal.IUT.HodgeTheater
#check LeanFormal.IUT.HodgeTheaterLink
#check LeanFormal.IUT.HodgeTheaterLink.theta_q_eq
#check LeanFormal.IUT.HodgeTheaterLink.theta_scale_eq
#check LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardAMPLThetaBoundSupply
#check LeanFormal.IUTDispute.ReceiverBound
#check LeanFormal.IUTDispute.ReceiverBound.cTheta
#check LeanFormal.IUTDispute.ReceiverBound.hull_upper_bound
#check S2780HeightGap
#check S2838ThetaUpperGap
#check S2714_sourceSignedHull_upper_zero
#check S2714_cThetaLowerBound_of_upper

#check S2918ThetaLinkHodgeUpperInventory

end LeanFormal.IUT.XiFPaper.S2918ThetaLinkHodgeUpperAudit