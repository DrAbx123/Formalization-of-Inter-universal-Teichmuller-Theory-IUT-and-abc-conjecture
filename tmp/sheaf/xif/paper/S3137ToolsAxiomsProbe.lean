import tmp.sheaf.xif.paper.S3137LogVolumeMapToolActual
import tmp.sheaf.xif.paper.S3137PadicNormToolActual
import tmp.sheaf.xif.paper.S3137ThetaPacketLogVolumeToolActual
import tmp.sheaf.xif.paper.S3137ToolInventoryIndexActual

/-! Axiom probe: manufactured generic tools + external/repo tool inventory (data). -/
open LeanFormal.IUT.XiFPaper.LogVolumeMapToolActual
open LeanFormal.IUT.XiFPaper.PadicNormToolActual
open LeanFormal.IUT.XiFPaper.ThetaPacketLogVolumeToolActual
open LeanFormal.IUT.Audit

#print axioms haarLogVolume_map_of_preimage_eq
#print axioms haarLogVolume_map_image_of_injective
#print axioms haarLogVolume_map_const_smul_image
#print axioms padic_norm_prime
#print axioms padic_norm_prime_zpow
#print axioms exists_padic_norm_prime_inv
#print axioms padic_norm_five
#print axioms finiteThetaPacket_logVolume_eq_weight_mul_log
#print axioms finiteThetaPacket_logVolume_nonpos_of_q_le_one
#print axioms finiteThetaPacket_logVolume_neg_of_q_lt_one
#print axioms S3137ToolInventoryIndex
#check S3137ToolInventoryIndex_length
