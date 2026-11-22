/- P6 actual hCor312 source from P5: exposes the accepted P5 local volume
inequality as the actual display input component, alongside the final display. -/
import tmp.sheaf.xif.paper.Node09P5HullInequalityFinalActual
import tmp.sheaf.xif.paper.Mzk1P6Thm110DisplayActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6HCor312ActualFromP5Actual
noncomputable def p5_local_volume_inequality := @LeanFormal.IUT.XiFPaper.Node09P5HullInequalityFinalActual.qVFamNormalizedQPilotVolume_le_thetaHullVolume
noncomputable def p6_display_from_p5 := @LeanFormal.IUT.XiFPaper.Mzk1P6Thm110DisplayActual.p6_thm110_display
#print axioms p5_local_volume_inequality
#print axioms p6_display_from_p5
end LeanFormal.IUT.XiFPaper.Mzk1P6HCor312ActualFromP5Actual
end