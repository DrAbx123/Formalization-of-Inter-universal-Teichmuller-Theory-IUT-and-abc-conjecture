import tmp.sheaf.xif.paper.S2605LiftSLActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2607HmapActual
open LeanFormal.IUT.XiFPaper.S2605LiftSLActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual

lemma hmap : (algebraMap Sb Lb) = liftSL := by
  apply IsLocalization.ringHom_ext (M := Submonoid.powers (Cden : Cb))
  rw [liftSL_comp]
  change ((algebraMap Sb Lb).comp (algebraMap Cb Sb)) = gCL
  ext x
  simp [gCL, IsScalarTower.algebraMap_apply Cb Fb Lb]

end LeanFormal.IUT.XiFPaper.S2607HmapActual
end