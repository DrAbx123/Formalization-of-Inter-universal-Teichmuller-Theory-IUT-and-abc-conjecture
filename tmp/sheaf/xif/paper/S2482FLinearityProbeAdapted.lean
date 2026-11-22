import tmp.sheaf.xif.paper.S2482SpecPhiActual
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2482FLinearityProbeAdapted
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482SpecPhiActual
open LeanFormal.IUT.XiFPaper.S2482UnderlyingSquareActual
open CategoryTheory AlgebraicGeometry
theorem S2482Phi_commutes (η : S2482Orbicurve.Hom S2482Orbicurve) :
    (S2482Phi η).comp (algebraMap F S2482CoordinateRing) =
      algebraMap F S2482CoordinateRing := by
  have h := Over.w (S2482Underlying η)
  rw [← S2482UnderlyingLeft_eq] at h
  rw [← S2482Phi_spec] at h
  change Spec.map (CommRingCat.ofHom (S2482Phi η)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F S2482CoordinateRing)) =
      Spec.map (CommRingCat.ofHom (algebraMap F S2482CoordinateRing)) at h
  rw [← Spec.map_comp, Spec.map_inj] at h
  have h' : ((CommRingCat.ofHom (algebraMap F S2482CoordinateRing)) ≫
      (CommRingCat.ofHom (S2482Phi η))).hom =
      (CommRingCat.ofHom (algebraMap F S2482CoordinateRing)).hom := by
    exact congrArg (fun f => f.hom) h
  simpa [CommRingCat.ofHom_comp, CommRingCat.hom_ofHom,
    CommRingCat.hom_comp] using h'
#check S2482Phi_commutes
#print axioms S2482Phi_commutes
end LeanFormal.IUT.XiFPaper.S2482FLinearityProbeAdapted
end