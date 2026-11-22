import tmp.sheaf.xif.paper.S2482CorrectedHomUniquenessActual
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2482ExtractProbeAdapted
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482SpecPhiActual
open LeanFormal.IUT.XiFPaper.S2482CorrectedHomUniquenessActual
open CategoryTheory AlgebraicGeometry
example (η : S2482Orbicurve.Hom S2482Orbicurve)
    (h2 : Nonempty (Iso (Iut.HyperbolicOrbicurve.Hom.comp η η)
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve)))
    (hid : (S2482PhiAlgEquiv η h2).toAlgHom = AlgHom.id F S2482CoordinateRing) :
    S2482Phi η = RingHom.id S2482CoordinateRing := by
  have h := congrArg AlgHom.toRingHom hid
  change S2482Phi η = RingHom.id S2482CoordinateRing at h
  exact h
end LeanFormal.IUT.XiFPaper.S2482ExtractProbeAdapted
end