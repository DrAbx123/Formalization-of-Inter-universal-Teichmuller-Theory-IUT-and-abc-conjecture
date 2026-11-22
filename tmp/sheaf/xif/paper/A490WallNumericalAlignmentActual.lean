/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.lana.iut.Iut.Wall.Checks

/-! # A490 NumericalWall squad: Wall ⇒ NumericalWall ⇒ variant -/

namespace Iut

namespace Wall

variable (D : InitialThetaData.{0})

/-- The eta-algorithm wall gives the numerical wall: its output region is adelic, sits in
the hull of the theta-pilot image, and has log-volume `qPilot.lhs` (hence pointed map `etaQ`). -/
theorem numericalWall_of_wall (A : EtaAlg D) (hW : Wall D A) : NumericalWall D := by
  obtain ⟨U, hAd, hHull, hVol⟩ := A.exists_out_of_wall hW
  refine ⟨U, hAd, hHull, ?_⟩
  rw [hVol]
  unfold etaQ

/-- Consequently the wall implies the Corollary 3.12 variant (through the shadow lemma). -/
theorem corollary312Variant_of_wall (A : EtaAlg D) (hW : Wall D A) :
    Corollary312Variant (concreteVariantData D) :=
  (numericalWall_iff D).mp (numericalWall_of_wall D A hW)

end Wall

end Iut
