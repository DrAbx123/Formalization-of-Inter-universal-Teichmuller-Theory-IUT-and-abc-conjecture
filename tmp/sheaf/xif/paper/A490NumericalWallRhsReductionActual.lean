/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.lana.iut.Iut.Wall.NumericalWallHullActual
import tmp.sheaf.lana.iut.Iut.Wall.Rss

/-! # A490 NumericalWall squad: wall reduces to qPilot.lhs <= rhs -/

namespace Iut

namespace Wall

variable (D : InitialThetaData.{0})

/-- The numerical wall, in archScale-region form, is exactly the comparison
`qPilot.lhs <= rhs`: existence of an admissible region in the hull with log-volume
`qPilot.lhs` is equivalent to that inequality (archimedean rescaling realizes every
`x <= rhs`, while `logVol_le_rhs` bounds every admissible hull region by `rhs`). -/
theorem numericalWall_iff_qPilot_le_rhs :
    NumericalWall D ↔
      (concreteVariantData D).qPilot.lhs ≤ (concreteVariantData D).rhsData.rhs := by
  constructor
  · intro hW
    obtain ⟨U, hU, hI, hvol⟩ :=
      (hullActual_numericalWall_iff_exists_logVol D).mp hW
    rw [← hvol]
    exact logVol_le_rhs D hU hI
  · intro hle
    obtain ⟨U, hU, hI, hvol⟩ :=
      hullActual_exists_adelic_inHullOfImage_logVol D _ hle
    exact (hullActual_numericalWall_iff_exists_logVol D).mpr ⟨U, hU, hI, hvol⟩

/-- The Corollary 3.12 variant is equivalent to the single numerical inequality
`qPilot.lhs <= rhs`. -/
theorem corollary312Variant_iff_qPilot_le_rhs :
    Corollary312Variant (concreteVariantData D) ↔
      (concreteVariantData D).qPilot.lhs ≤ (concreteVariantData D).rhsData.rhs :=
  (numericalWall_iff D).symm.trans (numericalWall_iff_qPilot_le_rhs D)

end Wall

end Iut
