/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shehdd lane (A490 squad — bridge)
-/
import tmp.sheaf.lana.iut.Iut.Wall.NumericalWallHullActual
import tmp.sheaf.lana.iut.Iut.Wall.NumericalWallRssActual

/-!
# NumericalWall ↔ q-pilot inequality (A490 squad bridge)

The A490 NumericalWall files give the field-level wiring:
* `hullActual_numericalWall_iff_exists_logVol` reduces `NumericalWall` to the existence of an
  adelic region in the hull of a single (Ind1)-image with log-volume `qPilot.lhs`;
* `hullActual_exists_adelic_inHullOfImage_logVol` builds such a region from any real number
  `x ≤ rhsData.rhs` (archimedean rescaling of the hull of the distinguished image);
* `numericalWall_of_adelicHull_logVol` turns such a region into `NumericalWall` through the
  proved `numericalWall_iff_rss`.

This file closes the bridge: `NumericalWall D` is *equivalent* to the single real inequality
`qPilot.lhs ≤ rhsData.rhs` (i.e. `-|log q| ≤ -|log Theta|`), which is the Corollary 3.12
variant (`corollary312Variant_iff`).  The bridge does NOT prove that inequality; it records
that the remaining mathematical content is exactly the variant inequality.
No sorry/axiom; assembled from the existing A490/LANA port.
-/

namespace Iut

namespace Wall

variable (D : InitialThetaData.{0})

/-- **The NumericalWall bridge**: the numerical wall is exactly the q-pilot log-volume
inequality `-|log q| ≤ -|log Theta|` (the Corollary 3.12 variant inequality). -/
theorem numericalWall_iff_le_rhs :
    NumericalWall D ↔
      (concreteVariantData D).qPilot.lhs ≤ (concreteVariantData D).rhsData.rhs := by
  constructor
  · intro hW
    exact (corollary312Variant_iff (concreteVariantData D)).mp ((numericalWall_iff D).mp hW)
  · intro hle
    obtain ⟨U, hU, hI, hlog⟩ :=
      hullActual_exists_adelic_inHullOfImage_logVol D (concreteVariantData D).qPilot.lhs hle
    exact numericalWall_of_adelicHull_logVol D U hU hI hlog

/-- Convenience form: the inequality gives the numerical wall. -/
theorem numericalWall_of_le_rhs
    (hle : (concreteVariantData D).qPilot.lhs ≤ (concreteVariantData D).rhsData.rhs) :
    NumericalWall D :=
  (numericalWall_iff_le_rhs D).mpr hle

/-- Convenience form: the numerical wall gives the inequality. -/
theorem le_rhs_of_numericalWall (hW : NumericalWall D) :
    (concreteVariantData D).qPilot.lhs ≤ (concreteVariantData D).rhsData.rhs :=
  (numericalWall_iff_le_rhs D).mp hW

end Wall

end Iut
