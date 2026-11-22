/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ThetaModLProjectionActual

/-! # Reuse: corollaries of the mod-l theta/elliptic projection rules -/

namespace LeanFormal.IUT

universe u

variable (G : Type u) [Group G]

theorem modLThetaProjection_apply_one (g : G) :
    modLThetaProjection G 1 g =
      QuotientGroup.mk (QuotientGroup.mk g : ThetaQuotient G) :=
  modLThetaProjection_apply G 1 g

theorem modLEllipticProjection_apply_one (g : G) :
    modLEllipticProjection G 1 g =
      QuotientGroup.mk (QuotientGroup.mk g : EllipticAbelianization G) :=
  modLEllipticProjection_apply G 1 g

theorem modLThetaProjection_congr {g h : G} (hgh : g = h) (l : Nat) :
    modLThetaProjection G l g = modLThetaProjection G l h := by
  rw [hgh]

theorem modLEllipticProjection_congr {g h : G} (hgh : g = h) (l : Nat) :
    modLEllipticProjection G l g = modLEllipticProjection G l h := by
  rw [hgh]

theorem modLThetaProjection_eq_comp_apply (l : Nat) (g : G) :
    modLThetaProjection G l g =
      (QuotientGroup.mk' (thetaPowerKernel G l))
        ((QuotientGroup.mk' (thetaCommutatorKernel G)) g) := by
  rw [modLThetaProjection_eq_comp]
  rfl

theorem modLEllipticProjection_eq_comp_apply (l : Nat) (g : G) :
    modLEllipticProjection G l g =
      (QuotientGroup.mk' (ellipticPowerKernel G l))
        ((QuotientGroup.mk' (thetaDerivedSubgroup G)) g) := by
  rw [modLEllipticProjection_eq_comp]
  rfl

end LeanFormal.IUT
