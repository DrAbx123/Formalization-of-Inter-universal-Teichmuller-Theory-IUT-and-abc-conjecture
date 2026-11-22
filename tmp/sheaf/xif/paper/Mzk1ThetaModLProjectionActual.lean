/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Theta.EtaleThetaQuotient

/-!
# Mod-l projections of the theta/elliptic quotients: computation on classes

Declaration-level addendum to `EtaleThetaQuotient`: the mod-l theta and elliptic
projections are computed on a group element by the two-stage quotient class.  These
are the elementary computation rules needed when passing between the group G, the
theta quotient and the elliptic abelianization in the EtTh realization rows.

SHEAF node: iuti-ii:Theta.ModLProjection (kind theorem, status PENDING-VERIFY until
the DAG watchdog reports EXIT0).  No new axioms.
-/

namespace LeanFormal.IUT

universe u

variable (G : Type u) [Group G]

/-- The mod-l theta projection sends g to the double quotient class of g. -/
theorem modLThetaProjection_apply (l : Nat) (g : G) :
    modLThetaProjection G l g =
      QuotientGroup.mk (QuotientGroup.mk g : ThetaQuotient G) := by
  simp [modLThetaProjection]

/-- The mod-l elliptic projection sends g to the double quotient class of g. -/
theorem modLEllipticProjection_apply (l : Nat) (g : G) :
    modLEllipticProjection G l g =
      QuotientGroup.mk (QuotientGroup.mk g : EllipticAbelianization G) := by
  simp [modLEllipticProjection]

/-- The theta mod-l projection factors through the theta quotient projection. -/
theorem modLThetaProjection_eq_comp (l : Nat) :
    modLThetaProjection G l =
      (QuotientGroup.mk' (thetaPowerKernel G l)).comp
        (QuotientGroup.mk' (thetaCommutatorKernel G)) := rfl

/-- The elliptic mod-l projection factors through the derived-subgroup projection. -/
theorem modLEllipticProjection_eq_comp (l : Nat) :
    modLEllipticProjection G l =
      (QuotientGroup.mk' (ellipticPowerKernel G l)).comp
        (QuotientGroup.mk' (thetaDerivedSubgroup G)) := rfl

end LeanFormal.IUT
