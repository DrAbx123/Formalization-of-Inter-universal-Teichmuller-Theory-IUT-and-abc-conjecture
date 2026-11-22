/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.WeightedNormalization
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-!
# P6-A: (C17) WeightedDeterminantPacket interface instantiation

Status: PARTIAL. This file proves the **packet-interface identity** behind (C17):
for two packets with the same denominator family, the weighted log-volume
difference is the common tensor degree times the normalized difference. It also
records the (Ob3-2)/(Ob3-3) profile scaling from
`HullDeterminantLogVolumeReduction`.

The actual q-side and Theta-side normalized readings are not identified with
`WeightedDeterminantPacket.normalizedLogVolume` here: that is exactly the named
gap `GAP-P6-C17-DICT`. No actual q/Theta packet is asserted; the conditional
theorem below only consumes the gap as an explicit hypothesis, never as a field
of a shared structure.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1WeightedDetPacketActual

open LeanFormal.IUT
open scoped BigOperators

universe u

/-- Two packets with the same denominator family have the same common tensor degree. -/
theorem commonTensorDegree_eq_of_denominator_eq {label : Type*} [Fintype label]
    (P Q : WeightedDeterminantPacket label)
    (hden : P.denominator = Q.denominator) :
    P.commonTensorDegree = Q.commonTensorDegree := by
  unfold WeightedDeterminantPacket.commonTensorDegree
  rw [hden]

/-- **C17 packet identity**: weighted difference = N * normalized difference. -/
theorem weightedLogVolume_sub_eq_commonTensorDegree_mul_normalized_sub
    {label : Type*} [Fintype label]
    (P Q : WeightedDeterminantPacket label)
    (hden : P.denominator = Q.denominator) :
    P.weightedLogVolume - Q.weightedLogVolume =
      (P.commonTensorDegree : Real) *
        (P.normalizedLogVolume - Q.normalizedLogVolume) := by
  rw [WeightedDeterminantPacket.weightedLogVolume_eq_commonTensorDegree_mul_normalizedLogVolume,
    WeightedDeterminantPacket.weightedLogVolume_eq_commonTensorDegree_mul_normalizedLogVolume]
  rw [commonTensorDegree_eq_of_denominator_eq P Q hden]
  ring

/-- Named exact gap: the packet normalized logs are the actual q/Theta normalized
readings.  This is a `Prop`, not an assumption of a structure. -/
def GAP_P6_C17_DICT
    (qPacketNormalized thetaPacketNormalized qActual thetaActual : Real) : Prop :=
  qPacketNormalized = qActual ∧ thetaPacketNormalized = thetaActual

/-- Conditional (C17) form: once the named gap holds and `thetaActual - qActual = M`,
the weighted difference is `N * M`.  The gap is an explicit hypothesis, not a
field of a shared structure. -/
theorem weightedLogVolume_sub_eq_commonTensorDegree_mul_M
    {label : Type*} [Fintype label]
    (P Q : WeightedDeterminantPacket label)
    (hden : P.denominator = Q.denominator)
    (M qActual thetaActual : Real)
    (hgap : GAP_P6_C17_DICT P.normalizedLogVolume Q.normalizedLogVolume qActual thetaActual)
    (hM : thetaActual - qActual = M) :
    Q.weightedLogVolume - P.weightedLogVolume =
      (P.commonTensorDegree : Real) * M := by
  have h := weightedLogVolume_sub_eq_commonTensorDegree_mul_normalized_sub Q P hden.symm
  rw [h]
  rw [commonTensorDegree_eq_of_denominator_eq Q P hden.symm]
  rw [hgap.1, hgap.2, hM]

/-- Re-export of the (Ob3-2)/(Ob3-3) profile-degree scaling from the green
hull-determinant reduction: the adjusted det tensor power has degree `M` times
the degree difference. -/
theorem c17_profileArithmeticDegree_adjustedDetTensorPower
    {Place : Type*} [Fintype Place] (M : Nat)
    (arithmeticBundle structureSheaf : Place -> Real) :
    profileArithmeticDegree (M • (arithmeticBundle - structureSheaf)) =
      (M : Real) * (profileArithmeticDegree arithmeticBundle -
        profileArithmeticDegree structureSheaf) :=
  profileArithmeticDegree_adjustedDetTensorPower M arithmeticBundle structureSheaf

def c17Rows : List (String × String × String) :=
  [ ("commonTensorDegree_eq_of_denominator_eq", "denominator family determines N", "PROVED"),
    ("weightedLogVolume_sub_eq_commonTensorDegree_mul_normalized_sub", "weighted diff = N * normalized diff", "PROVED"),
    ("GAP_P6_C17_DICT", "packet normalized = actual q/Theta readings", "GAP (Prop, explicit)"),
    ("weightedLogVolume_sub_eq_commonTensorDegree_mul_M", "conditional (C17) = N*M", "PROVED conditional on gap"),
    ("c17_profileArithmeticDegree_adjustedDetTensorPower", "Ob3-2/Ob3-3 degree scaling", "PROVED (re-export)") ]

theorem c17Rows_length : c17Rows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1WeightedDetPacketActual
