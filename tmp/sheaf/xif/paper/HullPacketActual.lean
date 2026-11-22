import tmp.sheaf.xif.paper.SignedHullLogActual
import LeanFormal.IUT.IUTII.Theta.ConcreteSourceHistoryLinkBridge
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

/-!
# Actual log-shell hull packet data for SignedHullLogActual

This file supplies the actual packet/reference/tensor/procession data required
by SignedHullLogActual.lean from the project's actual theta packet scales.

Inputs used:
* sourcePositivePacket l : PositivePacket (sourceFiniteLabel l), the actual
  finite theta packet whose scales are the actual thetaScale l j
  (ConcreteSourceHistoryLinkBridge.lean);
* the actual sourcePositivePacket determinant/log-volume theorems;
* the unit reference packet with all scales exactly 1;
* the finite label type sourceFiniteLabel l = SignedsourceFiniteLabel l.value;
* the uniform finite procession weights normalized to total 1.

The one exact missing source field is theta_scales_ge_one: the actual theta
packet scales are required to be at least 1 for the signed hull normalization.
This is carried as a structure field, not asserted. No prohibited placeholder
constructs, axioms, or unfilled proofs are used. The resulting SignedHullLogActual is conditional on that
exact source field; no actual paper carrier or inhabitant is asserted.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u

namespace HullPacketActual

open LeanFormal.IUT.ConcreteSourceHistoryLinkBridge
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge
open LeanFormal.IUT.SignedLabel

variable (l : PrimeGeFive)

/-- The actual finite theta label type. -/
abbrev Label : Type := sourceFiniteLabel l

/-- Nonemptiness of the actual finite label type, via an actual representative. -/
instance labelNonempty : Nonempty (sourceFiniteLabel l) :=
  ⟨SignedLabel.representative l (0 : Fl l.value)⟩

/-- The actual hull log-shell packet: the source positive theta packet. -/
def hullPacket : PositivePacket (sourceFiniteLabel l) :=
  sourcePositivePacket l

/-- The actual reference/unit packet with all scales exactly 1. -/
def referencePacket : PositivePacket (sourceFiniteLabel l) where
  scale _ := 1
  positive _ := by norm_num

/-- The actual theta packet scale underlying the hull packet. -/
theorem hullPacket_scale (j : sourceFiniteLabel l) :
    (hullPacket l).scale j = thetaScale l j :=
  rfl

/-- The reference packet scale is exactly 1. -/
@[simp] theorem referencePacket_scale (j : sourceFiniteLabel l) :
    (referencePacket l).scale j = 1 :=
  rfl

/-- The actual hull packet is the source positive packet. -/
theorem hullPacket_eq_sourcePositivePacket :
    hullPacket l = sourcePositivePacket l :=
  rfl

/-- The reference packet has zero log-volume. -/
theorem referencePacket_logVolume_zero :
    packetLogVolume (referencePacket l) = 0 := by
  unfold packetLogVolume referencePacket
  apply Finset.sum_eq_zero
  intro j hj
  rw [Real.log_one]

/-- The reference packet determinant is 1. -/
theorem referencePacket_det_eq_one :
    packetDet (referencePacket l) = 1 := by
  rw [packetDet_eq_prod]
  apply Finset.prod_eq_one
  intro j hj
  rfl

/-- The actual hull packet determinant is the product of the theta scales. -/
theorem hullPacket_det_eq_theta_product :
    packetDet (hullPacket l) = ∏ j : sourceFiniteLabel l, thetaScale l j := by
  rw [hullPacket, sourcePositivePacket_det_eq_product]

/-- The actual hull packet log-volume is the theta log-volume. -/
theorem hullPacket_logVolume_eq_theta :
    packetLogVolume (hullPacket l) = thetaLogVolume l := by
  rw [hullPacket, sourcePositivePacket_log_volume_eq_theta]

/-- The actual hull packet log-volume is the log of its determinant. -/
theorem hullPacket_logVolume_eq_log_det :
    packetLogVolume (hullPacket l) =
      Real.log (packetDet (hullPacket l)) :=
  packetLogVolume_eq_log_det (hullPacket l)

/-- The hull packet determinant is positive. -/
theorem hullPacket_det_positive : 0 < packetDet (hullPacket l) := by
  change 0 < packetDet (sourcePositivePacket l)
  exact sourcePositivePacket_det_positive l

/-- The uniform procession: values are the logarithms of the actual theta
scales, weights are the reciprocal of the finite label cardinality. -/
def procession : WeightedValues (sourceFiniteLabel l) where
  value j := Real.log ((hullPacket l).scale j)
  weight _ := (Fintype.card (sourceFiniteLabel l) : Real)⁻¹
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hcard : (Fintype.card (sourceFiniteLabel l) : Real) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero (α := sourceFiniteLabel l)
    exact (mul_inv_cancel₀ hcard).symm

/-- The procession values are the actual log-scales. -/
@[simp] theorem procession_value (j : sourceFiniteLabel l) :
    (procession l).value j = Real.log (thetaScale l j) := by
  rfl

/-- The procession weight is the normalized reciprocal cardinality. -/
@[simp] theorem procession_weight (j : sourceFiniteLabel l) :
    (procession l).weight j = (Fintype.card (sourceFiniteLabel l) : Real)⁻¹ :=
  rfl

/-- The procession total weight is exactly 1. -/
theorem procession_weightTotal :
    (procession l).weightTotal = 1 :=
  rfl

/-- The procession weights are nonnegative. -/
theorem procession_weights_nonnegative (j : sourceFiniteLabel l) :
    0 <= (procession l).weight j := by
  rw [procession_weight]
  exact inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (sourceFiniteLabel l)))

/-- The exact missing source field: the actual theta packet scales are at
least 1. This is carried by the structure, not asserted from OriginalInput. -/
structure SourceFields where
  /-- The actual hull packet scales are at least 1. -/
  theta_scales_ge_one : forall j : sourceFiniteLabel l, 1 <= thetaScale l j

/-- Under the exact source scaling field, the uniform procession average of
the actual log-scales is nonnegative. -/
theorem procession_average_nonneg (S : SourceFields l) :
    0 <= (procession l).average := by
  unfold WeightedValues.average
  apply div_nonneg
  · exact Finset.sum_nonneg (fun j hi =>
      mul_nonneg (procession_weights_nonnegative l j) (by
        rw [procession_value]
        exact Real.log_nonneg (S.theta_scales_ge_one j)))
  · exact le_of_lt (procession l).weightTotal_pos


/-- The actual packet/reference/tensor/procession data, conditional on the
exact source scaling field. -/
structure Data where
  /-- The determinant tensor power M of det^{tensor M}. -/
  tensorPower : Nat
  tensorPower_pos : 0 < tensorPower
  /-- The exact source scaling condition. -/
  sourceScaling : SourceFields l

/-- The signed hull data obtained from the actual packet/reference/procession
and the source scaling field, in the exact shape required by
SignedHullLogActual. -/
def toSignedHullLogActual (D : Data l) :
    SignedHullLogActual (sourceFiniteLabel l) where
  hullPacket := hullPacket l
  referencePacket := referencePacket l
  tensorPower := D.tensorPower
  tensorPower_pos := D.tensorPower_pos
  hull_scales_ge_one := D.sourceScaling.theta_scales_ge_one
  reference_scales_eq_one := by
    intro j
    rfl
  procession := procession l
  procession_values := by
    intro j
    rfl
  weights_nonnegative := procession_weights_nonnegative l
  weightTotal_eq_one := procession_weightTotal l

/-- The normalized hull log-volume of the actual packet is M times the actual
theta log-volume. -/
theorem toSignedHullLogActual_hullLogVolume_eq (D : Data l) :
    (toSignedHullLogActual l D).hullLogVolume =
      (D.tensorPower : Real) * thetaLogVolume l := by
  rw [SignedHullLogActual.hullLogVolume_eq_tensor_mul_packet]
  change (D.tensorPower : Real) * packetLogVolume (hullPacket l) =
    (D.tensorPower : Real) * thetaLogVolume l
  rw [hullPacket_logVolume_eq_theta]

/-- The signed hull log-volume of the actual packet is minus M times the
actual theta log-volume. -/
theorem toSignedHullLogActual_signedHullLogVolume_eq (D : Data l) :
    (toSignedHullLogActual l D).signedHullLogVolume =
      -((D.tensorPower : Real) * thetaLogVolume l) := by
  rw [SignedHullLogActual.signedHullLogVolume_eq_neg,
    toSignedHullLogActual_hullLogVolume_eq]

/-- The signed hull log-volume is nonpositive. -/
theorem toSignedHullLogActual_signed_nonpos (D : Data l) :
    (toSignedHullLogActual l D).signedHullLogVolume <= 0 :=
  SignedHullLogActual.signedHullLogVolume_nonpos (toSignedHullLogActual l D)

/-- The signed procession normalized value is nonpositive. -/
theorem toSignedHullLogActual_signedProcession_nonpos (D : Data l) :
    (toSignedHullLogActual l D).signedProcessionNormalizedLogVolume <= 0 :=
  SignedHullLogActual.signedProcessionNormalizedLogVolume_nonpos
    (toSignedHullLogActual l D)

/-- The tensor normalization appears as the scalar M in the actual hull
log-volume. -/
theorem tensor_normalization_factor (D : Data l) :
    (toSignedHullLogActual l D).hullLogVolume =
      (D.tensorPower : Real) * thetaLogVolume l :=
  toSignedHullLogActual_hullLogVolume_eq l D

/-- The exact source fields, as a structure only; no inhabitant is asserted. -/
theorem sourceFields (D : Data l) : SourceFields l :=
  D.sourceScaling

end HullPacketActual

end
end LeanFormal.IUT