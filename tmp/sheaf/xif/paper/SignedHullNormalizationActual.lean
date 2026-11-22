import LeanFormal.IUT.IUTII.Theta.ConcreteSourceHistoryLinkBridge
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume

/-!
# Actual signed hull log-volume normalization

This file constructs the actual signed hull log-volume normalization from the
project's actual theta packet scales and the actual determinant/log-shell
packet laws of Volume.lean.

Data:
* hull packet: sourcePositivePacket l, the actual finite theta packet;
* reference packet: all scales 1, determinant 1, log-volume 0;
* determinant normalization: hullLogVolume = M * (packetLogVolume hull -
  packetLogVolume reference), with the reference term proved zero;
* procession: uniform finite weights 1/card(label), total weight 1, values the
  actual log-scales; the procession normalization equality with
  packetLogVolume/card is proved;
* signed hull log-volume: -hullLogVolume.

An actual inhabitant of NormalizedHullData is constructed at M = 1. The sign
nonpositivity requires the exact source scaling field theta_scales_ge_one;
that field is carried only as a structure and is not asserted. No fake/toy
data, no prohibited placeholders, no axioms, no unfilled proofs.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open scoped BigOperators
open LeanFormal.IUT.ConcreteSourceHistoryLinkBridge
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge

noncomputable section

universe u

namespace SignedHullNormalizationActual

variable (l : PrimeGeFive)

/-- Nonemptiness of the actual finite label type. -/
instance sourceFiniteLabelNonempty : Nonempty (sourceFiniteLabel l) :=
  ⟨SignedLabel.representative l (0 : Fl l.value)⟩

/-- The actual hull log-shell packet. -/
def hullPacket : PositivePacket (sourceFiniteLabel l) :=
  sourcePositivePacket l

/-- The actual reference/unit packet with all scales 1. -/
def referencePacket : PositivePacket (sourceFiniteLabel l) where
  scale _ := 1
  positive _ := by norm_num

/-- The actual uniform finite procession. -/
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

/-- Hull packet scales are the actual theta scales. -/
theorem hullPacket_scale (j : sourceFiniteLabel l) :
    (hullPacket l).scale j = thetaScale l j :=
  rfl

/-- Reference scales are 1. -/
@[simp] theorem referencePacket_scale (j : sourceFiniteLabel l) :
    (referencePacket l).scale j = 1 :=
  rfl

/-- Reference packet log-volume is zero. -/
theorem referencePacket_logVolume_zero :
    packetLogVolume (referencePacket l) = 0 := by
  unfold packetLogVolume referencePacket
  apply Finset.sum_eq_zero
  intro j hj
  rw [Real.log_one]

/-- Reference packet determinant is 1. -/
theorem referencePacket_det_eq_one :
    packetDet (referencePacket l) = 1 := by
  rw [packetDet_eq_prod]
  apply Finset.prod_eq_one
  intro j hj
  rfl

/-- Actual hull packet log-volume is the theta log-volume. -/
theorem hullPacket_logVolume_eq_theta :
    packetLogVolume (hullPacket l) = thetaLogVolume l := by
  rw [hullPacket, sourcePositivePacket_log_volume_eq_theta]

/-- Actual hull packet log-volume is its determinant logarithm. -/
theorem hullPacket_logVolume_eq_log_det :
    packetLogVolume (hullPacket l) =
      Real.log (packetDet (hullPacket l)) :=
  packetLogVolume_eq_log_det (hullPacket l)

/-- Actual hull determinant is the product of theta scales. -/
theorem hullPacket_det_eq_theta_product :
    packetDet (hullPacket l) = ∏ j : sourceFiniteLabel l, thetaScale l j := by
  rw [hullPacket, sourcePositivePacket_det_eq_product]

/-- Actual hull determinant is positive. -/
theorem hullPacket_det_positive : 0 < packetDet (hullPacket l) := by
  change 0 < packetDet (sourcePositivePacket l)
  exact sourcePositivePacket_det_positive l

/-- Procession values are the actual log-scales. -/
@[simp] theorem procession_value (j : sourceFiniteLabel l) :
    (procession l).value j = Real.log (thetaScale l j) := by
  rfl

/-- Procession weights are the normalized reciprocal cardinality. -/
@[simp] theorem procession_weight (j : sourceFiniteLabel l) :
    (procession l).weight j =
      (Fintype.card (sourceFiniteLabel l) : Real)⁻¹ :=
  rfl

/-- Procession total weight is 1. -/
theorem procession_weightTotal : (procession l).weightTotal = 1 :=
  rfl

/-- Procession weights are nonnegative. -/
theorem procession_weights_nonnegative (j : sourceFiniteLabel l) :
    0 <= (procession l).weight j := by
  rw [procession_weight]
  exact inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (sourceFiniteLabel l)))

/-- Procession normalization equality: the weighted average of the actual
log-scales is packetLogVolume divided by the label cardinality. -/
theorem procession_average_eq_packet_div_card :
    (procession l).average =
      packetLogVolume (hullPacket l) /
        (Fintype.card (sourceFiniteLabel l) : Real) := by
  unfold WeightedValues.average procession
  dsimp only
  unfold packetLogVolume hullPacket
  rw [div_one]
  rw [← Finset.mul_sum]
  rw [inv_mul_eq_div]

/-- Procession normalization: total weight one and the average equality. -/
theorem procession_normalization :
    (procession l).weightTotal = 1 ∧
      (procession l).average =
        packetLogVolume (hullPacket l) /
          (Fintype.card (sourceFiniteLabel l) : Real) :=
  ⟨procession_weightTotal l, procession_average_eq_packet_div_card l⟩

/-- Determinant/tensor normalization data. -/
structure NormalizedHullData (l : PrimeGeFive) where
  /-- The positive determinant tensor exponent M. -/
  tensorPower : Nat
  /-- M is positive. -/
  tensorPower_pos : 0 < tensorPower

namespace NormalizedHullData

/-- Normalized hull log-volume from actual determinant packets. -/
def hullLogVolume {l : PrimeGeFive} (D : NormalizedHullData l) : Real :=
  (D.tensorPower : Real) *
    (packetLogVolume (hullPacket l) - packetLogVolume (referencePacket l))

/-- Signed hull log-volume. -/
def signedHullLogVolume {l : PrimeGeFive} (D : NormalizedHullData l) : Real :=
  -hullLogVolume D

/-- Reference term vanishes: hull log-volume is M times the theta log-volume. -/
theorem hullLogVolume_eq_tensor_mul_theta {l : PrimeGeFive}
    (D : NormalizedHullData l) :
    D.hullLogVolume = (D.tensorPower : Real) * thetaLogVolume l := by
  unfold hullLogVolume
  rw [referencePacket_logVolume_zero, sub_zero]
  exact congrArg (fun x : Real => (D.tensorPower : Real) * x)
    (hullPacket_logVolume_eq_theta l)

/-- Determinant form of the normalized hull log-volume. -/
theorem hullLogVolume_eq_tensor_mul_log_det {l : PrimeGeFive}
    (D : NormalizedHullData l) :
    D.hullLogVolume =
      (D.tensorPower : Real) * Real.log (packetDet (hullPacket l)) := by
  have htheta :
      thetaLogVolume l = Real.log (packetDet (hullPacket l)) :=
    (hullPacket_logVolume_eq_theta l).symm.trans
      (hullPacket_logVolume_eq_log_det l)
  rw [D.hullLogVolume_eq_tensor_mul_theta, htheta]

/-- Tensor normalization is linear in the exponent for fixed packets. -/
theorem hullLogVolume_tensor_linear {l : PrimeGeFive}
    (D : NormalizedHullData l) (N : Nat) :
    D.hullLogVolume + (N : Real) * thetaLogVolume l =
      ((D.tensorPower + N : Nat) : Real) * thetaLogVolume l := by
  rw [D.hullLogVolume_eq_tensor_mul_theta]
  push_cast
  ring

/-- Signed hull log-volume is minus M times the theta log-volume. -/
theorem signedHullLogVolume_eq {l : PrimeGeFive}
    (D : NormalizedHullData l) :
    D.signedHullLogVolume = -((D.tensorPower : Real) * thetaLogVolume l) := by
  rw [signedHullLogVolume, D.hullLogVolume_eq_tensor_mul_theta]

/-- Signed plus normalized hull log-volume cancels. -/
theorem signed_add_hull_eq_zero {l : PrimeGeFive}
    (D : NormalizedHullData l) :
    D.signedHullLogVolume + D.hullLogVolume = 0 := by
  rw [signedHullLogVolume]
  ring

end NormalizedHullData

/-- The actual normalization inhabitant at determinant exponent 1. -/
def actualNormalizedHullData (l : PrimeGeFive) : NormalizedHullData l where
  tensorPower := 1
  tensorPower_pos := by norm_num

/-- Actual hull log-volume at M = 1 equals the theta log-volume. -/
theorem actual_hullLogVolume_eq_theta (l : PrimeGeFive) :
    (actualNormalizedHullData l).hullLogVolume = thetaLogVolume l := by
  rw [NormalizedHullData.hullLogVolume_eq_tensor_mul_theta]
  simp [actualNormalizedHullData]

/-- Actual signed hull log-volume at M = 1 is minus the theta log-volume. -/
theorem actual_signedHullLogVolume_eq (l : PrimeGeFive) :
    (actualNormalizedHullData l).signedHullLogVolume = -thetaLogVolume l := by
  rw [NormalizedHullData.signedHullLogVolume_eq]
  simp [actualNormalizedHullData]

/-- Exact source scaling field required for sign nonpositivity. -/
structure ScalingSource (l : PrimeGeFive) where
  /-- All actual hull packet scales are at least 1. -/
  theta_scales_ge_one :
    forall j : sourceFiniteLabel l, 1 <= thetaScale l j

/-- The actual procession average is nonnegative under the exact scaling field. -/
theorem procession_average_nonneg {l : PrimeGeFive} (S : ScalingSource l) :
    0 <= (procession l).average := by
  unfold WeightedValues.average
  apply div_nonneg
  · exact Finset.sum_nonneg (fun j hj =>
      mul_nonneg (procession_weights_nonnegative l j) (by
        rw [procession_value]
        exact Real.log_nonneg (S.theta_scales_ge_one j)))
  · exact le_of_lt (procession l).weightTotal_pos

/-- The normalized hull log-volume is nonnegative under the exact scaling
source. -/
theorem hullLogVolume_nonneg {l : PrimeGeFive}
    (D : NormalizedHullData l) (S : ScalingSource l) :
    0 <= D.hullLogVolume := by
  rw [D.hullLogVolume_eq_tensor_mul_theta]
  exact mul_nonneg (Nat.cast_nonneg D.tensorPower)
    (Finset.sum_nonneg (fun j hj => Real.log_nonneg (S.theta_scales_ge_one j)))

/-- The signed hull log-volume is nonpositive under the exact scaling source. -/
theorem signedHullLogVolume_nonpos {l : PrimeGeFive}
    (D : NormalizedHullData l) (S : ScalingSource l) :
    D.signedHullLogVolume <= 0 :=
  neg_nonpos.mpr (hullLogVolume_nonneg D S)

/-- Exact obligations summary. -/
structure SourceObligations (l : PrimeGeFive) where
  /-- The determinant tensor exponent M is positive. -/
  tensorPower : Nat
  tensorPower_pos : 0 < tensorPower
  /-- The exact theta packet scaling condition. -/
  theta_scales_ge_one :
    forall j : sourceFiniteLabel l, 1 <= thetaScale l j

/-- Actual M=1 normalization plus the exact scaling source supplies the
obligations structure. -/
def actualSourceObligations (l : PrimeGeFive) (S : ScalingSource l) :
    SourceObligations l where
  tensorPower := 1
  tensorPower_pos := by norm_num
  theta_scales_ge_one := S.theta_scales_ge_one

end SignedHullNormalizationActual

end
end LeanFormal.IUT
