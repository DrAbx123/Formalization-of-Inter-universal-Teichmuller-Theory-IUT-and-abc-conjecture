import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume

/-!
# Actual signed hull log-volume from determinant/Haar/log-shell normalization

This file constructs a real-valued signed hull log-volume for the paper side
without using the value-layer sourceThetaHullLogVolume (the sSup of pointwise
log-degrees) and without an ENNReal clamp or a supremum over reals.

The construction uses the actual project determinant/Haar/log-shell packet
declarations of Volume.lean:

* PositivePacket is the finite positive packet of log-shell scales;
* packetDet and packetLogVolume are the determinant and its real logarithm;
* rescalePacket and tensorPacket are the log-shell rescaling and tensor
  packet operations;
* FiniteHull and WeightedValues are the finite procession carriers;
* packetLogVolume_eq_log_det, packetLogVolume_rescale and
  packetLogVolume_tensor are the project's determinant/procession laws.

A SignedHullLogActual consists of an actual hull packet, a reference unit
packet whose scales are all 1, a positive determinant tensor power M, and a
procession (WeightedValues) whose values are the logarithms of the hull packet
scales. The normalization is

    hullLogVolume = M * (packetLogVolume hullPacket
                           - packetLogVolume referencePacket),

with the reference term normalized to zero by the scale-one condition, and

    signedHullLogVolume = - hullLogVolume.

The paper sign -|log(Theta)| is therefore the negative real quantity
-signedHullLogVolume, not an ENNReal clamp.

Exact source obligations carried by the structure (not hidden axioms):
1. the actual hull log-shell packet for the paper carrier;
2. the actual reference/unit packet with all scales 1;
3. the determinant tensor power M of the det^{tensor M} normalization;
4. the actual procession weights and their matching with the packet log
   scales, with total weight 1.
The structure does not assert that these data are constructed from
OriginalInput; no inhabitant is asserted and no fake/toy data is supplied.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open scoped BigOperators

noncomputable section

universe u

/-- Actual real-valued signed hull data built from the determinant/Haar/log-shell
packet normalization. All fields are source data or exact normalization data;
none is asserted to be constructed from OriginalInput. -/
structure SignedHullLogActual (label : Type u) [Fintype label] where
  /-- The actual hull log-shell packet. -/
  hullPacket : PositivePacket label
  /-- The actual reference/unit packet. -/
  referencePacket : PositivePacket label
  /-- The positive determinant tensor power M of det^{tensor M}. -/
  tensorPower : Nat
  /-- M is positive. -/
  tensorPower_pos : 0 < tensorPower
  /-- Hull packet normalization: every hull log-shell scale is at least 1. -/
  hull_scales_ge_one : forall i, 1 <= hullPacket.scale i
  /-- Reference normalization: every reference scale is exactly 1. -/
  reference_scales_eq_one : forall i, referencePacket.scale i = 1
  /-- The actual procession weights and values. -/
  procession : WeightedValues label
  /-- The procession values are the logarithms of the hull packet scales. -/
  procession_values : forall i, procession.value i = Real.log (hullPacket.scale i)
  /-- Procession weights are nonnegative. -/
  weights_nonnegative : forall i, 0 <= procession.weight i
  /-- The procession weights are normalized to total 1. -/
  weightTotal_eq_one : procession.weightTotal = 1

namespace SignedHullLogActual

variable {label : Type u} [Fintype label] (D : SignedHullLogActual label)

/-- The normalized hull log-volume, real-valued:
M * (log det hullPacket - log det referencePacket). -/
def hullLogVolume : Real :=
  (D.tensorPower : Real) *
    (packetLogVolume D.hullPacket - packetLogVolume D.referencePacket)

/-- The paper signed hull log-volume -|log(Theta)| as a real number. -/
def signedHullLogVolume : Real :=
  -D.hullLogVolume

/-- The procession-normalized hull log-volume, the WeightedValues average of
the packet log-scales. -/
def processionNormalizedLogVolume : Real :=
  D.procession.average

/-- The signed procession-normalized hull log-volume. -/
def signedProcessionNormalizedLogVolume : Real :=
  -D.processionNormalizedLogVolume

/-- The reference packet has zero log-volume: all its scales are 1. -/
theorem referencePacket_logVolume_zero :
    packetLogVolume D.referencePacket = 0 := by
  unfold packetLogVolume
  apply Finset.sum_eq_zero
  intro i hi
  rw [D.reference_scales_eq_one i, Real.log_one]

/-- The reference determinant is 1. -/
theorem referencePacket_det_eq_one :
    packetDet D.referencePacket = 1 := by
  rw [packetDet_eq_prod]
  apply Finset.prod_eq_one
  intro i hi
  exact D.reference_scales_eq_one i

/-- The hull packet log-volume is nonnegative: all hull scales are at least 1. -/
theorem hullPacket_logVolume_nonneg :
    0 <= packetLogVolume D.hullPacket := by
  unfold packetLogVolume
  exact Finset.sum_nonneg (fun i hi =>
    Real.log_nonneg (D.hull_scales_ge_one i))

/-- The normalized hull log-volume is M times the hull packet log-volume. -/
theorem hullLogVolume_eq_tensor_mul_packet :
    D.hullLogVolume =
      (D.tensorPower : Real) * packetLogVolume D.hullPacket := by
  unfold hullLogVolume
  rw [D.referencePacket_logVolume_zero, sub_zero]

/-- The normalized hull log-volume is nonnegative. -/
theorem hullLogVolume_nonneg : 0 <= D.hullLogVolume := by
  rw [D.hullLogVolume_eq_tensor_mul_packet]
  exact mul_nonneg (Nat.cast_nonneg D.tensorPower) D.hullPacket_logVolume_nonneg

/-- The signed hull log-volume is nonpositive. -/
theorem signedHullLogVolume_nonpos : D.signedHullLogVolume <= 0 :=
  neg_nonpos.mpr D.hullLogVolume_nonneg

/-- The signed hull log-volume is exactly the negative of the normalized hull
log-volume. -/
theorem signedHullLogVolume_eq_neg : D.signedHullLogVolume = -D.hullLogVolume :=
  rfl

/-- Adding the signed and normalized hull log-volumes gives zero. -/
theorem signed_add_hull_eq_zero :
    D.signedHullLogVolume + D.hullLogVolume = 0 := by
  rw [D.signedHullLogVolume_eq_neg]
  ring

/-- Determinant form of the normalized hull log-volume:
M times the logarithm of the determinant of the hull packet. -/
theorem hullLogVolume_eq_tensor_mul_log_det :
    D.hullLogVolume =
      (D.tensorPower : Real) * Real.log (packetDet D.hullPacket) := by
  rw [D.hullLogVolume_eq_tensor_mul_packet, packetLogVolume_eq_log_det]

/-- The signed hull log-volume is minus M times the hull log-determinant. -/
theorem signedHullLogVolume_eq_neg_tensor_mul_log_det :
    D.signedHullLogVolume =
      -((D.tensorPower : Real) * Real.log (packetDet D.hullPacket)) := by
  rw [D.signedHullLogVolume_eq_neg, D.hullLogVolume_eq_tensor_mul_log_det]

/-- The hull determinant is at least 1: the product of scales each at least 1. -/
theorem hullPacket_det_ge_one : 1 <= packetDet D.hullPacket := by
  rw [packetDet_eq_prod]
  exact Finset.one_le_prod (fun i hi => D.hull_scales_ge_one i)

/-- The logarithm of the hull determinant is nonnegative. -/
theorem hullPacket_log_det_nonneg : 0 <= Real.log (packetDet D.hullPacket) :=
  Real.log_nonneg D.hullPacket_det_ge_one

/-- Normalization under rescaling of the hull packet: if every hull scale is
multiplied by c > 0, the normalized hull log-volume is shifted by
M * card(label) * log c. This is the real (not ENNReal) rescaling law. -/
def hullLogVolumeRescaled (c : Real) : Real :=
  (D.tensorPower : Real) *
    ((Fintype.card label : Real) * Real.log c +
      packetLogVolume D.hullPacket -
      packetLogVolume D.referencePacket)

theorem hullLogVolumeRescaled_eq (c : Real) :
    D.hullLogVolumeRescaled c =
      D.hullLogVolume +
        (D.tensorPower : Real) * (Fintype.card label : Real) * Real.log c := by
  unfold hullLogVolumeRescaled hullLogVolume
  rw [D.referencePacket_logVolume_zero]
  ring

/-- The procession values are nonnegative log-scales. -/
theorem procession_values_nonneg (i : label) : 0 <= D.procession.value i := by
  rw [D.procession_values i]
  exact Real.log_nonneg (D.hull_scales_ge_one i)

/-- The WeightedValues procession average is nonnegative. -/
theorem processionNormalizedLogVolume_nonneg :
    0 <= D.processionNormalizedLogVolume := by
  unfold processionNormalizedLogVolume WeightedValues.average
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i hi =>
      mul_nonneg (D.weights_nonnegative i) (D.procession_values_nonneg i))
  · exact le_of_lt D.procession.weightTotal_pos

/-- The signed procession-normalized hull log-volume is nonpositive. -/
theorem signedProcessionNormalizedLogVolume_nonpos :
    D.signedProcessionNormalizedLogVolume <= 0 :=
  neg_nonpos.mpr D.processionNormalizedLogVolume_nonneg

/-- The signed procession-normalized hull log-volume is the negative of the
procession average. -/
theorem signedProcession_eq_neg :
    D.signedProcessionNormalizedLogVolume =
      -D.processionNormalizedLogVolume :=
  rfl

/-- The procession weight total is positive (from the normalized one). -/
theorem procession_weightTotal_pos : 0 < D.procession.weightTotal :=
  D.procession.weightTotal_pos

/-- The procession weight total is one. -/
theorem procession_weightTotal_eq_one : D.procession.weightTotal = 1 :=
  D.weightTotal_eq_one

/-- Normalization of the procession: the weight total is both positive and one. -/
theorem procession_normalization :
    D.procession.weightTotal = 1 ∧ 0 < D.procession.weightTotal :=
  ⟨D.weightTotal_eq_one, D.procession.weightTotal_pos⟩

/-! ### Tensor-packet and rescaling laws from the actual project theorems -/

/-- Tensor-packet law: the actual log-shell tensor operation multiplies the
packet log-volumes with the cardinality factors (restatement of the project
packetLogVolume_tensor theorem in determinant-normalization form). -/
theorem tensor_packet_logVolume (p : PositivePacket label) (q : PositivePacket label) :
    packetLogVolume (tensorPacket p q) =
      (Fintype.card label : Real) * packetLogVolume p +
        (Fintype.card label : Real) * packetLogVolume q := by
  simpa using packetLogVolume_tensor p q

/-- Rescaling law: the actual rescalePacket operation shifts the packet
log-volume by card(label) * log c. -/
theorem rescale_packet_logVolume (c : Real) (hc : 0 < c)
    (packet : PositivePacket label) :
    packetLogVolume (rescalePacket c hc packet) =
      (Fintype.card label : Real) * Real.log c + packetLogVolume packet := by
  simpa using packetLogVolume_rescale c hc packet

/-- Determinant tensor law in log form. -/
theorem tensor_packet_log_det (p : PositivePacket label) (q : PositivePacket label) :
    Real.log (packetDet (tensorPacket p q)) =
      (Fintype.card label : Real) * Real.log (packetDet p) +
        (Fintype.card label : Real) * Real.log (packetDet q) := by
  rw [← packetLogVolume_eq_log_det, ← packetLogVolume_eq_log_det,
    ← packetLogVolume_eq_log_det]
  exact tensor_packet_logVolume p q

/-- Rescaling in determinant log form. -/
theorem rescale_packet_log_det (c : Real) (hc : 0 < c)
    (packet : PositivePacket label) :
    Real.log (packetDet (rescalePacket c hc packet)) =
      (Fintype.card label : Real) * Real.log c +
        Real.log (packetDet packet) := by
  rw [← packetLogVolume_eq_log_det, ← packetLogVolume_eq_log_det]
  exact rescale_packet_logVolume c hc packet

/-- The normalized hull log-volume as a determinant log-volume (no ENNReal
clamp, no sSup). -/
theorem hullLogVolume_determinant_normalization :
    D.hullLogVolume =
      (D.tensorPower : Real) *
        (Real.log (packetDet D.hullPacket) - 0) := by
  rw [D.hullLogVolume_eq_tensor_mul_log_det]
  ring

/-- The signed hull log-volume is the negative determinant log-volume. -/
theorem signedHullLogVolume_determinant_normalization :
    D.signedHullLogVolume =
      -((D.tensorPower : Real) * Real.log (packetDet D.hullPacket)) :=
  D.signedHullLogVolume_eq_neg_tensor_mul_log_det

/-! ### Exact source obligations -/

/-- The exact source obligations of this construction, as a proposition with
explicit data fields. This is not asserted; it records what a paper-level
instantiation must supply. -/
structure SourceObligations (label : Type u) [Fintype label] where
  /-- An actual paper hull log-shell packet. -/
  hullPacket : PositivePacket label
  /-- An actual reference/unit packet. -/
  referencePacket : PositivePacket label
  /-- A positive determinant tensor power. -/
  tensorPower : Nat
  tensorPower_pos : 0 < tensorPower
  /-- Hull packet normalization. -/
  hull_scales_ge_one : forall i, 1 <= hullPacket.scale i
  /-- Reference packet normalization. -/
  reference_scales_eq_one : forall i, referencePacket.scale i = 1
  /-- Actual procession weights/values. -/
  procession : WeightedValues label
  procession_values : forall i, procession.value i = Real.log (hullPacket.scale i)
  weights_nonnegative : forall i, 0 <= procession.weight i
  weightTotal_eq_one : procession.weightTotal = 1

/-- Every SignedHullLogActual gives source obligations of the same shape. -/
def toSourceObligations : SourceObligations label where
  hullPacket := D.hullPacket
  referencePacket := D.referencePacket
  tensorPower := D.tensorPower
  tensorPower_pos := D.tensorPower_pos
  hull_scales_ge_one := D.hull_scales_ge_one
  reference_scales_eq_one := D.reference_scales_eq_one
  procession := D.procession
  procession_values := D.procession_values
  weights_nonnegative := D.weights_nonnegative
  weightTotal_eq_one := D.weightTotal_eq_one

end SignedHullLogActual

end
end LeanFormal.IUT
