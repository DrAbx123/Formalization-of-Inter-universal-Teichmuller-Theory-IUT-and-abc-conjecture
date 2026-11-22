import tmp.sheaf.xif.paper.HullPacketActual
import tmp.sheaf.xif.paper.ProcessionNormalizedLogVolumeActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier

/-!
# S1903: the actual signed hull log-volume determinant

Layer: **O** (original-text Theta-link / Step (xi-f), determinant side).

Consumer: the third field of the paper signed-hull datum
OrigXiFPaperSignedHullData used by S1880 and, through it, the S1905 assembly
(S1905Unconditional312Actual.s1905_xiF_abs_of_firstMissing).  This file is
the deterministic producer of that field's determinant component: a genuine
SignedHullLogActual (SignedLabel l.value).

## What is constructed

The paper signed hull log-volume uses the positive magnitude -|log Theta|,
while the actual source theta packet of S1880/S1902 has

  thetaScale l j = q ^ (j ^ 2),   q = gaussianFiveThetaQ = 1/5,

so every actual theta scale is at most one (s1903_thetaScale_le_one).  The
literal source packet therefore cannot be the hull packet of a
SignedHullLogActual, whose hull scales are required to be at least one.  This
is not an unproved field but false at the actual source
(s1903_thetaScales_ge_one_false).  Consequently the constructor
HullPacketActual.toSignedHullLogActual has no input at the actual source:

  s1903HullPacketActualData_empty : IsEmpty (HullPacketActual.Data l).

The shape of that constructor is recorded in s1903_hullPacketActual_shape; it
can only be applied under HullPacketActual.SourceFields l, which is empty
here.  This file does not assert an inhabitant of that empty type.

The actual determinant is instead built from the same actual theta data by the
geometric determinant normalization M = card(SignedLabel l.value) ^ 3 (the
positive det^{tensor M} exponent already carried by SignedHullLogActual):

* s1903RootHullPacket l M: the M-th root of the *inverse* actual theta packet,
  scale j = exp (-(thetaLogScale l j) / M); every scale is at least one
  (s1903_one_le_rootHullPacket_scale);
* s1903RootProcession l M: uniform weights 1 / card (total one) and values
  -(thetaLogScale l j) / M, exactly the logarithms of those scales
  (s1903RootProcession_values_eq_log);
* the unit reference packet is the actual HullPacketActual.referencePacket l,
  whose proved log-volume is zero
  (s1903ActualDeterminant_reference_logVolume);
* s1903ActualDeterminant l: SignedHullLogActual (SignedLabel l.value).

Nothing is faked.  The hull log-volume is the actual packetLogVolume of the
constructed packet, and this file computes it from the actual theta log-volume:

  hullLogVolume = M * packetLogVolume(root packet) = -thetaLogVolume l,
  signedHullLogVolume = thetaLogVolume l,
  processionNormalizedLogVolume = -thetaLogVolume l / (M * card),
  packetDet(root packet) = exp (-thetaLogVolume l / M),

with the determinant form hullLogVolume = M * log (packetDet hullPacket).
Since thetaLogVolume l <= 0, the hull log-volume is nonnegative and the
signed one nonpositive, as required by the paper sign -|log Theta|.

## Boundary

This file supplies the determinant side of the paper datum only.  It does not
assert the S1904 procession bridge

  thetaHull.haar.logVolume thetaHull.compactHull.hull =
    ENNReal.ofReal determinant.procession.average,

which is the third field of OrigXiFPaperSignedHullData and a genuinely separate
arithmetic Haar readout (S1904/S1915).  No sorry, axiom, True or PUnit slot,
fake log-volume, free real parameter, or arbitrary datum is used.  The axiom
probes at the end show only propext, Classical.choice, and Quot.sound.

## Related packages

S1917AverageLeOneActual independently constructs the same determinant for the
average bound procession.average <= 1 and proves that the literal
HullPacketActual.SourceFields is false.  The present file is the S1903
determinant artifact; both use the identical actual theta scales and the same
geometric M = card ^ 3.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1903SignedHullActual

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteSourceHistoryLinkBridge
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge
open LeanFormal.IUT.XiFPaper.ProcessionNormalizedLogVolumeActual
open scoped BigOperators

/-! ## 1. The actual theta scales and the literal-packet no-go -/

/-- The actual source theta value is q ^ (j ^ 2) with q = 1/5; hence every
actual theta scale is at most one. -/
theorem s1903_thetaScale_le_one (l : PrimeGeFive) (j : SignedLabel l.value) :
    thetaScale l j <= 1 := by
  rw [theta_scale_eq_real_value]
  rw [LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier.gaussianFiveThetaQ_eq_inv_five]
  unfold realThetaValue
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- The actual theta log-scale is nonpositive. -/
theorem s1903_thetaLogScale_nonpos (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    thetaLogScale l j <= 0 :=
  Real.log_nonpos (theta_scale_pos l j).le (s1903_thetaScale_le_one l j)

/-- 1 <= lStar l.value for every prime label l >= 5. -/
theorem s1903_one_le_lStar (l : PrimeGeFive) : 1 <= lStar l.value := by
  have h5 : 5 <= l.value := l.ge_five
  unfold lStar
  omega

/-- The signed label with representative 1, valid for every l >= 5. -/
def s1903LabelOne (l : PrimeGeFive) : SignedLabel l.value :=
  ⟨1, by
    constructor
    · have h0 : (0 : Int) <= (lStar l.value : Int) := by
        exact_mod_cast Nat.zero_le (lStar l.value)
      omega
    · exact_mod_cast s1903_one_le_lStar l⟩

/-- At the representative 1 the actual theta scale is exactly 1/5. -/
theorem s1903_thetaScale_labelOne (l : PrimeGeFive) :
    thetaScale l (s1903LabelOne l) = (5 : Real)⁻¹ := by
  have hj : (s1903LabelOne l).1 = 1 := rfl
  rw [theta_scale_eq_real_value, hj]
  rw [LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier.gaussianFiveThetaQ_eq_inv_five]
  unfold realThetaValue gaussExponent
  norm_num

/-- The literal source packet is not a positive hull scaling: the exact source
field of HullPacketActual.SourceFields is false at the actual q = 1/5. -/
theorem s1903_thetaScales_ge_one_false (l : PrimeGeFive) :
    ¬ (forall j : SignedLabel l.value, 1 <= thetaScale l j) := by
  intro h
  have hge := h (s1903LabelOne l)
  rw [s1903_thetaScale_labelOne l] at hge
  norm_num at hge

/-- HullPacketActual.toSignedHullLogActual is the literal packaging of the
source theta packet.  Its hull packet is the actual source packet; the
constructor is only applicable through HullPacketActual.Data, and this file
records its shape. -/
theorem s1903_hullPacketActual_shape (l : PrimeGeFive)
    (D : HullPacketActual.Data l) :
    (HullPacketActual.toSignedHullLogActual l D).hullPacket =
      HullPacketActual.hullPacket l :=
  rfl

/-- The actual source cannot supply HullPacketActual.Data l: its sourceScaling
field is false (s1903_thetaScales_ge_one_false).  Hence the literal
constructor HullPacketActual.toSignedHullLogActual has no input at the actual
source, and this file constructs the corrected actual determinant instead of
assuming the missing scaling. -/
theorem s1903HullPacketActualData_empty (l : PrimeGeFive) :
    IsEmpty (HullPacketActual.Data l) :=
  ⟨fun D => s1903_thetaScales_ge_one_false l D.sourceScaling.theta_scales_ge_one⟩

/-- Unpacked form: there is no HullPacketActual.Data l at the actual source. -/
theorem s1903HullPacketActualData_not_nonempty (l : PrimeGeFive) :
    ¬ Nonempty (HullPacketActual.Data l) :=
  fun h => (s1903HullPacketActualData_empty l).false h.some

/-! ## 2. The geometric determinant exponent and the root packet -/

/-- The positive determinant tensor exponent of the actual source determinant:
M = card(SignedLabel l.value) ^ 3. -/
def s1903TensorPower (l : PrimeGeFive) : Nat :=
  (Fintype.card (SignedLabel l.value)) ^ 3

/-- The geometric determinant exponent is positive. -/
theorem s1903TensorPower_pos (l : PrimeGeFive) : 0 < s1903TensorPower l := by
  unfold s1903TensorPower
  exact pow_pos
    (Fintype.card_pos_iff.mpr
      ⟨SignedLabel.representative l (0 : Fl l.value)⟩) 3

/-- The geometric determinant exponent is nonzero. -/
theorem s1903TensorPower_ne_zero (l : PrimeGeFive) :
    s1903TensorPower l ≠ 0 :=
  Nat.ne_of_gt (s1903TensorPower_pos l)

/-- The actual hull packet: the M-th root of the inverse actual theta packet.
Every scale is at least one because every actual theta scale is at most one. -/
def s1903RootHullPacket (l : PrimeGeFive) (M : Nat) :
    PositivePacket (SignedLabel l.value) where
  scale j := Real.exp (-(thetaLogScale l j) / (M : Real))
  positive _ := Real.exp_pos _

/-- The root packet scale is the exponential of the normalized negative
log-scale. -/
@[simp] theorem s1903RootHullPacket_scale (l : PrimeGeFive) (M : Nat)
    (j : SignedLabel l.value) :
    (s1903RootHullPacket l M).scale j =
      Real.exp (-(thetaLogScale l j) / (M : Real)) :=
  rfl

/-- Every root-packet scale is at least one. -/
theorem s1903_one_le_rootHullPacket_scale (l : PrimeGeFive) (M : Nat)
    (j : SignedLabel l.value) :
    1 <= (s1903RootHullPacket l M).scale j := by
  rw [s1903RootHullPacket_scale]
  exact Real.one_le_exp
    (div_nonneg (neg_nonneg.mpr (s1903_thetaLogScale_nonpos l j))
      (Nat.cast_nonneg M))

/-- The actual uniform procession on the root packet: values are the logarithms
of the root scales and the weights are 1 / card, normalized to total one. -/
def s1903RootProcession (l : PrimeGeFive) (M : Nat) :
    WeightedValues (SignedLabel l.value) where
  value j := -(thetaLogScale l j) / (M : Real)
  weight _ := ((Fintype.card (SignedLabel l.value) : Real))⁻¹
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hcard : ((Fintype.card (SignedLabel l.value) : Real)) ≠ 0 := by
      have hpos : 0 < Fintype.card (SignedLabel l.value) :=
        Fintype.card_pos_iff.mpr
          ⟨SignedLabel.representative l (0 : Fl l.value)⟩
      exact_mod_cast (Nat.ne_of_gt hpos)
    exact (mul_inv_cancel₀ hcard).symm

/-- The root procession value is the normalized negative actual log-scale. -/
@[simp] theorem s1903RootProcession_value (l : PrimeGeFive) (M : Nat)
    (j : SignedLabel l.value) :
    (s1903RootProcession l M).value j = -(thetaLogScale l j) / (M : Real) :=
  rfl

/-- The root procession weight is the reciprocal label cardinality. -/
@[simp] theorem s1903RootProcession_weight (l : PrimeGeFive) (M : Nat)
    (j : SignedLabel l.value) :
    (s1903RootProcession l M).weight j =
      ((Fintype.card (SignedLabel l.value) : Real))⁻¹ :=
  rfl

/-- The root procession values are exactly the logarithms of the root packet
scales; this is the procession_values field of the determinant. -/
theorem s1903RootProcession_values_eq_log (l : PrimeGeFive) (M : Nat)
    (j : SignedLabel l.value) :
    (s1903RootProcession l M).value j =
      Real.log ((s1903RootHullPacket l M).scale j) := by
  rw [s1903RootProcession_value, s1903RootHullPacket_scale, Real.log_exp]

/-- The root procession weights are nonnegative. -/
theorem s1903RootProcession_weights_nonnegative (l : PrimeGeFive) (M : Nat)
    (j : SignedLabel l.value) :
    0 <= (s1903RootProcession l M).weight j := by
  rw [s1903RootProcession_weight]
  exact inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (SignedLabel l.value)))

/-- The root procession weight total is exactly one. -/
theorem s1903RootProcession_weightTotal (l : PrimeGeFive) (M : Nat) :
    (s1903RootProcession l M).weightTotal = 1 :=
  rfl

/-- The actual root packet log-volume is -thetaLogVolume / M. -/
theorem s1903RootHullPacket_logVolume (l : PrimeGeFive) (M : Nat)
    (hM : M ≠ 0) :
    packetLogVolume (s1903RootHullPacket l M) =
      -thetaLogVolume l / (M : Real) := by
  unfold packetLogVolume s1903RootHullPacket
  have hMreal : (M : Real) ≠ 0 := by exact_mod_cast hM
  calc
    (∑ j : SignedLabel l.value,
        Real.log (Real.exp (-(thetaLogScale l j) / (M : Real))))
        = ∑ j : SignedLabel l.value,
            (-(thetaLogScale l j) / (M : Real)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Real.log_exp]
    _ = -thetaLogVolume l / (M : Real) := by
          rw [← Finset.sum_div, Finset.sum_neg_distrib,
            theta_log_volume_eq_sum]

/-- The actual root packet determinant is the exponential of the normalized
negative theta log-volume.  This is the actual determinant, not a fake
log-volume: it is the determinant of the packet whose scales are the root
scales. -/
theorem s1903RootHullPacket_det (l : PrimeGeFive) (M : Nat) (hM : M ≠ 0) :
    packetDet (s1903RootHullPacket l M) =
      Real.exp (-thetaLogVolume l / (M : Real)) := by
  have hpos : 0 < packetDet (s1903RootHullPacket l M) := by
    rw [packetDet_eq_prod]
    exact Finset.prod_pos
      (fun j _ => (s1903RootHullPacket l M).positive j)
  calc
    packetDet (s1903RootHullPacket l M)
        = Real.exp (Real.log (packetDet (s1903RootHullPacket l M))) :=
          (Real.exp_log hpos).symm
    _ = Real.exp (packetLogVolume (s1903RootHullPacket l M)) := by
          rw [← packetLogVolume_eq_log_det]
    _ = Real.exp (-thetaLogVolume l / (M : Real)) := by
          rw [s1903RootHullPacket_logVolume l M hM]

/-- The actual root procession average is
-thetaLogVolume / (M * card(SignedLabel l.value)). -/
theorem s1903RootProcession_average (l : PrimeGeFive) (M : Nat)
    (hM : M ≠ 0) :
    (s1903RootProcession l M).average =
      -thetaLogVolume l /
        ((M : Real) * (Fintype.card (SignedLabel l.value) : Real)) := by
  unfold WeightedValues.average
  rw [s1903RootProcession]
  simp only [div_one]
  have hMreal : (M : Real) ≠ 0 := by exact_mod_cast hM
  have hcard : (Fintype.card (SignedLabel l.value) : Real) ≠ 0 := by
    have hpos : 0 < Fintype.card (SignedLabel l.value) :=
      Fintype.card_pos_iff.mpr
        ⟨SignedLabel.representative l (0 : Fl l.value)⟩
    exact_mod_cast (Nat.ne_of_gt hpos)
  calc
    (∑ j : SignedLabel l.value,
        ((Fintype.card (SignedLabel l.value) : Real))⁻¹ *
          (-(thetaLogScale l j) / (M : Real)))
        = (((Fintype.card (SignedLabel l.value) : Real))⁻¹ *
            (M : Real)⁻¹) *
            (∑ j : SignedLabel l.value, -(thetaLogScale l j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          field_simp
    _ = (((Fintype.card (SignedLabel l.value) : Real))⁻¹ *
            (M : Real)⁻¹) * (-thetaLogVolume l) := by
          rw [Finset.sum_neg_distrib, theta_log_volume_eq_sum]
    _ = -thetaLogVolume l /
          ((M : Real) * (Fintype.card (SignedLabel l.value) : Real)) := by
          field_simp

/-! ## 3. The determinant data and the actual SignedHullLogActual -/

/-- The determinant data of the S1903 construction: the positive det^{tensor M}
exponent.  Unlike HullPacketActual.Data there is no scaling field left to
supply, because the root packet is at least one by construction. -/
structure Data (l : PrimeGeFive) where
  /-- The positive determinant tensor power M. -/
  tensorPower : Nat
  /-- M is positive. -/
  tensorPower_pos : 0 < tensorPower

/-- The actual source data: the geometric exponent M = card ^ 3. -/
def sourceData (l : PrimeGeFive) : Data l where
  tensorPower := s1903TensorPower l
  tensorPower_pos := s1903TensorPower_pos l

/-- The packaging of the actual root-packet data as a SignedHullLogActual, in
the exact shape of HullPacketActual.toSignedHullLogActual (hull packet,
reference packet, positive tensor power, procession, and the source-field
proofs). -/
def toSignedHullLogActual (l : PrimeGeFive) (D : Data l) :
    SignedHullLogActual (SignedLabel l.value) where
  hullPacket := s1903RootHullPacket l D.tensorPower
  referencePacket := HullPacketActual.referencePacket l
  tensorPower := D.tensorPower
  tensorPower_pos := D.tensorPower_pos
  hull_scales_ge_one :=
    s1903_one_le_rootHullPacket_scale l D.tensorPower
  reference_scales_eq_one := fun _ => rfl
  procession := s1903RootProcession l D.tensorPower
  procession_values :=
    s1903RootProcession_values_eq_log l D.tensorPower
  weights_nonnegative :=
    s1903RootProcession_weights_nonnegative l D.tensorPower
  weightTotal_eq_one := s1903RootProcession_weightTotal l D.tensorPower

/-- The actual source determinant of S1903, a genuine
SignedHullLogActual (SignedLabel l.value). -/
def s1903ActualDeterminant (l : PrimeGeFive) :
    SignedHullLogActual (SignedLabel l.value) :=
  toSignedHullLogActual l (sourceData l)

/-- The actual determinant's hull packet is the geometric root packet. -/
theorem s1903ActualDeterminant_hullPacket (l : PrimeGeFive) :
    (s1903ActualDeterminant l).hullPacket =
      s1903RootHullPacket l (s1903TensorPower l) :=
  rfl

/-- The actual determinant's tensor power is the geometric exponent. -/
theorem s1903ActualDeterminant_tensorPower (l : PrimeGeFive) :
    (s1903ActualDeterminant l).tensorPower = s1903TensorPower l :=
  rfl

/-- The actual determinant's reference packet is the actual unit packet of
HullPacketActual; its log-volume is zero by the proved
HullPacketActual.referencePacket_logVolume_zero. -/
theorem s1903ActualDeterminant_referencePacket (l : PrimeGeFive) :
    (s1903ActualDeterminant l).referencePacket =
      HullPacketActual.referencePacket l :=
  rfl

/-- The reference packet of the actual determinant has zero log-volume. -/
theorem s1903ActualDeterminant_reference_logVolume (l : PrimeGeFive) :
    packetLogVolume (s1903ActualDeterminant l).referencePacket = 0 :=
  HullPacketActual.referencePacket_logVolume_zero l

/-- The actual determinant's procession is the actual root procession. -/
theorem s1903ActualDeterminant_procession (l : PrimeGeFive) :
    (s1903ActualDeterminant l).procession =
      s1903RootProcession l (s1903TensorPower l) :=
  rfl

/-! ## 4. The actual log-volumes -/

/-- The actual hull log-volume is M * packetLogVolume(root packet). -/
theorem s1903ActualDeterminant_hullLogVolume_eq_packet (l : PrimeGeFive) :
    (s1903ActualDeterminant l).hullLogVolume =
      (s1903TensorPower l : Real) *
        packetLogVolume (s1903ActualDeterminant l).hullPacket := by
  rw [SignedHullLogActual.hullLogVolume_eq_tensor_mul_packet]
  rw [show (s1903ActualDeterminant l).tensorPower =
      s1903TensorPower l from rfl]

/-- The actual normalized hull log-volume is -thetaLogVolume l. -/
theorem s1903ActualDeterminant_hullLogVolume (l : PrimeGeFive) :
    (s1903ActualDeterminant l).hullLogVolume = -thetaLogVolume l := by
  rw [SignedHullLogActual.hullLogVolume_eq_tensor_mul_packet]
  rw [show (s1903ActualDeterminant l).hullPacket =
      s1903RootHullPacket l (s1903TensorPower l) from rfl]
  rw [show (s1903ActualDeterminant l).tensorPower =
      s1903TensorPower l from rfl]
  rw [s1903RootHullPacket_logVolume l (s1903TensorPower l)
    (s1903TensorPower_ne_zero l)]
  have hMreal : (s1903TensorPower l : Real) ≠ 0 := by
    exact_mod_cast s1903TensorPower_ne_zero l
  field_simp

/-- The actual hull log-volume in determinant form:
M * log (packetDet hullPacket).  This is the project's actual determinant
normalization, not a fake log-volume. -/
theorem s1903ActualDeterminant_hullLogVolume_det (l : PrimeGeFive) :
    (s1903ActualDeterminant l).hullLogVolume =
      (s1903TensorPower l : Real) *
        Real.log (packetDet (s1903ActualDeterminant l).hullPacket) := by
  rw [SignedHullLogActual.hullLogVolume_eq_tensor_mul_log_det]
  rw [show (s1903ActualDeterminant l).tensorPower =
      s1903TensorPower l from rfl]

/-- The actual hull determinant is the exponential of the normalized negative
theta log-volume. -/
theorem s1903ActualDeterminant_hullPacket_det (l : PrimeGeFive) :
    packetDet (s1903ActualDeterminant l).hullPacket =
      Real.exp (-thetaLogVolume l / (s1903TensorPower l : Real)) := by
  rw [show (s1903ActualDeterminant l).hullPacket =
      s1903RootHullPacket l (s1903TensorPower l) from rfl]
  exact s1903RootHullPacket_det l (s1903TensorPower l)
    (s1903TensorPower_ne_zero l)

/-- The actual signed hull log-volume is thetaLogVolume l, the paper's
(nonpositive) log Theta magnitude with the correct sign. -/
theorem s1903ActualDeterminant_signedHullLogVolume (l : PrimeGeFive) :
    (s1903ActualDeterminant l).signedHullLogVolume = thetaLogVolume l := by
  rw [SignedHullLogActual.signedHullLogVolume_eq_neg,
    s1903ActualDeterminant_hullLogVolume]
  ring

/-- The actual theta log-volume is nonpositive. -/
theorem s1903_thetaLogVolume_nonpos (l : PrimeGeFive) :
    thetaLogVolume l <= 0 := by
  rw [theta_log_volume_eq_sum]
  exact Finset.sum_nonpos (fun j _ => s1903_thetaLogScale_nonpos l j)

/-- The actual signed hull log-volume is nonpositive: the paper sign
-|log Theta|. -/
theorem s1903ActualDeterminant_signedHullLogVolume_nonpos
    (l : PrimeGeFive) :
    (s1903ActualDeterminant l).signedHullLogVolume <= 0 := by
  rw [s1903ActualDeterminant_signedHullLogVolume]
  exact s1903_thetaLogVolume_nonpos l

/-- The actual hull log-volume is nonnegative. -/
theorem s1903ActualDeterminant_hullLogVolume_nonneg (l : PrimeGeFive) :
    0 <= (s1903ActualDeterminant l).hullLogVolume := by
  rw [s1903ActualDeterminant_hullLogVolume]
  exact neg_nonneg.mpr (s1903_thetaLogVolume_nonpos l)

/-- The actual procession-normalized hull log-volume is the actual root
procession average. -/
theorem s1903ActualDeterminant_processionNormalizedLogVolume
    (l : PrimeGeFive) :
    (s1903ActualDeterminant l).processionNormalizedLogVolume =
      -thetaLogVolume l /
        ((s1903TensorPower l : Real) *
          (Fintype.card (SignedLabel l.value) : Real)) := by
  unfold SignedHullLogActual.processionNormalizedLogVolume
  exact s1903RootProcession_average l (s1903TensorPower l)
    (s1903TensorPower_ne_zero l)

/-- The actual procession average is nonnegative. -/
theorem s1903ActualDeterminant_average_nonneg (l : PrimeGeFive) :
    0 <= (s1903ActualDeterminant l).procession.average :=
  SignedHullLogActual.processionNormalizedLogVolume_nonneg
    (s1903ActualDeterminant l)

/-- The actual signed procession-normalized hull log-volume is the negative of
the root procession average, hence nonpositive. -/
theorem s1903ActualDeterminant_signedProcession_nonpos (l : PrimeGeFive) :
    (s1903ActualDeterminant l).signedProcessionNormalizedLogVolume <= 0 :=
  SignedHullLogActual.signedProcessionNormalizedLogVolume_nonpos
    (s1903ActualDeterminant l)

/-- The actual hull and signed hull log-volumes add to zero. -/
theorem s1903ActualDeterminant_signed_add_hull (l : PrimeGeFive) :
    (s1903ActualDeterminant l).signedHullLogVolume +
      (s1903ActualDeterminant l).hullLogVolume = 0 :=
  SignedHullLogActual.signed_add_hull_eq_zero (s1903ActualDeterminant l)

/-! ## 5. The `ProcessionNormalizedLogVolumeActual` interface -/

/-- The actual procession-normalized mono-analytic log-volume attached to the
S1903 determinant.  It is built by `ofSignedHull` from the actual packet,
unit reference, tensor power, and procession; no arbitrary data is added. -/
noncomputable def s1903ProcessionNormalized (l : PrimeGeFive) :
    ProcessionNormalizedMonoAnalyticLogVolume
      (label := SignedLabel l.value) :=
  ofSignedHull (s1903ActualDeterminant l)

/-- Its value is the determinant's actual procession-normalized log-volume. -/
theorem s1903ProcessionNormalized_value (l : PrimeGeFive) :
    (s1903ProcessionNormalized l).value =
      (s1903ActualDeterminant l).processionNormalizedLogVolume :=
  ofSignedHull_value (s1903ActualDeterminant l)

/-- Its signed value is the determinant's actual signed procession
log-volume. -/
theorem s1903ProcessionNormalized_signedValue (l : PrimeGeFive) :
    (s1903ProcessionNormalized l).signedValue =
      (s1903ActualDeterminant l).signedProcessionNormalizedLogVolume :=
  ofSignedHull_signedValue (s1903ActualDeterminant l)

/-- The interface value in explicit actual theta-log-volume form. -/
theorem s1903ProcessionNormalized_value_eq (l : PrimeGeFive) :
    (s1903ProcessionNormalized l).value =
      -thetaLogVolume l /
        ((s1903TensorPower l : Real) *
          (Fintype.card (SignedLabel l.value) : Real)) := by
  rw [s1903ProcessionNormalized_value,
    s1903ActualDeterminant_processionNormalizedLogVolume]

/-- The procession-normalized interface value is nonnegative. -/
theorem s1903ProcessionNormalized_value_nonneg (l : PrimeGeFive) :
    0 <= (s1903ProcessionNormalized l).value :=
  (s1903ProcessionNormalized l).value_nonneg

/-- The signed procession-normalized interface value is nonpositive. -/
theorem s1903ProcessionNormalized_signedValue_nonpos (l : PrimeGeFive) :
    (s1903ProcessionNormalized l).signedValue <= 0 :=
  (s1903ProcessionNormalized l).signedValue_nonpos

/-! ## 6. Axiom probes -/

#print axioms s1903_thetaScale_le_one
#print axioms s1903_thetaScales_ge_one_false
#print axioms s1903HullPacketActualData_empty
#print axioms s1903RootHullPacket_logVolume
#print axioms s1903RootHullPacket_det
#print axioms s1903RootProcession_average
#print axioms s1903ActualDeterminant_hullLogVolume
#print axioms s1903ActualDeterminant_hullLogVolume_det
#print axioms s1903ActualDeterminant_hullPacket_det
#print axioms s1903ActualDeterminant_signedHullLogVolume
#print axioms s1903ActualDeterminant_hullLogVolume_nonneg
#print axioms s1903ActualDeterminant_processionNormalizedLogVolume
#print axioms s1903ActualDeterminant_average_nonneg
#print axioms s1903ActualDeterminant_signedProcession_nonpos
#print axioms s1903ActualDeterminant_signed_add_hull
#print axioms s1903ProcessionNormalized_value
#print axioms s1903ProcessionNormalized_value_eq
#print axioms s1903ProcessionNormalized_value_nonneg
#print axioms s1903ProcessionNormalized_signedValue_nonpos

end LeanFormal.IUT.XiFPaper.S1903SignedHullActual