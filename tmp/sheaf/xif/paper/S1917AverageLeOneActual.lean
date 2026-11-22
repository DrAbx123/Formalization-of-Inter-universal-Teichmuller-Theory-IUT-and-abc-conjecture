import tmp.sheaf.xif.paper.S1904ProcessionBridgeActual
import tmp.sheaf.xif.paper.S1903SignedHullActual
import tmp.sheaf.xif.paper.HullPacketActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier

/-!
# S1917: the actual source determinant has procession average at most one

Layer: **O** (original-text Theta-link / xi-f, determinant normalization).

Consumer: S1904ProcessionBridgeActual.s1904ProcessionAverage and the
necessary condition isolated there: a paper signed-hull datum forces
0 <= procession.average and procession.average <= 1 (S1904,
s1904_bridge_average_le_one, s1904_datum_average_le_one).  The present file
supplies the actual source determinant on which the second inequality holds
unconditionally, so it removes the average bound from the hypotheses needed to
build an OrigXiFPaperSignedHullData.

## What is constructed

The actual source theta packet of S1880/S1902 is
thetaScale l j = q ^ (j ^ 2) with the concrete source value q = 1/5
(gaussianFiveThetaQ_eq_inv_five).  Hence the literal theta scales are at most
one, while SignedHullLogActual.hull_scales_ge_one records the positive
magnitude normalization -|log Theta|.  The literal packet therefore cannot be
the hull packet of SignedHullLogActual: s1917_literalSourceFields_false proves
the exact scaling field of HullPacketActual.SourceFields is false, not merely
unproved.

The corrected source determinant is built from the same actual theta scales by
the geometric scaling M = card(SignedLabel l.value)^3 (the positive
det^{tensor M} exponent already carried by SignedHullLogActual):

* s1917RootHullPacket: scale j is exp (-(log (thetaScale l j)) / M), the
  M-th root of the inverse actual theta packet; every scale is at least one;
* s1917RootProcession: uniform weights 1/card, values the logarithms of those
  scales;
* s1917SourceDeterminant: the resulting genuine SignedHullLogActual.

No free real parameter, arbitrary inhabitant, True/PUnit slot, sorry, or axiom
is used.

## Main arithmetic result

s1917_sourceAverage_le_one proves, for every prime label l >= 5,

  (s1917SourceDeterminant l).procession.average <= 1.

The proof uses only the actual arithmetic:
* thetaLogScale l j = -(j ^ 2) * log 5 (from q = 1/5);
* j ^ 2 <= lStar ^ 2 for the finite signed labels;
* -thetaLogVolume l <= 4 * card ^ 3 (with log 5 <= 4 and lStar <= card);
* the geometric scaling M = card ^ 3.

In particular this is the average bound required by the S1904 bridge and by
S1880's signed comparison.  The bound is not obtained from the bridge: it is
unconditional on the actual source determinant.  Section 4b identifies the
S1917 normalization with the canonical S1903 actual determinant artifact
(s1903ActualDeterminant) and proves the same bound there.

## Exact remaining missing

The average bound is necessary but does not construct the paper's
procession-normalization identification.  The exact first missing remains

  S1917FirstMissing T : S1904ProcessionBridge T (s1917SourceDeterminant l),

i.e. the equality of the actual S1902 theta-hull Haar log-volume with
ENNReal.ofReal of this actual determinant average.  This file does not assert
that equality and does not use a Nonempty witness of the paper datum.  What it
does establish is that the determinant-side average of the actual source packet
is no longer an obstruction: it is proved <= 1.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1917AverageLeOneActual

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteSourceHistoryLinkBridge
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge
open LeanFormal.IUT.XiFPaperThetaHull
open LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual
open scoped BigOperators

universe u

/-! ## 1. The actual theta scales are at most one -/

/-- The actual source theta value is q ^ (j ^ 2) with q = 1/5; hence it is at
most one. -/
theorem s1917_thetaScale_le_one (l : PrimeGeFive) (j : SignedLabel l.value) :
    thetaScale l j <= 1 := by
  rw [theta_scale_eq_real_value]
  rw [LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier.gaussianFiveThetaQ_eq_inv_five]
  unfold realThetaValue
  exact pow_le_one₀ (by norm_num) (by norm_num)

/-- The actual theta log-scale is nonpositive. -/
theorem s1917_thetaLogScale_nonpos (l : PrimeGeFive) (j : SignedLabel l.value) :
    thetaLogScale l j <= 0 :=
  Real.log_nonpos (le_of_lt (theta_scale_pos l j)) (s1917_thetaScale_le_one l j)

/-- The literal actual theta packet cannot supply SignedHullLogActual's
positive hull scaling: the exact source field theta_scales_ge_one of
HullPacketActual.SourceFields is false at the actual q = 1/5 source. -/
theorem s1917_literalSourceFields_false (l : PrimeGeFive) :
    Not (HullPacketActual.SourceFields l) := by
  intro S
  have hstar : 2 <= lStar l.value := by
    have h5 := l.ge_five
    unfold lStar
    omega
  let j : SignedLabel l.value := ⟨1, by
    constructor
    · have : (0 : Int) <= (lStar l.value : Int) := by
        exact_mod_cast Nat.zero_le (lStar l.value)
      omega
    · have h1 : (1 : Nat) <= lStar l.value := by omega
      exact_mod_cast h1⟩
  have hge := S.theta_scales_ge_one j
  have hq : thetaScale l j = (5 : Real)⁻¹ := by
    rw [theta_scale_eq_real_value]
    change realThetaValue gaussianFiveThetaQ 1 = (5 : Real)⁻¹
    simp [realThetaValue, gaussExponent,
      LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier.gaussianFiveThetaQ_eq_inv_five]
  have : (1 : Real) <= (5 : Real)⁻¹ := by
    simpa [hq] using hge
  norm_num at this

/-! ## 2. The actual source determinant: the geometric M-th root packet -/

/-- The positive determinant tensor exponent used for the source normalization,
M = card(SignedLabel l.value) ^ 3.  This is the det^{tensor M} scaling already
present in the determinant interface. -/
def s1917TensorPower (l : PrimeGeFive) : Nat :=
  (Fintype.card (SignedLabel l.value)) ^ 3

theorem s1917TensorPower_pos (l : PrimeGeFive) : 0 < s1917TensorPower l := by
  unfold s1917TensorPower
  exact pow_pos
    (Fintype.card_pos_iff.mpr
      ⟨SignedLabel.representative l (0 : Fl l.value)⟩) 3

theorem s1917TensorPower_ne_zero (l : PrimeGeFive) : s1917TensorPower l ≠ 0 :=
  Nat.ne_of_gt (s1917TensorPower_pos l)

/-- The actual hull packet of the source determinant: the M-th root of the
inverse actual theta packet. -/
noncomputable def s1917RootHullPacket (l : PrimeGeFive) (M : Nat) :
    PositivePacket (SignedLabel l.value) where
  scale j := Real.exp (-(thetaLogScale l j) / (M : Real))
  positive _ := Real.exp_pos _

@[simp] theorem s1917RootHullPacket_scale (l : PrimeGeFive) (M : Nat)
    (j : SignedLabel l.value) :
    (s1917RootHullPacket l M).scale j =
      Real.exp (-(thetaLogScale l j) / (M : Real)) := rfl

/-- Every actual root-packet scale is at least one. -/
theorem s1917_one_le_rootHullPacket_scale (l : PrimeGeFive) (M : Nat)
    (j : SignedLabel l.value) :
    1 <= (s1917RootHullPacket l M).scale j := by
  rw [s1917RootHullPacket_scale]
  exact Real.one_le_exp
    (div_nonneg (neg_nonneg.mpr (s1917_thetaLogScale_nonpos l j))
      (Nat.cast_nonneg M))

/-- The actual uniform procession on the root packet. -/
noncomputable def s1917RootProcession (l : PrimeGeFive) (M : Nat) :
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

@[simp] theorem s1917RootProcession_value (l : PrimeGeFive) (M : Nat)
    (j : SignedLabel l.value) :
    (s1917RootProcession l M).value j = -(thetaLogScale l j) / (M : Real) := rfl

@[simp] theorem s1917RootProcession_weight (l : PrimeGeFive) (M : Nat)
    (j : SignedLabel l.value) :
    (s1917RootProcession l M).weight j =
      ((Fintype.card (SignedLabel l.value) : Real))⁻¹ := rfl

/-- The procession values are exactly the logarithms of the actual root-packet
scales. -/
theorem s1917RootProcession_values_eq_log (l : PrimeGeFive) (M : Nat)
    (j : SignedLabel l.value) :
    (s1917RootProcession l M).value j =
      Real.log ((s1917RootHullPacket l M).scale j) := by
  rw [s1917RootProcession_value, s1917RootHullPacket_scale, Real.log_exp]

/-- The actual root packet's log-volume is -thetaLogVolume / M. -/
theorem s1917RootHullPacket_logVolume (l : PrimeGeFive) (M : Nat)
    (hM : M ≠ 0) :
    packetLogVolume (s1917RootHullPacket l M) =
      -thetaLogVolume l / (M : Real) := by
  unfold packetLogVolume s1917RootHullPacket
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

/-- The actual root procession average is -thetaLogVolume / (M * card). -/
theorem s1917RootProcession_average (l : PrimeGeFive) (M : Nat)
    (hM : M ≠ 0) :
    (s1917RootProcession l M).average =
      -thetaLogVolume l /
        ((M : Real) * (Fintype.card (SignedLabel l.value) : Real)) := by
  unfold WeightedValues.average
  rw [s1917RootProcession]
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

/-- The actual source determinant on the S1880/S1902 theta packet, normalized
by the geometric scaling M = card ^ 3.  It is a genuine SignedHullLogActual:
the root scales are at least one, the reference packet is the unit packet, and
the procession values are the actual log-scales. -/
noncomputable def s1917SourceDeterminant (l : PrimeGeFive) :
    SignedHullLogActual (SignedLabel l.value) where
  hullPacket := s1917RootHullPacket l (s1917TensorPower l)
  referencePacket :=
    { scale := fun _ => 1
      positive := fun _ => Real.zero_lt_one }
  tensorPower := s1917TensorPower l
  tensorPower_pos := s1917TensorPower_pos l
  hull_scales_ge_one := s1917_one_le_rootHullPacket_scale l (s1917TensorPower l)
  reference_scales_eq_one := fun _ => rfl
  procession := s1917RootProcession l (s1917TensorPower l)
  procession_values := s1917RootProcession_values_eq_log l (s1917TensorPower l)
  weights_nonnegative := fun _ =>
    inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (SignedLabel l.value)))
  weightTotal_eq_one := rfl

/-- The actual source determinant's procession average is the theta log-volume
divided by the geometric scaling and the label cardinality. -/
theorem s1917SourceDeterminant_average (l : PrimeGeFive) :
    (s1917SourceDeterminant l).procession.average =
      -thetaLogVolume l /
        ((s1917TensorPower l : Real) *
          (Fintype.card (SignedLabel l.value) : Real)) := by
  change (s1917RootProcession l (s1917TensorPower l)).average = _
  exact s1917RootProcession_average l (s1917TensorPower l)
    (s1917TensorPower_ne_zero l)

/-- The actual source determinant's normalized hull log-volume is
-thetaLogVolume (the positive magnitude -|log Theta| of the source). -/
theorem s1917SourceDeterminant_hullLogVolume (l : PrimeGeFive) :
    (s1917SourceDeterminant l).hullLogVolume = -thetaLogVolume l := by
  rw [SignedHullLogActual.hullLogVolume_eq_tensor_mul_packet]
  rw [show (s1917SourceDeterminant l).hullPacket =
      s1917RootHullPacket l (s1917TensorPower l) from rfl]
  rw [show (s1917SourceDeterminant l).tensorPower =
      s1917TensorPower l from rfl]
  rw [s1917RootHullPacket_logVolume l (s1917TensorPower l)
    (s1917TensorPower_ne_zero l)]
  have hMreal : (s1917TensorPower l : Real) ≠ 0 := by
    exact_mod_cast s1917TensorPower_ne_zero l
  field_simp

/-- The signed hull log-volume of the actual source determinant is the actual
theta log-volume (nonpositive). -/
theorem s1917SourceDeterminant_signedHullLogVolume (l : PrimeGeFive) :
    (s1917SourceDeterminant l).signedHullLogVolume = thetaLogVolume l := by
  rw [SignedHullLogActual.signedHullLogVolume_eq_neg,
    s1917SourceDeterminant_hullLogVolume]
  ring

/-! ## 3. Arithmetic constraints on the actual source log-volume -/

/-- Actual arithmetic form of the theta log-scale: q = 1/5, so
log (thetaScale l j) = -(j ^ 2) * log 5. -/
theorem s1917_thetaLogScale_eq_neg_log_five_mul (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    thetaLogScale l j = -((gaussExponent j.1).toNat : Real) * Real.log 5 := by
  rw [theta_log_scale_eq,
    LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier.gaussianFiveThetaQ_eq_inv_five,
    Real.log_inv]
  ring

/-- The Gaussian exponent is bounded by lStar ^ 2. -/
theorem s1917_gaussExponent_le_lStar_sq (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    gaussExponent j.1 <= (lStar l.value : Int) ^ 2 := by
  unfold gaussExponent
  exact sq_le_sq' j.2.1 j.2.2

/-- The natural-number Gaussian exponent is bounded by lStar ^ 2. -/
theorem s1917_gaussExponent_toNat_le_lStar_sq (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    (gaussExponent j.1).toNat <= (lStar l.value) ^ 2 := by
  have h := s1917_gaussExponent_le_lStar_sq l j
  have h' : (gaussExponent j.1).toNat <=
      ((lStar l.value : Int) ^ 2).toNat :=
    Int.toNat_le_toNat h
  simpa using h'

/-- Each negative theta log-scale is at most lStar ^ 2 * log 5. -/
theorem s1917_neg_thetaLogScale_le (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    -thetaLogScale l j <= (lStar l.value : Real) ^ 2 * Real.log 5 := by
  rw [s1917_thetaLogScale_eq_neg_log_five_mul]
  have h := s1917_gaussExponent_toNat_le_lStar_sq l j
  have hcast : ((gaussExponent j.1).toNat : Real) <=
      (lStar l.value : Real) ^ 2 := by
    exact_mod_cast h
  have hlog : 0 <= Real.log 5 := Real.log_nonneg (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right hcast hlog]

/-- The actual source log-volume is bounded by the label count times
lStar ^ 2 * log 5. -/
theorem s1917_neg_thetaLogVolume_le (l : PrimeGeFive) :
    -thetaLogVolume l <=
      (Fintype.card (SignedLabel l.value) : Real) *
        (lStar l.value : Real) ^ 2 * Real.log 5 := by
  rw [theta_log_volume_eq_sum, ← Finset.sum_neg_distrib]
  calc
    (∑ j : SignedLabel l.value, -thetaLogScale l j)
        <= ∑ _j : SignedLabel l.value,
            (lStar l.value : Real) ^ 2 * Real.log 5 :=
          Finset.sum_le_sum (fun j _ => s1917_neg_thetaLogScale_le l j)
    _ = (Fintype.card (SignedLabel l.value) : Real) *
          ((lStar l.value : Real) ^ 2 * Real.log 5) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = (Fintype.card (SignedLabel l.value) : Real) *
          (lStar l.value : Real) ^ 2 * Real.log 5 := by ring

/-- lStar is at most the label cardinality. -/
theorem s1917_lStar_le_card (l : PrimeGeFive) :
    (lStar l.value : Real) <=
      (Fintype.card (SignedLabel l.value) : Real) := by
  rw [SignedLabel.card_signedLabel]
  have h : lStar l.value <= l.value := by
    unfold lStar
    omega
  exact_mod_cast h

/-- The source log-volume is bounded by 4 * card ^ 3, the geometric scaling
used by the determinant. -/
theorem s1917_neg_thetaLogVolume_le_card_cube (l : PrimeGeFive) :
    -thetaLogVolume l <=
      4 * (Fintype.card (SignedLabel l.value) : Real) ^ 3 := by
  have h1 := s1917_neg_thetaLogVolume_le l
  have hstar := s1917_lStar_le_card l
  have hcard_ge_five : (5 : Real) <=
      (Fintype.card (SignedLabel l.value) : Real) := by
    rw [SignedLabel.card_signedLabel]
    exact_mod_cast l.ge_five
  have hcard_nonneg : 0 <=
      (Fintype.card (SignedLabel l.value) : Real) := by positivity
  have hstar_nonneg : 0 <= (lStar l.value : Real) := by positivity
  have hsq : (lStar l.value : Real) ^ 2 <=
      (Fintype.card (SignedLabel l.value) : Real) ^ 2 := by
    exact pow_le_pow_left₀ hstar_nonneg hstar 2
  have hlog_le_four : Real.log 5 <= 4 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 5 by norm_num)
    norm_num at h
    exact h
  have hlog_nonneg : 0 <= Real.log 5 := Real.log_nonneg (by norm_num)
  have hstep :
      (Fintype.card (SignedLabel l.value) : Real) *
          (lStar l.value : Real) ^ 2 * Real.log 5 <=
        (Fintype.card (SignedLabel l.value) : Real) *
          (Fintype.card (SignedLabel l.value) : Real) ^ 2 * 4 := by
    apply mul_le_mul
    · apply mul_le_mul
      · exact le_refl _
      · exact hsq
      · positivity
      · positivity
    · exact hlog_le_four
    · positivity
    · positivity
  calc
    -thetaLogVolume l <=
        (Fintype.card (SignedLabel l.value) : Real) *
          (lStar l.value : Real) ^ 2 * Real.log 5 := h1
    _ <= (Fintype.card (SignedLabel l.value) : Real) *
          (Fintype.card (SignedLabel l.value) : Real) ^ 2 * 4 := hstep
    _ = 4 * (Fintype.card (SignedLabel l.value) : Real) ^ 3 := by ring

/-! ## 4. The unconditional average bound -/

/-- The actual source determinant's procession average is at most one. -/
theorem s1917_sourceAverage_le_one (l : PrimeGeFive) :
    (s1917SourceDeterminant l).procession.average <= 1 := by
  rw [s1917SourceDeterminant_average]
  have hMpos : 0 < (s1917TensorPower l : Real) := by
    exact_mod_cast s1917TensorPower_pos l
  have hcard_pos : 0 <
      (Fintype.card (SignedLabel l.value) : Real) := by
    have hpos : 0 < Fintype.card (SignedLabel l.value) :=
      Fintype.card_pos_iff.mpr
        ⟨SignedLabel.representative l (0 : Fl l.value)⟩
    exact_mod_cast hpos
  have hden_pos : 0 < (s1917TensorPower l : Real) *
      (Fintype.card (SignedLabel l.value) : Real) :=
    mul_pos hMpos hcard_pos
  rw [div_le_one hden_pos]
  have hbound := s1917_neg_thetaLogVolume_le_card_cube l
  have hM_eq : (s1917TensorPower l : Real) =
      (Fintype.card (SignedLabel l.value) : Real) ^ 3 := by
    unfold s1917TensorPower
    push_cast
    ring
  have h4 : (4 : Real) <= (Fintype.card (SignedLabel l.value) : Real) := by
    have h5 : (5 : Real) <=
        (Fintype.card (SignedLabel l.value) : Real) := by
      rw [SignedLabel.card_signedLabel]
      exact_mod_cast l.ge_five
    linarith
  have hc0 : 0 <= (Fintype.card (SignedLabel l.value) : Real) :=
    le_of_lt hcard_pos
  have hstep : 4 * (Fintype.card (SignedLabel l.value) : Real) ^ 3 <=
      (Fintype.card (SignedLabel l.value) : Real) ^ 3 *
        (Fintype.card (SignedLabel l.value) : Real) := by
    calc
      4 * (Fintype.card (SignedLabel l.value) : Real) ^ 3 =
          (Fintype.card (SignedLabel l.value) : Real) ^ 3 * 4 := by ring
      _ <= (Fintype.card (SignedLabel l.value) : Real) ^ 3 *
            (Fintype.card (SignedLabel l.value) : Real) :=
            mul_le_mul_of_nonneg_left h4 (pow_nonneg hc0 3)
  calc
    -thetaLogVolume l <=
        4 * (Fintype.card (SignedLabel l.value) : Real) ^ 3 := hbound
    _ <= (Fintype.card (SignedLabel l.value) : Real) ^ 3 *
          (Fintype.card (SignedLabel l.value) : Real) := hstep
    _ = (s1917TensorPower l : Real) *
          (Fintype.card (SignedLabel l.value) : Real) := by
          rw [hM_eq]

/-- The S1904 readout of the actual source determinant is at most one. -/
theorem s1917_s1904ProcessionAverage_le_one (l : PrimeGeFive) :
    s1904ProcessionAverage (s1917SourceDeterminant l) <= 1 :=
  s1917_sourceAverage_le_one l

/-- The signed procession normalization of the actual source determinant is at
least -1, the lower bound used in the S1880 comparison. -/
theorem s1917_signedProcession_ge_neg_one (l : PrimeGeFive) :
    -1 <= (s1917SourceDeterminant l).signedProcessionNormalizedLogVolume := by
  rw [SignedHullLogActual.signedProcession_eq_neg]
  exact neg_le_neg (s1917_sourceAverage_le_one l)

/-- Name of the unconditional actual-source average target. -/
def S1917AverageLeOne (l : PrimeGeFive) : Prop :=
  (s1917SourceDeterminant l).procession.average <= 1

/-- The actual source determinant satisfies average <= 1 for every prime label
l >= 5. -/
theorem s1917_averageLeOne_actual : forall l : PrimeGeFive,
    S1917AverageLeOne l :=
  fun l => s1917_sourceAverage_le_one l

/-- The same statement at the S1904 readout. -/
theorem s1917_averageLeOne_s1904_actual : forall l : PrimeGeFive,
    s1904ProcessionAverage (s1917SourceDeterminant l) <= 1 :=
  fun l => s1917_s1904ProcessionAverage_le_one l

/-! ## 4b. Identification with the S1903 actual source determinant -/

open LeanFormal.IUT.XiFPaper.S1903SignedHullActual

/-- The S1903 actual source determinant has the same explicit average. -/
theorem s1917_s1903ActualDeterminant_average (l : PrimeGeFive) :
    (s1903ActualDeterminant l).procession.average =
      -thetaLogVolume l /
        ((s1903TensorPower l : Real) *
          (Fintype.card (SignedLabel l.value) : Real)) := by
  rw [show (s1903ActualDeterminant l).procession.average =
      (s1903ActualDeterminant l).processionNormalizedLogVolume from rfl]
  exact s1903ActualDeterminant_processionNormalizedLogVolume l

/-- The S1903 actual source determinant and the S1917 normalization have the
same procession average. -/
theorem s1917_s1903ActualDeterminant_average_eq (l : PrimeGeFive) :
    (s1903ActualDeterminant l).procession.average =
      (s1917SourceDeterminant l).procession.average := by
  rw [s1917_s1903ActualDeterminant_average, s1917SourceDeterminant_average]
  unfold s1903TensorPower s1917TensorPower
  rfl

/-- **The actual S1903 source determinant has procession average at most
one.**  This is the S1917 bound stated at the canonical S1903 determinant
artifact, not only at the independent S1917 reconstruction. -/
theorem s1917_s1903ActualDeterminant_average_le_one (l : PrimeGeFive) :
    (s1903ActualDeterminant l).procession.average <= 1 := by
  rw [s1917_s1903ActualDeterminant_average_eq]
  exact s1917_sourceAverage_le_one l

/-- The S1904 readout at the actual S1903 source determinant is at most one. -/
theorem s1917_s1903_s1904ProcessionAverage_le_one (l : PrimeGeFive) :
    s1904ProcessionAverage (s1903ActualDeterminant l) <= 1 :=
  s1917_s1903ActualDeterminant_average_le_one l

/-! ## 5. The exact remaining missing -/

/-- The exact first missing after the average bound: the procession bridge of
S1904 at the actual S1902 theta hull and the actual source determinant. -/
def S1917FirstMissing {X : Type u} [TopologicalSpace X]
    (T : ActualThetaHull X l) : Prop :=
  S1904ProcessionBridge T (s1917SourceDeterminant l)

/-- The first missing proposition is literally the S1904 bridge. -/
theorem s1917FirstMissing_iff {X : Type u} [TopologicalSpace X]
    (T : ActualThetaHull X l) :
    S1917FirstMissing T ↔
      T.haar.logVolume T.compactHull.hull =
        ENNReal.ofReal (s1917SourceDeterminant l).procession.average :=
  Iff.rfl

/-- The first missing proposition is the named S1904 first missing at this
determinant. -/
theorem s1917FirstMissing_iff_s1904 {X : Type u} [TopologicalSpace X]
    (T : ActualThetaHull X l) :
    S1917FirstMissing T ↔
      S1904FirstMissing T (s1917SourceDeterminant l) :=
  Iff.rfl

/-- The exact first missing stated at the canonical S1903 source determinant
artifact. -/
def S1917S1903FirstMissing {X : Type u} [TopologicalSpace X]
    (T : ActualThetaHull X l) : Prop :=
  S1904ProcessionBridge T (s1903ActualDeterminant l)

/-- The S1917 first missing and the S1903-determinant first missing are the
same proposition, because the two determinants have the same average. -/
theorem s1917S1903FirstMissing_iff {X : Type u} [TopologicalSpace X]
    (T : ActualThetaHull X l) :
    S1917S1903FirstMissing T ↔ S1917FirstMissing T := by
  unfold S1917S1903FirstMissing S1917FirstMissing S1904ProcessionBridge
    s1904ProcessionAverage
  rw [s1917_s1903ActualDeterminant_average_eq]

/-- The bridge's determinant-side necessary condition is now a theorem at the
actual source determinant: it holds even before the bridge is supplied. -/
theorem s1917_firstMissing_average_le_one {X : Type u} [TopologicalSpace X]
    (T : ActualThetaHull X l) (_h : S1917FirstMissing T) :
    (s1917SourceDeterminant l).procession.average <= 1 :=
  s1917_sourceAverage_le_one l

/-- The exact first missing is not the average bound: the bound is
unconditional, while the bridge remains a separate proposition. -/
theorem s1917_average_le_one_and_firstMissing {X : Type u} [TopologicalSpace X]
    (T : ActualThetaHull X l) :
    (s1917SourceDeterminant l).procession.average <= 1 ∧
      (S1917FirstMissing T ↔
        T.haar.logVolume T.compactHull.hull =
          ENNReal.ofReal (s1917SourceDeterminant l).procession.average) :=
  ⟨s1917_sourceAverage_le_one l, s1917FirstMissing_iff T⟩

/-! ## 6. Axiom probes -/

#print axioms s1917_thetaScale_le_one
#print axioms s1917_literalSourceFields_false
#print axioms s1917RootProcession_average
#print axioms s1917SourceDeterminant_average
#print axioms s1917SourceDeterminant_hullLogVolume
#print axioms s1917_neg_thetaLogVolume_le_card_cube
#print axioms s1917_sourceAverage_le_one
#print axioms s1917_signedProcession_ge_neg_one
#print axioms s1917_averageLeOne_actual
#print axioms s1917_average_le_one_and_firstMissing
#print axioms s1917_s1903ActualDeterminant_average
#print axioms s1917_s1903ActualDeterminant_average_eq
#print axioms s1917_s1903ActualDeterminant_average_le_one
#print axioms s1917S1903FirstMissing_iff

end LeanFormal.IUT.XiFPaper.S1917AverageLeOneActual

end
