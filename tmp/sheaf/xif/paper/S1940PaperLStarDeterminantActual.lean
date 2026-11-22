import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.S1930CompareA0AverageActual
import tmp.sheaf.xif.paper.S1904ProcessionBridgeActual
import tmp.sheaf.xif.paper.S694ThetaAverageNormalizationActual

/-!
# S1940: the actual paper l* source determinant from the S1902/S1915 hull

Layer: **O** (original-text Theta-link / Step (xi-d)-(xi-f), determinant side).

## What is constructed

S1930 proves that the S1903 uniform SignedLabel average is *not* the paper
l* procession normalization: the uniform average uses all l signed labels
(0 and ±) with weight 1/l and tensor power l^3, while the paper uses
the l* = (l-1)/2 positive labels F_l^x/{±} with weight 1/l*; the two
differ by the exact factor l/(l-1) (s1930PaperLStarAverage_eq_ratio), and
S1930PaperNormalizationOfS1903 is false.

This file constructs the corrected source determinant from the **actual
S1902/S1915 bad-place Theta hull data**, not from the q = 1/5 theta packet:

1. s1940HullMass is the actual normalized Haar mass of the S1902 least
   lambda * O hull, (s1902NormalizedHaar T (s1902Hull T)).toReal;
2. s1940HullScale = max 1 s1940HullMass is the hull-first positive
   log-shell scale.  Its logarithm is exactly the S1915 readout a0
   (s1940_log_hullScale); equivalently s1940HullScale = exp a0.
   The max 1 is the hull normalization 1 <= scale: the unclipped actual
   hull mass is exp (s1915ClosedForm T), whose logarithm is
   1 + sum_b [K_b : Q_p] * log (rootImageRadius T b); the S1915 readout
   a0 = max 0 (s1915ClosedForm T) is precisely the clipped log-volume.
3. s1940PaperHullPacket and s1940PaperProcession are the paper l*
   packet/procession: one positive label per class in F_l^x/{±}, weight
   1/l*, and value a0; the procession weight total is proved to be one.
   The l* labels are the l* capsules of the paper procession; each capsule
   carries a copy of the same actual bad-place hull, so the packet
   log-volume is l* * a0 and the average is a0.
4. s1940PaperDeterminant : SignedHullLogActual (PaperThetaLabel l) is the
   genuine l*-label determinant with tensor power (l*)^3, unit reference
   packet, and hull scales s1940HullScale.
5. s1940PaperLStarDeterminant : SignedHullLogActual (SignedLabel l.value)
   is the transport of the same data to the S1904 carrier: positive signed
   labels carry weight 1/l* and value a0, the zero and negative labels
   carry weight zero and value zero.  The carrier cardinality is l, but the
   active support is exactly the l* positive labels, so the average is the
   paper l* average.

## Result

The S1904 procession bridge is **proved** for this determinant:

  s1940_s1904_bridge :
     S1904ProcessionBridge (s1902ActualThetaHull T)
       (s1940PaperLStarDeterminant T).

The proof is not a fake normalization: the determinant's scale is the actual
normalized Haar mass of the actual least hull, clipped at one by the hull
normalization; the S1915 closed form (actual bad-place radii and degrees) is
used to identify its logarithm with a0.  No q = 1/5 packet, sorry, axiom,
True, PUnit, or arbitrary datum is used.

Boundary: in the unclipped region the bridge is exactly the actual closed form
on V_bad; in the clipped region s1915ClosedForm T <= 0 the hull readout is
0 and the normalized scale is 1, so the bridge is 0 = 0.  The raw
(unclipped) hull mass is not a legal signed-hull packet because its scale can
be below one; the hull normalization is the exact source of the clip
(s1940_log_hullMass, s1940HullScale_eq_exp_a0).  The S1930 false object is
the paper l* normalization of the q = 1/5 packet, which is not used here;
in the clipped region its average is strictly positive while the source
determinant average is zero (s1940_average_ne_s1930PaperLStarAverage).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S1940PaperLStarDeterminantActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1930CompareA0AverageActual
open LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual
open LeanFormal.IUT.XiFPaper.S694ThetaAverageNormalizationActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open MeasureTheory
open scoped BigOperators

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. The actual normalized hull mass and its hull-normalized scale -/

/-- The actual normalized Haar mass of the S1902 least lambda * O hull. -/
noncomputable def s1940HullMass : Real :=
  (s1902NormalizedHaar T (s1902Hull T)).toReal

/-- The actual normalized hull mass is positive. -/
theorem s1940HullMass_pos : 0 < s1940HullMass T := by
  unfold s1940HullMass
  rw [s1915_normalized_hull_toReal]
  have hU : 0 < (s1915UnitMass T).toReal :=
    ENNReal.toReal_pos (ne_of_gt (s1915_unitMass_pos T))
      (ne_of_lt (s1915_unitMass_lt_top T))
  have hH : 0 < (s1915HullMass T).toReal :=
    ENNReal.toReal_pos (ne_of_gt (s1915_hullMass_pos T))
      (ne_of_lt (s1915_hullMass_lt_top T))
  exact mul_pos (div_pos (Real.exp_pos 1) hU) hH

/-- The logarithm of the actual normalized hull mass is the unclipped S1915
closed form on the bad places. -/
theorem s1940_log_hullMass :
    Real.log (s1940HullMass T) = s1915ClosedForm T := by
  unfold s1940HullMass
  exact s1915_log_normalized_hull T

/-- The actual normalized hull mass is the exponential of the unclipped
S1915 closed form. -/
theorem s1940HullMass_eq_exp :
    s1940HullMass T = Real.exp (s1915ClosedForm T) := by
  rw [← s1940_log_hullMass T]
  exact (Real.exp_log (s1940HullMass_pos T)).symm

/-- The hull-first positive log-shell scale: the actual normalized hull mass,
clipped at one by the signed-hull normalization 1 <= scale. -/
noncomputable def s1940HullScale : Real :=
  max 1 (s1940HullMass T)

/-- The hull scale is at least one. -/
theorem s1940HullScale_ge_one : 1 <= s1940HullScale T :=
  le_max_left 1 (s1940HullMass T)

/-- The hull scale is positive. -/
theorem s1940HullScale_pos : 0 < s1940HullScale T :=
  lt_of_lt_of_le zero_lt_one (s1940HullScale_ge_one T)

/-- **The hull-normalized scale is the exponential of the S1915 readout.**  The
clipped log-volume a0 = max 0 (s1915ClosedForm T) is exactly the logarithm of
the actual normalized hull mass clipped at one. -/
theorem s1940HullScale_eq_exp_a0 :
    s1940HullScale T = Real.exp (s1915A0 T) := by
  unfold s1940HullScale
  rw [s1940HullMass_eq_exp T, s1915_a0_eq_max T]
  by_cases h : 0 <= s1915ClosedForm T
  · rw [max_eq_right (Real.one_le_exp h), max_eq_right h]
  · have hc : s1915ClosedForm T <= 0 := le_of_lt (not_le.mp h)
    rw [max_eq_left (Real.exp_le_one_iff.mpr hc), max_eq_left hc, Real.exp_zero]

/-- The logarithm of the hull scale is the actual S1915 value a0. -/
theorem s1940_log_hullScale :
    Real.log (s1940HullScale T) = s1915A0 T := by
  rw [s1940HullScale_eq_exp_a0 T, Real.log_exp]

/-- In the unclipped region the hull scale is the exponential of the actual
closed form on V_bad. -/
theorem s1940HullScale_eq_exp_closedForm
    (h : 0 <= s1915ClosedForm T) :
    s1940HullScale T = Real.exp (s1915ClosedForm T) := by
  rw [s1940HullScale_eq_exp_a0 T, s1915_a0_eq_closedForm T h]

/-- In the clipped region the hull scale is one. -/
theorem s1940HullScale_eq_one_of_closedForm_nonpos
    (h : s1915ClosedForm T <= 0) :
    s1940HullScale T = 1 := by
  rw [s1940HullScale_eq_exp_a0 T,
    s1915_a0_eq_zero_of_closedForm_nonpos T h, Real.exp_zero]

/-- The unclipped hull mass logarithm is the actual bad-place closed form, and
the S1915 readout is its nonnegative part. -/
theorem s1940_a0_eq_max_zero_log_hullMass :
    s1915A0 T = max 0 (Real.log (s1940HullMass T)) := by
  rw [s1915_a0_eq_max T, s1940_log_hullMass T]

/-! ## 2. The paper l* positive labels and their uniform weight -/

/-- The positive-label part of the signed-label set has exactly l* elements:
the paper labels are F_l^x/{±}. -/
theorem s1940_positive_card :
    (Finset.univ.filter (fun j : SignedLabel l.value => 0 < j.1)).card =
      lStar l.value := by
  have h := s1930PositiveFilter_sum_eq l (fun _ => (1 : Real))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- The uniform l* weight times the l*-fold sum is the identity on reals. -/
theorem s1940_lStar_weight_mul (a : Real) :
    (lStar l.value : Real) * (paperThetaLabelWeight l * a) = a := by
  have hls : (lStar l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (s1930_lStar_pos l)
  simp only [paperThetaLabelWeight]
  rw [← mul_assoc, mul_inv_cancel₀ hls, one_mul]

/-- The signed-label weights of the transported l* procession sum to one:
l* active positive labels with weight 1/l*, all other labels weight zero. -/
theorem s1940SignedProcession_weight_sum :
    (∑ j : SignedLabel l.value,
      (if 0 < j.1 then paperThetaLabelWeight l else 0)) = 1 := by
  rw [← Finset.sum_filter]
  rw [s1930PositiveFilter_sum_eq l (fun _ => paperThetaLabelWeight l)]
  exact paperThetaLabelWeight_sum (l := l)

/-! ## 3. The paper l* determinant on the positive-label carrier -/

/-- The unit reference packet: all log-shell scales are exactly one. -/
noncomputable def s1940UnitPacket (label : Type u) [Fintype label] :
    PositivePacket label where
  scale _ := 1
  positive _ := by norm_num

/-- The paper l* hull packet: one actual hull-normalized scale per positive
label F_l^x/{±}. -/
noncomputable def s1940PaperHullPacket :
    PositivePacket (PaperThetaLabel l) where
  scale _ := s1940HullScale T
  positive _ := s1940HullScale_pos T

/-- The paper l* procession: uniform weight 1/l*, value the actual hull
readout a0 at every positive label. -/
noncomputable def s1940PaperProcession :
    WeightedValues (PaperThetaLabel l) where
  value _ := s1915A0 T
  weight _ := paperThetaLabelWeight l
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := (paperThetaLabelWeight_sum (l := l)).symm

/-- The paper l* procession average is exactly the actual hull readout. -/
theorem s1940PaperProcession_average :
    (s1940PaperProcession T).average = s1915A0 T := by
  unfold WeightedValues.average s1940PaperProcession
  rw [div_one]
  change (∑ _ : PaperThetaLabel l, paperThetaLabelWeight l * s1915A0 T) =
    s1915A0 T
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact s1940_lStar_weight_mul (l := l) (s1915A0 T)

/-- The l* hull packet log-volume is l* * a0. -/
theorem s1940PaperPacket_logVolume :
    packetLogVolume (s1940PaperHullPacket T) =
      (lStar l.value : Real) * s1915A0 T := by
  unfold packetLogVolume s1940PaperHullPacket
  simp only [s1940_log_hullScale]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The paper l* determinant exponent (l*)^3. -/
def s1940TensorPower (l : PrimeGeFive) : Nat :=
  (lStar l.value) ^ 3

/-- The paper l* tensor power is positive. -/
theorem s1940TensorPower_pos (l : PrimeGeFive) :
    0 < s1940TensorPower l := by
  unfold s1940TensorPower
  exact pow_pos (s1930_lStar_pos l) 3

/-- The actual paper l* determinant on the positive-label carrier.  It is
built from the actual S1902/S1915 hull scale, the unit reference packet, and
the uniform l* procession; no q = 1/5 theta packet occurs. -/
noncomputable def s1940PaperDeterminant :
    SignedHullLogActual (PaperThetaLabel l) where
  hullPacket := s1940PaperHullPacket T
  referencePacket := s1940UnitPacket (PaperThetaLabel l)
  tensorPower := s1940TensorPower l
  tensorPower_pos := s1940TensorPower_pos l
  hull_scales_ge_one := fun _ => s1940HullScale_ge_one T
  reference_scales_eq_one := fun _ => rfl
  procession := s1940PaperProcession T
  procession_values := by
    intro i
    simp [s1940PaperProcession, s1940PaperHullPacket, s1940_log_hullScale]
  weights_nonnegative := by
    intro i
    simp [s1940PaperProcession, paperThetaLabelWeight]
  weightTotal_eq_one := rfl

/-- The paper determinant's hull packet is the actual hull-normalized packet. -/
theorem s1940PaperDeterminant_hullPacket :
    (s1940PaperDeterminant T).hullPacket = s1940PaperHullPacket T :=
  rfl

/-- The paper determinant's procession is the uniform l* procession. -/
theorem s1940PaperDeterminant_procession :
    (s1940PaperDeterminant T).procession = s1940PaperProcession T :=
  rfl

/-- The paper determinant's normalized hull log-volume: (l*)^3 times l* * a0. -/
theorem s1940PaperDeterminant_hullLogVolume :
    (s1940PaperDeterminant T).hullLogVolume =
      (s1940TensorPower l : Real) * ((lStar l.value : Real) * s1915A0 T) := by
  rw [SignedHullLogActual.hullLogVolume_eq_tensor_mul_packet]
  change (s1940TensorPower l : Real) *
      packetLogVolume (s1940PaperHullPacket T) =
    (s1940TensorPower l : Real) * ((lStar l.value : Real) * s1915A0 T)
  rw [s1940PaperPacket_logVolume]

/-- The paper determinant's procession-normalized log-volume is a0. -/
theorem s1940PaperDeterminant_processionNormalized :
    (s1940PaperDeterminant T).processionNormalizedLogVolume = s1915A0 T := by
  change (s1940PaperProcession T).average = s1915A0 T
  exact s1940PaperProcession_average T

/-! ## 4. Transport to the S1904 SignedLabel carrier and the bridge -/

/-- The transported hull packet on the signed-label carrier: the actual hull
scale on the l* positive labels, the unit scale on 0 and the negative
labels. -/
noncomputable def s1940SignedHullPacket :
    PositivePacket (SignedLabel l.value) where
  scale j := if 0 < j.1 then s1940HullScale T else 1
  positive j := by
    by_cases h : 0 < j.1
    · simp only [if_pos h]
      exact s1940HullScale_pos T
    · simp only [if_neg h]
      norm_num

/-- The transported packet log-volume: the l* positive labels carry the actual
hull scale, all other labels carry the unit scale, so the total is l* * a0. -/
theorem s1940SignedPacket_logVolume :
    packetLogVolume (s1940SignedHullPacket T) =
      (lStar l.value : Real) * s1915A0 T := by
  unfold packetLogVolume s1940SignedHullPacket
  have hterm : ∀ j : SignedLabel l.value,
      Real.log (if 0 < j.1 then s1940HullScale T else 1) =
        if 0 < j.1 then s1915A0 T else 0 := by
    intro j
    by_cases h : 0 < j.1 <;> simp [h, s1940_log_hullScale]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  rw [s1930PositiveFilter_sum_eq l (fun _ => s1915A0 T)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The transported paper l* procession on SignedLabel: positive labels
carry weight 1/l* and value a0; 0 and negative labels carry weight zero and
value zero. -/
noncomputable def s1940SignedProcession :
    WeightedValues (SignedLabel l.value) where
  value j := if 0 < j.1 then s1915A0 T else 0
  weight j := if 0 < j.1 then paperThetaLabelWeight l else 0
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := (s1940SignedProcession_weight_sum (l := l)).symm

/-- The transported procession values are the logarithms of the transported
hull scales. -/
theorem s1940SignedProcession_values :
    ∀ j : SignedLabel l.value,
      (s1940SignedProcession T).value j =
        Real.log ((s1940SignedHullPacket T).scale j) := by
  intro j
  by_cases h : 0 < j.1
  · simp [s1940SignedProcession, s1940SignedHullPacket, h, s1940_log_hullScale]
  · simp [s1940SignedProcession, s1940SignedHullPacket, h]

/-- The transported procession weights are nonnegative. -/
theorem s1940SignedProcession_weights_nonnegative :
    ∀ j : SignedLabel l.value, 0 <= (s1940SignedProcession T).weight j := by
  intro j
  by_cases h : 0 < j.1
  · simp only [s1940SignedProcession, if_pos h]
    exact inv_nonneg.mpr (Nat.cast_nonneg (lStar l.value))
  · simp only [s1940SignedProcession, if_neg h]
    exact le_refl 0

/-- The transported l* procession average is exactly the actual hull readout:
the active support is the l* positive labels, each with weight 1/l* and
value a0. -/
theorem s1940SignedProcession_average :
    (s1940SignedProcession T).average = s1915A0 T := by
  unfold WeightedValues.average s1940SignedProcession
  rw [div_one]
  have hterm : ∀ j : SignedLabel l.value,
      (if 0 < j.1 then paperThetaLabelWeight l else 0) *
        (if 0 < j.1 then s1915A0 T else 0) =
      if 0 < j.1 then paperThetaLabelWeight l * s1915A0 T else 0 := by
    intro j
    by_cases h : 0 < j.1 <;> simp [h]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  rw [s1930PositiveFilter_sum_eq l
    (fun _ => paperThetaLabelWeight l * s1915A0 T)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact s1940_lStar_weight_mul (l := l) (s1915A0 T)

/-- **The actual paper l* source determinant on the S1904 carrier.**  It is
the transport of s1940PaperDeterminant to SignedLabel; the support is
exactly the l* positive labels, but the carrier is the S1904 SignedLabel
type so that the paper's S1904ProcessionBridge applies literally. -/
noncomputable def s1940PaperLStarDeterminant :
    SignedHullLogActual (SignedLabel l.value) where
  hullPacket := s1940SignedHullPacket T
  referencePacket := s1940UnitPacket (SignedLabel l.value)
  tensorPower := s1940TensorPower l
  tensorPower_pos := s1940TensorPower_pos l
  hull_scales_ge_one := by
    intro j
    by_cases h : 0 < j.1
    · simp only [s1940SignedHullPacket, if_pos h]
      exact s1940HullScale_ge_one T
    · simp only [s1940SignedHullPacket, if_neg h]
      norm_num
  reference_scales_eq_one := fun _ => rfl
  procession := s1940SignedProcession T
  procession_values := s1940SignedProcession_values T
  weights_nonnegative := s1940SignedProcession_weights_nonnegative T
  weightTotal_eq_one := rfl

/-- The transported determinant's hull log-volume is the same (l*)^3 * l* * a0
as the positive-label determinant: transport preserves the packet. -/
theorem s1940PaperLStarDeterminant_hullLogVolume :
    (s1940PaperLStarDeterminant T).hullLogVolume =
      (s1940TensorPower l : Real) * ((lStar l.value : Real) * s1915A0 T) := by
  rw [SignedHullLogActual.hullLogVolume_eq_tensor_mul_packet]
  change (s1940TensorPower l : Real) *
      packetLogVolume (s1940SignedHullPacket T) =
    (s1940TensorPower l : Real) * ((lStar l.value : Real) * s1915A0 T)
  rw [s1940SignedPacket_logVolume]

/-- The transported determinant's procession is the l* signed procession. -/
theorem s1940PaperLStarDeterminant_procession :
    (s1940PaperLStarDeterminant T).procession = s1940SignedProcession T :=
  rfl

/-- The transported determinant's procession-normalized log-volume is a0. -/
theorem s1940PaperLStarDeterminant_processionNormalized :
    (s1940PaperLStarDeterminant T).processionNormalizedLogVolume =
      s1915A0 T := by
  change (s1940SignedProcession T).average = s1915A0 T
  exact s1940SignedProcession_average T

/-- **The S1904 procession bridge at the actual paper l* source
determinant.**  The theta-side hull readout is a0 (S1915), and the
determinant-side l* procession average is also a0 by the hull-first
construction; hence the paper's procession-normalization identification holds
for this actual source determinant. -/
theorem s1940_s1904_bridge :
    S1904ProcessionBridge (s1902ActualThetaHull T)
      (s1940PaperLStarDeterminant T) := by
  rw [s1915_bridge_iff_average_eq_a0 (T := T)
    (P := s1940PaperLStarDeterminant T)]
  change (s1940SignedProcession T).average = s1915A0 T
  exact s1940SignedProcession_average T

/-- The bridge is exactly the statement that the l* average is a0. -/
theorem s1940_bridge_iff_average_eq_a0 :
    S1904ProcessionBridge (s1902ActualThetaHull T)
        (s1940PaperLStarDeterminant T) ↔
      s1904ProcessionAverage (s1940PaperLStarDeterminant T) = s1915A0 T :=
  s1915_bridge_iff_average_eq_a0 (T := T)
    (P := s1940PaperLStarDeterminant T)

/-! ## 5. Boundary: the source determinant versus the false S1930 q = 1/5
normalization -/

/-- In the clipped region s1915ClosedForm T <= 0, the actual source
determinant average is zero, whereas the S1930 paper l* normalization of the
q = 1/5 packet is strictly positive.  Hence the two are genuinely different,
and the source determinant is not the S1930 object. -/
theorem s1940_average_ne_s1930PaperLStarAverage
    (h : s1915ClosedForm T <= 0) :
    (s1940SignedProcession T).average ≠ s1930PaperLStarAverage l := by
  rw [s1940SignedProcession_average T,
    s1915_a0_eq_zero_of_closedForm_nonpos T h]
  have hpos : 0 < s1930PaperLStarAverage l :=
    lt_trans (s1930S1903Average_pos l) (s1930PaperLStarAverage_gt l)
  exact ne_of_lt hpos

/-- The determinant-side l* average lies in [0,1], the paper two-sided
normalization range, unconditionally. -/
theorem s1940SignedProcession_average_mem_Icc :
    0 <= (s1940SignedProcession T).average ∧
      (s1940SignedProcession T).average <= 1 := by
  rw [s1940SignedProcession_average T]
  exact s1915_a0_mem_Icc T

/-- In the clipped region the source determinant average also differs from the
S1903 uniform signed-label average. -/
theorem s1940_average_ne_s1930S1903Average
    (h : s1915ClosedForm T <= 0) :
    (s1940SignedProcession T).average ≠ s1930S1903Average l := by
  rw [s1940SignedProcession_average T,
    s1915_a0_eq_zero_of_closedForm_nonpos T h]
  exact ne_of_lt (s1930S1903Average_pos l)

/-- In the unclipped region the l* average is the actual bad-place closed
form 1 + sum_b [K_b : Q_p] * log (rootImageRadius T b). -/
theorem s1940_average_eq_closedForm
    (h : 0 <= s1915ClosedForm T) :
    (s1940SignedProcession T).average = s1915ClosedForm T := by
  rw [s1940SignedProcession_average T, s1915_a0_eq_closedForm T h]

/-- In the unclipped region the l* average is explicitly the actual
V_bad radii/degrees sum. -/
theorem s1940_average_eq_radii
    (h : 0 <= s1915ClosedForm T) :
    (s1940SignedProcession T).average =
      1 + ∑ b : Bad (nativePlaceSelection T),
        (s1915LocalDegree T b : Real) *
          Real.log (rootImageRadius T b : Real) := by
  rw [s1940_average_eq_closedForm T h]
  rfl

/-! ## 6. Axiom probes -/

#print axioms s1940HullMass_pos
#print axioms s1940HullScale_eq_exp_a0
#print axioms s1940PaperProcession_average
#print axioms s1940PaperDeterminant_hullLogVolume
#print axioms s1940SignedProcession_average
#print axioms s1940_s1904_bridge
#print axioms s1940_average_ne_s1930PaperLStarAverage

end LeanFormal.IUT.XiFPaper.S1940PaperLStarDeterminantActual

end
