import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import LeanFormal.IUT.ABCBridge.Geometry.ABCModelHeightComparison

/-!
# Both comparison clauses at the realized arithmetic-line-bundle carrier

This file assembles the per-`epsilon` comparison data
`Cor312EpsilonArithmeticComparisonAdditive` (`Cor312ToABCBridgeInterface.lean:319`)
at the realized carrier whose point datum is the procession-normalized log-volume
`(1/6) log q` of the arithmetic line bundle, and feeds it to the production
consumer `abcHeightWeightAdditiveBoundV2_of_epsilonComparisonAdditive`
(`Cor312ToABCBridgeInterface.lean:348`).

## Realized objects

* `log q = Height.logHeight₁ (abcJInvariant a b c)`: the actual rational Frey
  `j`-invariant log-height (IUT IV:1302-1362; on the bad support `q = j^{-1}`,
  `ABCModelHeightComparison.lean:257-264`).
* point datum `qPilotDisplayPoint a b c = (1/6) log q + c0`, where
  `c0 = -log(27/64)/6 = log(64/27)/6` is the bounded-discrepancy normalization from
  the actual Frey model comparison `6·ht(x) + log(27/64) <= log q`
  (`abcJInvariant_logHeight_bounds_abcRationalPoint`).
* carrier `realLineHullData` (`Cor312ToABCBridgeInterface.lean:521`): real line of
  normalized log-volumes, unit region/hull `{0}`, identity scaling, sup-of-degrees
  log-volume.  The region volume of the point datum is therefore exactly its value.

## What is proved

* F4 (additive form, `A = 0`): from `6·ht(x) + log(27/64) <= log q` we get
  `ht(x) <= (1/6) log q + c0`, hence `ht(x) <= (1 + eps)·(region volume)` because
  the realized log-volume is nonnegative.
* F5: from the section-2 display family
  `(1/6) log q <= (1 + 20 d_mod/l)·weight + 20(e*_mod l + eta)` (IUT IV Theorem
  1.10, `:1376-1385`; the exact shape named `IUTIVSection2UniformDisplayFamily`),
  with `20 d_mod/l <= eps`, the region volume is bounded by
  `(1 + eps)·weight + D` with `D = 20(e*_mod l + eta) + c0`.
* `s3135_ABCHeightWeightAdditiveBoundV2_of_displayFamily`: the assembled family
  yields the version-2 additive height/weight contract through the production
  consumer.

The single named input is `IUTIVSection2UniformDisplayFamily` — the section-2
uniform form of the IUT IV Theorem 1.10 display at the arithmetic-weight dictionary.
It is not proved here and is exposed, not hidden.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3135ComparisonAssemblyActual

/-- The realized `log q` of IUT IV:1302-1362: the logarithmic height of the actual
rational Frey `j`-invariant. -/
noncomputable def freyLogQ (a b c : ℕ) : ℝ :=
  Height.logHeight₁ (abcJInvariant a b c)

theorem freyLogQ_nonneg (a b c : ℕ) : 0 ≤ freyLogQ a b c :=
  Height.zero_le_logHeight₁ _

/-- The bounded-discrepancy normalization of the Frey model comparison,
`c0 = -log(27/64)/6 = log(64/27)/6`. -/
noncomputable def freyDiscrepancy : ℝ := -Real.log (27 / 64 : ℝ) / 6

/-- The realized point datum: the procession-normalized log-volume `(1/6) log q`
of the arithmetic line bundle, shifted by the bounded-discrepancy normalization. -/
noncomputable def qPilotDisplayPoint (a b c : ℕ) : ℝ :=
  (1 / 6) * freyLogQ a b c + freyDiscrepancy

theorem qPilotDisplayPoint_nonneg (a b c : ℕ) : 0 ≤ qPilotDisplayPoint a b c := by
  unfold qPilotDisplayPoint freyDiscrepancy
  have h : 0 ≤ freyLogQ a b c := freyLogQ_nonneg a b c
  have hc : 0 ≤ -Real.log (27 / 64 : ℝ) / 6 := by
    have : Real.log (27 / 64 : ℝ) ≤ 0 :=
      Real.log_nonpos (by norm_num) (by norm_num)
    linarith
  nlinarith

/-- The height comparison from the actual Frey model comparison:
`ht(x) <= (1/6) log q + c0`. -/
theorem height_le_qPilotDisplayPoint {a b c : ℕ} (h : IsABCTriple a b c) :
    Height.logHeight₁ (abcRationalPoint a c) ≤ qPilotDisplayPoint a b c := by
  have h6 := (abcJInvariant_logHeight_bounds_abcRationalPoint h).1
  unfold qPilotDisplayPoint freyLogQ freyDiscrepancy
  linarith

/-- The region volume of the realized point datum is its own value: the region is
`{0, point}` with nonnegative point, and the log-volume is the sup of normalized
log-degrees. -/
theorem regionVolume_qPilotDisplayPoint (a b c : ℕ) :
    realLineHullData.logVolume
        (normalizedComparisonRegion realLineHullData qPilotDisplayPoint a b c) =
      ENNReal.ofReal (qPilotDisplayPoint a b c) := by
  change realLineLogVolume (id '' (({0} : Set ℝ) ∪ {qPilotDisplayPoint a b c})) =
    ENNReal.ofReal (qPilotDisplayPoint a b c)
  rw [Set.image_id, Set.singleton_union]
  exact realLineLogVolume_pair_zero (qPilotDisplayPoint_nonneg a b c)

theorem hullVolume_eq :
    realLineHullData.logVolume realLineHullData.hull = 0 := by
  change realLineLogVolume (∅ : Set ℝ) = 0
  exact realLineLogVolume_empty

/-- **The section-2 uniform display family (named input).**  For every `eps > 0`,
uniform initial-`Theta`-data constants and a residual constant, with the IUT IV
Theorem 1.10 display at the arithmetic-weight dictionary readout (IUT IV
`:1376-1385`; the uniformity is the bounded-discrepancy passage of IUT IV section 2,
`:93-112` and `:2404-2430`). -/
def IUTIVSection2UniformDisplayFamily : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ (l dmod emod eta D : ℝ),
    5 ≤ l ∧ 0 ≤ dmod ∧ 1 ≤ emod ∧ 0 ≤ eta ∧
      20 * dmod / l ≤ eps ∧ 20 * (emod * l + eta) ≤ D ∧
      ∀ a b c : ℕ, IsABCTriple a b c →
        (1 / 6) * freyLogQ a b c ≤
          (1 + 20 * dmod / l) * arithmeticWeight (abcRationalPoint a c) +
            20 * (emod * l + eta)

/-- **Both clauses assembled at the realized carrier.**  Given the section-2 display
family, the per-`epsilon` additive comparison data with `A = 0` exists: F4 is the
height/log-volume dictionary direction (proved from the actual Frey model
comparison), F5 is the display with the slope absorbed into `eps`. -/
theorem s3135_epsilonComparisonAdditive_nonempty
    (hf : IUTIVSection2UniformDisplayFamily) (eps : ℝ) (heps : 0 < eps) :
    Nonempty (Cor312EpsilonArithmeticComparisonAdditive realLineHullData eps 0) := by
  obtain ⟨l, dmod, emod, eta, D, hl, hd, he, heta, hslope, hconst, hdisp⟩ :=
    hf eps heps
  refine
    ⟨{ logShellPoint := qPilotDisplayPoint
       height_le_normalizedRegionVolume_add := ?_
       regionVolume_le_normalizedWeight := ?_ }⟩
  · intro a b c habc
    rw [regionVolume_qPilotDisplayPoint]
    rw [ENNReal.toReal_ofReal (qPilotDisplayPoint_nonneg a b c)]
    have hheight := height_le_qPilotDisplayPoint habc
    have hnn := qPilotDisplayPoint_nonneg a b c
    have hmul : 0 ≤ eps * qPilotDisplayPoint a b c := mul_nonneg heps.le hnn
    nlinarith [hmul]
  · refine ⟨20 * (emod * l + eta) + freyDiscrepancy, fun a b c habc => ?_⟩
    rw [regionVolume_qPilotDisplayPoint, hullVolume_eq, ENNReal.toReal_zero, add_zero,
      ENNReal.toReal_ofReal (qPilotDisplayPoint_nonneg a b c)]
    have hd' := hdisp a b c habc
    have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) := arithmeticWeight_nonneg _
    have hslope' : (20 * dmod / l) * arithmeticWeight (abcRationalPoint a c) ≤
        eps * arithmeticWeight (abcRationalPoint a c) :=
      mul_le_mul_of_nonneg_right hslope hw
    unfold qPilotDisplayPoint
    nlinarith [hd', hslope', hw, hconst, mul_le_mul_of_nonneg_right heps.le hw]

/-- The per-`epsilon` comparison data, extracted from the existence form
(classical choice; the data are `Type`-valued). -/
noncomputable def s3135_epsilonComparisonAdditive_of_displayFamily
    (hf : IUTIVSection2UniformDisplayFamily) (eps : ℝ) (heps : 0 < eps) :
    Cor312EpsilonArithmeticComparisonAdditive realLineHullData eps 0 :=
  Classical.choice (s3135_epsilonComparisonAdditive_nonempty hf eps heps)

/-- **The version-2 additive height/weight contract from the paper inputs.**  The
assembled per-`epsilon` comparison data is consumed by the production bridge
consumer `abcHeightWeightAdditiveBoundV2_of_epsilonComparisonAdditive`
(`Cor312ToABCBridgeInterface.lean:348`), yielding
`ABCHeightWeightAdditiveBoundV2` — the exact IUT IV Theorem A / section 2 shape. -/
theorem s3135_ABCHeightWeightAdditiveBoundV2_of_displayFamily
    (hf : IUTIVSection2UniformDisplayFamily) : ABCHeightWeightAdditiveBoundV2 :=
  abcHeightWeightAdditiveBoundV2_of_epsilonComparisonAdditive realLineHullData
    (fun _ => 0)
    (fun eps heps => s3135_epsilonComparisonAdditive_of_displayFamily hf eps heps)

#check IUTIVSection2UniformDisplayFamily
#check s3135_epsilonComparisonAdditive_of_displayFamily
#check s3135_ABCHeightWeightAdditiveBoundV2_of_displayFamily

end LeanFormal.IUT.XiFPaper.S3135ComparisonAssemblyActual
end
