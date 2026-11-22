import tmp.sheaf.xif.paper.S3135ActualF4LogShellDegreeActual

/-!
# Card (2): the normalized scaling-log-degree card, reduced exactly

**task-11 deliverable (second card).**  The task-10 file reduced the F4 residual to the
value-group faithfulness card and the scaling-normalization card
`S3135ScalingNormalization eps`:
`∀ ABC triples, 0 ≤ (1+eps)·logDegree_v(scaling) + eps·ht(x)`,
equivalently `(1+eps)·(-logDegree_v(scaling)) ≤ eps·ht(x)`.

This file proves that the full family over all `eps > 0` is **exactly equivalent** to
the single scalar normalization equation

`S3135ScalingLogDegreeZero : logDegree_v(scaling) = 0`,

using the carrier field `scaling_logDegree_nonpos` and the ABC triple `(1, 1, 2)`
(height `log 2 > 0`): a negative contraction `logDegree_v(scaling) < 0` cannot be
absorbed for arbitrarily small `eps`.  Hence card (2) is *not* a consequence of the
`SourceUnitRegionHaarData` fields (which only give `logDegree_v(scaling) ≤ 0`); it is
the normalized-scaling equation of the procession-normalized log-volume
(IUT III Remark 3.9.5, (i): the `lambda·O` normalization; IUT IV section 1,
Proposition 1.4, iut4.txt:671-760), recorded as the exact smaller missing.

The file also assembles F4 at the actual carrier from the full faithfulness card
(task-10) together with this zero-log-degree normalization.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual

namespace LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)

/-- **The exact smaller missing of card (2)**: the normalized scaling has zero
log-degree.  The carrier data only provides `logDegree_v(scaling) ≤ 0`
(`SourceUnitRegionHaarData.scaling_logDegree_nonpos`); the procession-normalized
log-volume of IUT III Remark 3.9.5, (i) / IUT IV section 1 normalizes `lambda·O` so
that the scaling contributes no log-volume, which is this equation. -/
def S3135ScalingLogDegreeZero : Prop :=
  I.sourceLocalLogDegree v D.scaling = 0

/-- `(1, 1, 2)` is an ABC triple. -/
theorem abcTriple_one_one_two : IsABCTriple 1 1 2 :=
  ⟨Nat.one_pos, Nat.one_pos, by norm_num, Nat.coprime_one_left 1⟩

/-- The height of the ABC point of `(1, 1, 2)` is `log 2`. -/
theorem logHeight_one_one_two :
    Height.logHeight₁ (abcRationalPoint 1 2) = Real.log 2 :=
  abcRationalPoint_logHeight₁ abcTriple_one_one_two

/-- **Real-variable core of card (2).**  If `L ≤ 0` and the normalized scaling
inequality `0 ≤ (1+eps)·L + eps·log 2` holds for every `eps > 0` (the `(1,1,2)`
height), then `L = 0`: a negative `L` loses against the positive constant `log 2`
as `eps → 0`. -/
theorem scalingLogDegree_eq_zero_of_normalized_inequality (L : ℝ) (hL : L ≤ 0)
    (hnorm : ∀ eps : ℝ, 0 < eps → 0 ≤ (1 + eps) * L + eps * Real.log 2) :
    L = 0 := by
  rcases lt_or_eq_of_le hL with hlt | heq
  · exfalso
    rcases le_total (L + Real.log 2) 0 with hsum | hsum
    · have h := hnorm 1 (by norm_num)
      linarith
    · rcases lt_or_eq_of_le hsum with hpos | heq0
      · have hden : (0 : ℝ) < 2 * (L + Real.log 2) := by linarith
        have hepspos : 0 < -L / (2 * (L + Real.log 2)) :=
          div_pos (neg_pos.mpr hlt) hden
        have h := hnorm _ hepspos
        have hden_ne : (2 * (L + Real.log 2)) ≠ 0 := ne_of_gt hden
        have hval : (1 + (-L / (2 * (L + Real.log 2)))) * L +
            (-L / (2 * (L + Real.log 2))) * Real.log 2 = L / 2 := by
          field_simp [hden_ne]
          ring
        rw [hval] at h
        linarith
      · have h := hnorm 1 (by norm_num)
        linarith
  · exact heq

/-- **Card (2) forces zero scaling log-degree.**  If the normalized scaling inequality
holds for every `eps > 0`, then with the carrier bound `logDegree_v(scaling) ≤ 0` the
scaling log-degree must vanish (the triple `(1,1,2)` supplies the positive height
`log 2`). -/
theorem s3135_scalingLogDegreeZero_of_normalization
    (hnorm : ∀ eps : ℝ, 0 < eps → S3135ScalingNormalization I v R n D eps) :
    S3135ScalingLogDegreeZero I v R n D := by
  unfold S3135ScalingLogDegreeZero
  refine scalingLogDegree_eq_zero_of_normalized_inequality
    (I.sourceLocalLogDegree v D.scaling) D.scaling_logDegree_nonpos ?_
  intro eps heps
  have h := hnorm eps heps 1 1 2 abcTriple_one_one_two
  rw [logHeight_one_one_two] at h
  exact h

/-- Conversely, zero scaling log-degree gives the normalized scaling inequality for
every `eps > 0` (the point log-volume is the height, which is nonnegative). -/
theorem s3135_normalization_of_scalingLogDegreeZero
    (hzero : S3135ScalingLogDegreeZero I v R n D) :
    ∀ eps : ℝ, 0 < eps → S3135ScalingNormalization I v R n D eps := by
  intro eps heps a b c habc
  unfold S3135ScalingLogDegreeZero at hzero
  rw [hzero]
  have hht : 0 ≤ Height.logHeight₁ (abcRationalPoint a c) := Height.zero_le_logHeight₁ _
  have : (0 : ℝ) ≤ eps * Height.logHeight₁ (abcRationalPoint a c) :=
    mul_nonneg heps.le hht
  linarith

/-- **Exact equivalence**: card (2), as a family over all `eps > 0`, is precisely the
normalized-scaling equation `logDegree_v(scaling) = 0`. -/
theorem s3135_normalization_family_iff_scalingLogDegreeZero :
    (∀ eps : ℝ, 0 < eps → S3135ScalingNormalization I v R n D eps) ↔
      S3135ScalingLogDegreeZero I v R n D :=
  ⟨s3135_scalingLogDegreeZero_of_normalization I v R n D,
    s3135_normalization_of_scalingLogDegreeZero I v R n D⟩

/-- **F4 at the actual carrier from the two named cards** (value-group degree
faithfulness from task-10 + zero normalized scaling log-degree). -/
theorem s3135_actualF4_of_faithfulness_scalingZero
    (hdeg : S3135ValueGroupDegreeFaithfulness I v R)
    (hzero : S3135ScalingLogDegreeZero I v R n D) :
    FrontierHeightComparisonClause (sourceActualCarrier I v R n D)
      (fun _ _ a b c => abcSourcePoint I v R a b c) :=
  s3135_actualF4_withSourcePoint I v R n D hdeg
    (s3135_normalization_of_scalingLogDegreeZero I v R n D hzero)

#check S3135ScalingLogDegreeZero
#check s3135_normalization_family_iff_scalingLogDegreeZero
#check s3135_actualF4_of_faithfulness_scalingZero

end LeanFormal.IUT.XiFPaper.S3135ScalingNormalizationActual
end
