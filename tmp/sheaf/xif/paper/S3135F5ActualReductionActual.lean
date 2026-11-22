import tmp.sheaf.xif.paper.S3135ActualF4LogShellDegreeActual

/-!
# F5 at the actual carrier: minimal residual reduction (region volume vs arithmetic weight)

**task-22 (2).**  F5 is the frontier clause
`FrontierRegionComparisonClause` (`ABCFrontier.lean:173`):

`(logVolume comparison region).toReal <= (1+eps)*arithmeticWeight(x) + (logVolume hull).toReal + D`.

At the actual value-realized carrier `W = I.sourceUnitRegionHaarInterface v R n D`
(`IQCarrierHaarData.lean:159-203`; `logVolume = sourceSetVolume`, an actual sup of
value-monoid log-degrees) this file reduces F5 to **two** minimal cards, using the
already-proved structural inputs of the supply layer:

* `hsplit` (subadditivity of the set log-volume over the union decomposition) —
  **proved unconditionally** for the value-realized carrier:
  `cor312GapSupply_sourceInterface_hsplit` (`Cor312ComparisonGapSupplyLayer.lean:127`);
* `hptfin` (singleton point volume finite) — **proved unconditionally**:
  `cor312GapSupply_sourceInterface_hptfin` (`:152`).

The two remaining cards (named, with paper sources):

1. `S3135ActualUnitHullCard`: the unit-region normalization against the θ-pilot hull
   bound, in the exact supply-layer shape
   `ofReal D.degreeBound <= sourceHullVolume + ofReal D0`, `0 <= D0`
   (IUT III Remark 3.9.5, (i); Corollary 3.12 finiteness :10324-10353; the
   supply-layer reduction `cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume`,
   `Cor312ComparisonGapSupplyLayer.lean:167`).
2. `S3135ActualPointWeightCard`: the arithmetic-line-bundle point volume against the
   arithmetic weight, `(vol {scaleShift point}).toReal <= (1+eps)*weight + D1`
   uniformly in the triple — the IUT IV section 2 point/line-bundle log-volume
   computation (IV:2329-2340; [GenEll] Definition 1.5; IV:2367-2375; the
   `hpoint` input of `Cor312ComparisonGapReduction.lean:306`).

The main theorem `s3135_actualFrontierRegionClause_of_cards` assembles F5 from the
two cards through the frozen reduction
`cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound`
(`Cor312ComparisonGapReduction.lean:306`), so F5 at the actual carrier is *exactly*
these two cards plus the two proved structural inputs.  No residual is renamed into a
proof and no inequality is assumed silently.

Note: the card (2) is the direction opposite to the F4/gap-1 weight comparison
`arithmeticWeight <= region volume`; the two are not interchangeable.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual

namespace LeanFormal.IUT.XiFPaper.S3135F5ActualReductionActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (D : I.SourceUnitRegionHaarData v R n)
variable (p : ℕ → ℕ → ℕ → I.ThetaPilotPoint v)

/-- **Card U (unit-region normalization against the θ-pilot hull bound).**  In the
exact supply-layer discharge shape: the unit-region degree bound is at most the
actual hull log-volume plus a nonnegative constant.  Paper: the normalization of the
log-shell against the θ-pilot hull bound (IUT III Remark 3.9.5, (i); Corollary 3.12
finiteness, :10324-10353). -/
def S3135ActualUnitHullCard : Prop :=
  ∃ D₀ : ℝ, 0 ≤ D₀ ∧
    ENNReal.ofReal D.degreeBound ≤
      I.sourceHullVolume v R n + ENNReal.ofReal D₀

/-- **Card P (point log-volume against the arithmetic weight).**  Uniformly in the
ABC triple, the singleton log-volume of the scaled point is at most `(1+eps)` times
the arithmetic weight plus a triple-independent constant.  Paper: the IUT IV section 2
arithmetic-line-bundle log-volume computation (IV:2329-2340; [GenEll] Definition 1.5;
IV:2367-2375). -/
def S3135ActualPointWeightCard : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ D₁ : ℝ, ∀ a b c : ℕ, IsABCTriple a b c →
    ((I.sourceUnitRegionHaarInterface v R n D).logVolume
        {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)}).toReal ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁

/-- **F5 at the actual carrier from the two named cards.**  The structural inputs
`hsplit`/`hptfin` are the unconditional supply-layer theorems; the reduction is the
frozen gap-2 reduction; only cards U and P remain. -/
theorem s3135_actualFrontierRegionClause_of_cards
    (hU : S3135ActualUnitHullCard I v R n D)
    (hP : S3135ActualPointWeightCard I v R n D p) :
    FrontierRegionComparisonClause (I.sourceUnitRegionHaarInterface v R n D)
      (fun _ _ a b c => p a b c) := by
  intro eps heps
  obtain ⟨D₀, hD₀, hB⟩ := hU
  obtain ⟨D₁, hD₁⟩ := hP eps heps
  exact cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
    (I.sourceUnitRegionHaarInterface v R n D) p hD₀
    (I.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume v R n D hD₀ hB)
    (fun a b c habc => I.cor312GapSupply_sourceInterface_hsplit v R n D p a b c habc)
    (fun a b c _ => I.cor312GapSupply_sourceInterface_hptfin v R n D p a b c)
    hD₁

/-- The card P is exactly the `hpoint` input of the frozen gap-2 reduction (same
statement, same carrier, same point map). -/
theorem s3135_pointWeightCard_eq_hpoint
    (hP : S3135ActualPointWeightCard I v R n D p) :
    ∀ (eps : ℝ) (hε : 0 < eps), ∃ D₁ : ℝ, ∀ a b c : ℕ, IsABCTriple a b c →
      ((I.sourceUnitRegionHaarInterface v R n D).logVolume
          {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁ :=
  hP

#check S3135ActualUnitHullCard
#check S3135ActualPointWeightCard
#check s3135_actualFrontierRegionClause_of_cards

end LeanFormal.IUT.XiFPaper.S3135F5ActualReductionActual
end
