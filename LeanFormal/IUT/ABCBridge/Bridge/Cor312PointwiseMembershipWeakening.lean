import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierReductions
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer

/-!
# F5b/F5c weakening: the unit-membership premise replaced by the split/finiteness pair

The pointwise-residual frontier (ABCFrontierPointwiseReduced,
ABCFrontierReductions.lean:243) compresses the two F5 point-side inputs F5b
(FrontierSplitClause, :136) and F5c (FrontierPointFinitenessClause, :157) into the
single membership datum P1 (FrontierUnitMembershipClause, :199): P1 implies F5b by
cor312Gap2_hsplit_of_mem_unitRegion (Cor312ComparisonGapReduction.lean:409) and F5c
by cor312Gap2_hptfin_of_mem_unitRegion (:432).  This module executes the repair
recorded as open in the P1 premise evaluation: replace P1 by the strictly smaller
named datum

* FrontierPointSplitFinitenessClause W point := FrontierSplitClause W point and
  FrontierPointFinitenessClause W point

and rebuild the reduction slot on it.  The weakened datum is strictly smaller in
the implication sense:

* P1 implies it by the two rewirings above
  (frontierPointSplitFinitenessClause_of_unitMembership, Section 2);
* it does not imply P1
  (frontierPointSplitFinitenessClause_not_imply_unitMembership, Section 3 witness).

## Route accounting

* Route A (smaller named datum) -- proved here: the replaced frontier
  ABCFrontierPointwiseWeakened reduces to ABCFrontier through the gap-reduced
  frontier (pointwiseWeakened_to_gapReduced,
  ABCFrontier.reduce_pointwiseWeakenedResidual), with the composed chains
  bridgeInterface_of_frontierPointwiseWeakened and
  abcConjecture_of_frontierPointwiseWeakened.
* Route B (derivation from existing source data) -- proved, conditional on the
  StepXI data: at the value-realized carrier the weakened datum is a theorem for
  every point map (Section 5), rebased from cor312GapSupply_sourceInterface_hsplit
  (Cor312ComparisonGapSupplyLayer.lean:127) and
  cor312GapSupply_sourceInterface_hptfin (:152).
* Route C (card) -- not needed: the strengthened datum P1 itself stays the open
  datum; its interface-level exclusion is recorded below and its premise
  evaluation is carried by the companion files.

## Why the weakening is the repair, not a cosmetic change

P1 is not only unsupplied: at any interface, membership collapses the comparison
region to the scaled unit region, whose log-volume is finite, while the arithmetic
weights are unbounded, so P1 is incompatible with the weight/region conjunct F4b
of its own consumer frontier (iqCarrierModel_hmem_hweightvol_incompatible,
IUTIII/Corollary312/StepXI/HolomorphicHull/IQCarrierConcreteModel.lean:531 -- an
interface-level theorem, general in W and the point map).  The successor frontier
of that exclusion and the P1 premise cards live in the companion P1 evaluation
files (ABCBridge/Bridge/ABCFrontierPointwisePremiseReduction.lean,
ABCBridge/Bridge/ABCFrontierSingletonReduction.lean); this module neither imports
nor duplicates their statements, and references them only as context.  The
weakened datum does not collapse the region: F5c carries finiteness per triple
through the singleton term, and F5b permits the singleton term to vary (and grow)
with the triple, so no fixed finite bound on the region is forced.

## Honest boundary

The chain ABCFrontierPointwiseWeakened -> ABCFrontier -> Cor312ToABCBridgeInterface
-> ABCConjecture below is a conditional reduction; no clause is proved at a
source-faithful carrier.  F4a, F4b, F5a and P2 keep their recorded statuses (no
supply / degree dictionary / Card A / frozen point-height card) unchanged by this
module; only the two F5 point-side clauses acquire supplies, and only at the
value-realized interface (Section 5).  Not proved: any inhabitant of
ABCFrontierPointwiseWeakened (F4a and P2 remain open at every carrier), and the
membership datum stays unprovable in the replaced consumer shape.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT

noncomputable section

universe u ua uv upi umon ui

/-! ## 1. The weakened datum and the weakened pointwise frontier -/

/-- **The weakened unit datum (P1 replaced).**  The F5 point-side pair that P1
absorbs, as a single named clause: split over the scaled unit region and the
scaled named point, plus finiteness of the scaled singleton.  Strictly smaller
than FrontierUnitMembershipClause: membership implies it (Section 2) and it does
not imply membership (Section 3). -/
def FrontierPointSplitFinitenessClause {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) : Prop :=
  FrontierSplitClause W point ∧ FrontierPointFinitenessClause W point

/-- **The weakened pointwise frontier.**  ABCFrontierPointwiseReduced
(ABCFrontierReductions.lean:243) with FrontierUnitMembershipClause replaced by
the strictly smaller FrontierPointSplitFinitenessClause.  Sufficient for
ABCFrontier by ABCFrontier.reduce_pointwiseWeakenedResidual; the F5-repair datum
it carries has source-layer supplies (Section 5), unlike the replaced
membership datum. -/
def ABCFrontierPointwiseWeakened : Prop :=
  ∃ (X : Type u) (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X),
    FrontierHeightWeightClause ∧ FrontierWeightRegionClause W point ∧
      FrontierUnitNormalizationClause W ∧ FrontierPointSplitFinitenessClause W point ∧
      FrontierPointHeightClause W point

/-! ## 2. The replacement direction: membership implies the weakened datum -/

/-- **Absorption of the weakened datum from P1.**  FrontierUnitMembershipClause
implies FrontierPointSplitFinitenessClause by the two membership rewirings
(cor312Gap2_hsplit_of_mem_unitRegion, Cor312ComparisonGapReduction.lean:409;
cor312Gap2_hptfin_of_mem_unitRegion, :432). -/
theorem frontierPointSplitFinitenessClause_of_unitMembership {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) :
    FrontierUnitMembershipClause W point → FrontierPointSplitFinitenessClause W point :=
  fun hmem =>
    ⟨fun ε hε a b c habc =>
        cor312Gap2_hsplit_of_mem_unitRegion W (point ε hε)
          (fun a b c habc => hmem ε hε a b c habc) a b c habc,
      fun ε hε a b c habc =>
        cor312Gap2_hptfin_of_mem_unitRegion W (point ε hε)
          (fun a b c habc => hmem ε hε a b c habc) a b c habc⟩

/-- **Frontier-level replacement.**  Every inhabitant of the old pointwise
frontier yields an inhabitant of the weakened one after replacing P1 by its
consequence: the weakening removes the membership premise and changes nothing
else. -/
theorem pointwiseWeakened_of_pointwiseReduced (h : ABCFrontierPointwiseReduced.{u}) :
    ABCFrontierPointwiseWeakened.{u} := by
  obtain ⟨X, W, point, hhw, hwv, hunit, hmem, hvolheight⟩ := h
  exact ⟨X, W, point, hhw, hwv, hunit,
    frontierPointSplitFinitenessClause_of_unitMembership W point hmem, hvolheight⟩

/-! ## 3. Strictness witness: the weakened datum does not imply membership -/

/-- Witness carrier for the strictness of the replacement: every log-volume is
zero, so the split and finiteness clauses hold trivially, while the unit region
is {0} and the witnessing point map is constantly 1, so membership fails.  This
is the constant-zero log-volume carrier shape (the companion P1 evaluation uses
the empty-region variant frontierZeroCarrier); it is an interface-combinatorial
witness, not a model of the paper carrier. -/
def frontierWeakeningWitnessCarrier : IQHullLogVolumeInterface ℝ where
  imageSet := ∅
  hull := ∅
  imageSet_subset_hull := Set.empty_subset _
  logVolume := fun _ => 0
  logVolume_mono := by
    intro S T hST
    exact le_refl 0
  unitRegion := {0}
  scaleShift := id
  hull_subset_scaleShift := Set.empty_subset _
  unitRegion_logVolume_lt_top := ENNReal.zero_lt_top
  scaleShift_unitRegion_logVolume_le := le_refl 0

theorem frontierWeakeningWitnessCarrier_splitClause :
    FrontierSplitClause frontierWeakeningWitnessCarrier (fun _ _ _ _ _ => (1 : ℝ)) := by
  intro ε hε a b c habc
  change (0 : ENNReal) ≤ 0 + 0
  exact zero_le

theorem frontierWeakeningWitnessCarrier_pointFinitenessClause :
    FrontierPointFinitenessClause frontierWeakeningWitnessCarrier
      (fun _ _ _ _ _ => (1 : ℝ)) := by
  intro ε hε a b c habc
  change (0 : ENNReal) < ⊤
  exact ENNReal.zero_lt_top

theorem frontierWeakeningWitnessCarrier_not_unitMembership :
    ¬ FrontierUnitMembershipClause frontierWeakeningWitnessCarrier
      (fun _ _ _ _ _ => (1 : ℝ)) := by
  intro hmem
  have hmem' : (1 : ℝ) ∈ ({0} : Set ℝ) :=
    hmem 1 (by norm_num) 1 2 3
      ⟨Nat.one_pos, by norm_num, by norm_num, Nat.coprime_one_left 2⟩
  rw [Set.mem_singleton_iff] at hmem'
  exact one_ne_zero hmem'

/-- **The weakened datum does not imply membership.**  The witness carrier
satisfies FrontierSplitClause and FrontierPointFinitenessClause while failing
FrontierUnitMembershipClause, so the replacement is strict: P1 is strictly
stronger than the pair it absorbs. -/
theorem frontierPointSplitFinitenessClause_not_imply_unitMembership :
    ¬ (∀ (X : Type) (W : IQHullLogVolumeInterface X)
        (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X),
        FrontierPointSplitFinitenessClause W point →
          FrontierUnitMembershipClause W point) :=
  fun h =>
    frontierWeakeningWitnessCarrier_not_unitMembership
      (h ℝ frontierWeakeningWitnessCarrier (fun _ _ _ _ _ => (1 : ℝ))
        ⟨frontierWeakeningWitnessCarrier_splitClause,
          frontierWeakeningWitnessCarrier_pointFinitenessClause⟩)

/-! ## 4. The reduction slot on the weakened frontier -/

/-- **The weakened pointwise frontier lands in the gap-reduced frontier.**  The
two components of the weakened datum are F5b and F5c verbatim; hpoint with
D₁ = 0 is the same P2-into-F4a step as in
ABCFrontier.reduce_pointwiseResidual; all other conjuncts are unchanged. -/
theorem pointwiseWeakened_to_gapReduced (h : ABCFrontierPointwiseWeakened.{u}) :
    ABCFrontierGapReduced.{u} := by
  obtain ⟨X, W, point, hhw, hwv, hunit, hsplitfin, hvolheight⟩ := h
  obtain ⟨hsplit, hptfin⟩ := hsplitfin
  refine ⟨X, W, point, hhw, hwv, hunit, hsplit, hptfin, ?_⟩
  intro ε hε
  refine ⟨0, fun a b c habc => ?_⟩
  simpa only [add_zero] using
    le_trans (hvolheight ε hε a b c habc) (hhw ε hε a b c habc)

/-- **Implemented reduction slot ABCFrontier.reduce_pointwiseWeakenedResidual.**
The weakened pointwise frontier implies ABCFrontier through
ABCFrontier.reduce_gapReductionInputs, replacing
ABCFrontier.reduce_pointwiseResidual on the repaired datum.  Conditional by
construction; no sub-clause is proved at a source-faithful carrier. -/
theorem ABCFrontier.reduce_pointwiseWeakenedResidual :
    ABCFrontierPointwiseWeakened.{u} → ABCFrontier.{u} :=
  fun h => ABCFrontier.reduce_gapReductionInputs.{u} (pointwiseWeakened_to_gapReduced h)

/-- Composed chain of the weakened slot: the weakened pointwise frontier
assembles the frozen interface field by field. -/
def bridgeInterface_of_frontierPointwiseWeakened (h : ABCFrontierPointwiseWeakened.{u}) :
    Cor312ToABCBridgeInterface.{u} :=
  bridgeInterface_of_frontier.{u} (ABCFrontier.reduce_pointwiseWeakenedResidual.{u} h)

/-- Composed chain of the weakened slot: the weakened pointwise frontier closes
ABC through abcConjecture_of_frontier.  Conditional by construction; no
sub-clause is proved at a source-faithful carrier. -/
theorem abcConjecture_of_frontierPointwiseWeakened
    (h : ABCFrontierPointwiseWeakened.{u}) : ABCConjecture :=
  abcConjecture_of_frontier.{u} (ABCFrontier.reduce_pointwiseWeakenedResidual.{u} h)

/-! ## 5. Route B: the weakened datum at the value-realized source interface -/

namespace Theorem311Source

namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}

variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- **The weakened datum from existing source data.**  At the value-realized
carrier I.sourceUnitRegionHaarInterface v R n D the weakened datum holds for
every point map, with no ABC-side hypothesis: F5b is the sup-subadditivity
supply cor312GapSupply_sourceInterface_hsplit
(Cor312ComparisonGapSupplyLayer.lean:127) and F5c is the ofReal-finiteness
supply cor312GapSupply_sourceInterface_hptfin (:152).  Conditional only on the
StepXI data R and D. -/
theorem frontierPointSplitFinitenessClause_sourceInterface (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v) :
    FrontierPointSplitFinitenessClause (I.sourceUnitRegionHaarInterface v R n D)
      (fun _ _ => p) :=
  ⟨fun ε hε a b c habc =>
      I.cor312GapSupply_sourceInterface_hsplit v R n D p a b c habc,
    fun _ _ a b c _ =>
      I.cor312GapSupply_sourceInterface_hptfin v R n D p a b c⟩

end OriginalInput

end Theorem311Source

end

end LeanFormal.IUT
