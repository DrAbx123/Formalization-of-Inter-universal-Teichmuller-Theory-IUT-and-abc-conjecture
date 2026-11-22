import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

/-!
# ABC frontier reductions: the implemented weakening slots

`ABCBridge/Bridge/ABCFrontier.lean` re-expresses the frozen bridge interface
`Cor312ToABCBridgeInterface` (`Cor312ToABCBridgeInterface.lean:404`) as the
named enemy `ABCFrontier` and reserved two reduction slots that replace the
coarse clauses F4 (`FrontierHeightComparisonClause`) and F5
(`FrontierRegionComparisonClause`) by finer named sub-clauses.  This module
implements both slots; the reservation paragraph of the companion module is
updated accordingly and the reduction protocol itself is unchanged.  Every
sub-clause records its consumer, tree status, attack surface and upgrade
condition, and the chain

`ABCFrontierGapReduced → ABCFrontier → Cor312ToABCBridgeInterface → ABCConjecture`

stays intact by proved compositions.  The full per-sub-clause ledger is
section H of `logs/coordination/finite-certificate-link-wiring-20261016.md`;
the consumer anchors follow the E7 line of
`logs/coordination/wild-brainstorm-20261017.md:1088-1092`.

## The sub-clauses

| sub-clause | shape | consumer |
| --- | --- | --- |
| F4a `FrontierHeightWeightClause` | height vs weight | F4; pointwise `hpoint` |
| F4b `FrontierWeightRegionClause` | weight vs region volume | F4 |
| F5a `FrontierUnitNormalizationClause` | unit region vs hull (`∃` D₀) | F5 via `:306` |
| F5b `FrontierSplitClause` | region vs scaled unit + point | F5 via `:306` |
| F5c `FrontierPointFinitenessClause` | scaled point finiteness | F5 via `:306` |
| F5d `FrontierPointVolumeWeightClause` | point volume vs weight (+D₁) | F5 via `:306` |
| P1 `FrontierUnitMembershipClause` | point `∈` unit region | absorbs F5b/F5c (`:409`, `:432`) |
| P2 `FrontierPointHeightClause` | point volume vs height | pointwise `hpoint` (via F4a, `:455`) |

Tree statuses (proved supply / frozen card / refuted / none) are recorded in
the docstring of each sub-clause below.

## Honest boundary

The reductions are *sufficient factorizations*: the reduced conjunction implies
the clause it supports, so the enemy becomes finer-grained per sub-clause; no
strength reduction is claimed, and the calibration fixture does not inhabit the
reduced frontiers (its weight/region sub-clause fails at
`Cor312ComparisonGapReduction.lean:232`).  The reserved `:367` assembly is not
used because its `hval` input is refuted (`no_oneAdd_valuation_bound`).  Not
proved: any sub-clause at a source-faithful carrier; nowhere is F4, F5, the
paper-literal carrier or ABC closed.
-/

namespace LeanFormal.IUT

noncomputable section

universe u

/-! ## 1. The named sub-clauses -/

/-- Sub-clause F4a: height versus arithmetic weight, the conclusion shape of
the proved H1 reduction (`ABCHeightArithmeticWeightComparison.lean:99`).

Consumer: `ABCFrontier.reduce_gapReductionInputs` (with F4b reassembles F4) and
`ABCFrontier.reduce_pointwiseResidual` (with `FrontierPointHeightClause` it
discharges the point-volume/weight input with `D₁ = 0`).

Tree status: no supply.  The `hval` input of the H1 reduction is refuted
(`no_oneAdd_valuation_bound`, family `(1, 2^k - 1, 2^k)`); the additive
re-freeze `ABCHeightWeightAdditiveBoundV2`
(`ABCHeightArithmeticWeightComparison.lean:158`, ABC-equivalent by `:167`) is
the recorded upgrade path.

Attack surface: a height-versus-weight comparison at the source carrier.
Upgrade condition: adopt the additive form (slack `∃ A`) and absorb `A` on
the F5 side through a new cross-clause assembly (not in the tree). -/
def FrontierHeightWeightClause : Prop :=
  ∀ (ε : Real) (_ : 0 < ε) (a b c : Nat), IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + ε) * arithmeticWeight (abcRationalPoint a c)

/-- Sub-clause F4b: arithmetic weight versus the comparison-region log-volume,
the named `hweightvol` input of the gap-1 reduction
(`Cor312ComparisonGapReduction.lean:198`).

Consumer: `ABCFrontier.reduce_gapReductionInputs` (transports the `(1 + ε)`
factor by nonnegativity to reassemble F4).

Tree status: refuted at the calibration carrier: there the fixture triple
`(1, 2, 3)` has `log 6 > log 3`
(`cor312Gap1_exists_carrier_arithmeticWeight_gt_normalizedComparisonRegionVolume`,
`:232`; uniform form `:272`), so the sub-clause is a genuine extra hypothesis
(`:195-197`).  Conditional route:
`cor312Gap1_weight_le_normalizedRegionVolume_of_singletonVolume` (`:502`)
derives the `ENNReal`-level region comparison from the singleton-level
comparison `ofReal (arithmeticWeight x) ≤ logVolume {scaleShift point}`; the
value-realized singleton bridge is the source-facing gap.

Attack surface: the singleton weight/point-volume comparison at the source
carrier, with region finiteness for the `toReal` form (`:498-501`).
Upgrade condition: land the singleton comparison in the source layer. -/
def FrontierWeightRegionClause {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) : Prop :=
  ∀ (ε : Real) (hε : 0 < ε) (a b c : Nat), IsABCTriple a b c →
    arithmeticWeight (abcRationalPoint a c) ≤
      (W.logVolume (normalizedComparisonRegion W (point ε hε) a b c)).toReal

/-- Sub-clause F5a (`hunit`): the `ε`-independent normalization of the unit
region against the hull (slack `D₀`).  Consumer:
`ABCFrontier.reduce_gapReductionInputs` (through `:306`).

Tree status: value-realized supply proved
(`cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume`,
`Cor312ComparisonGapSupplyLayer.lean:167`), conditional on the Card A
degree-bound comparison (unit-region degree bound versus hull log-volume).

Attack surface: Card A, the hull-side volume inventory at the source carrier.
Upgrade condition: land the Card A supply. -/
def FrontierUnitNormalizationClause {X : Type u} (W : IQHullLogVolumeInterface X) : Prop :=
  ∃ D₀ : Real, 0 ≤ D₀ ∧
    W.logVolume W.unitRegion ≤ W.logVolume W.hull + ENNReal.ofReal D₀

/-- Sub-clause F5b (`hsplit`): subadditivity of the comparison-region volume
over the scaled unit region and the scaled named point.

Consumer: `:306` through `ABCFrontier.reduce_gapReductionInputs`; absorbed by
`FrontierUnitMembershipClause` in `ABCFrontier.reduce_pointwiseResidual`.

Tree status: value-realized supply proved
(`Cor312ComparisonGapSupplyLayer.lean:127`); abstract derivation from
membership `Cor312ComparisonGapReduction.lean:409`.

Attack surface: none left at this shape; the remaining content is the
membership datum itself.
Upgrade condition: weaken `FrontierUnitMembershipClause`. -/
def FrontierSplitClause {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) : Prop :=
  ∀ (ε : Real) (hε : 0 < ε) (a b c : Nat), IsABCTriple a b c →
    W.logVolume (normalizedComparisonRegion W (point ε hε) a b c) ≤
      W.logVolume (W.scaleShift '' W.unitRegion) +
        W.logVolume {W.scaleShift (point ε hε a b c)}

/-- Sub-clause F5c (`hptfin`): finiteness of the scaled singleton volume of the
named point.

Consumer: `:306` through `ABCFrontier.reduce_gapReductionInputs`; absorbed by
`FrontierUnitMembershipClause` in `ABCFrontier.reduce_pointwiseResidual`.

Tree status: value-realized supply proved
(`Cor312ComparisonGapSupplyLayer.lean:152`); abstract derivation from
membership `Cor312ComparisonGapReduction.lean:432`; not derivable from the
carrier fields alone (spike-carrier independence witness,
`Cor312PointwiseResidualSupply.lean:171`).

Attack surface: none left at this shape; the membership datum itself.
Upgrade condition: weaken `FrontierUnitMembershipClause`. -/
def FrontierPointFinitenessClause {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) : Prop :=
  ∀ (ε : Real) (hε : 0 < ε) (a b c : Nat), IsABCTriple a b c →
    W.logVolume {W.scaleShift (point ε hε a b c)} < ⊤

/-- Sub-clause F5d (`hpoint` with slack `D₁`): the scaled singleton volume
against `(1 + ε) * arithmeticWeight + D₁`.

Consumer: `:306` through `ABCFrontier.reduce_gapReductionInputs`; in
`ABCFrontier.reduce_pointwiseResidual` replaced by `D₁ = 0` through
`FrontierPointHeightClause` composed with F4a (the point-height step of
`Cor312ComparisonGapReduction.lean:455`).

Tree status: no uniform supply; the v1 pointwise closures live at the
value-realized carrier along `Cor312PointwiseResidualSupply.lean:359/:369`,
the additive route at `:385` (with `D₁ = A`).

Attack surface: the point-volume/weight comparison (one scalar per triple).
Upgrade condition: `FrontierPointHeightClause` plus F4a, or the additive
input. -/
def FrontierPointVolumeWeightClause {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) : Prop :=
  ∀ (ε : Real) (hε : 0 < ε), ∃ D₁ : Real, ∀ (a b c : Nat), IsABCTriple a b c →
    (W.logVolume {W.scaleShift (point ε hε a b c)}).toReal ≤
      (1 + ε) * arithmeticWeight (abcRationalPoint a c) + D₁

/-- Sub-clause P1 of the pointwise layer (membership datum): every named point
lies in the unit region on ABC triples; this single datum absorbs `hsplit` and
`hptfin` (`Cor312ComparisonGapReduction.lean:409`, `:432`).

Consumer: `ABCFrontier.reduce_pointwiseResidual`.

Tree status: no supply at the source layer; in the concrete IQ calibration
model unit-region membership is incompatible with the weighted-volume shape
(`IQCarrierConcreteModel.lean:531`), and the spike witness
(`Cor312PointwiseResidualSupply.lean:171`) shows the sibling finiteness
statement is not a carrier theorem.

Attack surface: the source-facing membership of the q-pilot image point in the
unit region.
Upgrade condition: construct the membership at the source layer, or replace it
by a strictly smaller named datum. -/
def FrontierUnitMembershipClause {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) : Prop :=
  ∀ (ε : Real) (hε : 0 < ε) (a b c : Nat), IsABCTriple a b c →
    point ε hε a b c ∈ W.unitRegion

/-- Sub-clause P2 of the pointwise layer (point-height dictionary direction):
the scaled singleton volume against the canonical height; the frozen card
`Cor312PointwisePointHeightDictionary` (`Cor312PointwiseResidualSupply.lean:246`,
normal form `:258`).

Consumer: `ABCFrontier.reduce_pointwiseResidual` (with F4a it discharges
`FrontierPointVolumeWeightClause` with `D₁ = 0`).

Tree status: frozen card, no supply; no declaration in the tree bridges
`sourceLocalLogDegree` to `Height.logHeight₁`, and the only in-tree
scaled-point estimate is `≤ max degreeBound 0` (`:287`), carrying no height
content.

Attack surface: the `sourceLocalLogDegree → Height.logHeight₁` bridge at
the source carrier.
Upgrade condition: prove the dictionary normal form at the source layer
(`max (sourceLocalLogDegree v (D.scaling * p)) 0 ≤ Height.logHeight₁`). -/
def FrontierPointHeightClause {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) : Prop :=
  ∀ (ε : Real) (hε : 0 < ε) (a b c : Nat), IsABCTriple a b c →
    (W.logVolume {W.scaleShift (point ε hε a b c)}).toReal ≤
      Height.logHeight₁ (abcRationalPoint a c)

/-! ## 2. The reduced frontiers and the two implemented slots -/

/-- The gap-reduction frontier: F4 factored into F4a and F4b, F5 replaced by
the four named inputs F5a-F5d; sufficient for `ABCFrontier` by
`ABCFrontier.reduce_gapReductionInputs`. -/
def ABCFrontierGapReduced : Prop :=
  ∃ (X : Type u) (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X),
    FrontierHeightWeightClause ∧ FrontierWeightRegionClause W point ∧
      FrontierUnitNormalizationClause W ∧ FrontierSplitClause W point ∧
      FrontierPointFinitenessClause W point ∧ FrontierPointVolumeWeightClause W point

/-- The pointwise-residual frontier: F4 factored as above; F5's point-side
inputs absorbed into the membership datum P1 and the point-height dictionary
direction P2; sufficient for `ABCFrontierGapReduced` (hence `ABCFrontier`) by
`ABCFrontier.reduce_pointwiseResidual`. -/
def ABCFrontierPointwiseReduced : Prop :=
  ∃ (X : Type u) (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X),
    FrontierHeightWeightClause ∧ FrontierWeightRegionClause W point ∧
      FrontierUnitNormalizationClause W ∧ FrontierUnitMembershipClause W point ∧
      FrontierPointHeightClause W point

/-- **Implemented reduction slot `ABCFrontier.reduce_gapReductionInputs`.**
The reduced-input frontier implies the full frontier: F4 is reassembled from
F4a and F4b by the `(1 + ε)`-transport, and F5 follows from F5a-F5d through
`cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound`
(`Cor312ComparisonGapReduction.lean:306`).  The `:367` assembly is avoided
because its `hval` input is refuted. -/
theorem ABCFrontier.reduce_gapReductionInputs :
    ABCFrontierGapReduced.{u} → ABCFrontier.{u} := by
  rintro ⟨X, W, point, hhw, hwv, hunit, hsplit, hptfin, hpoint⟩
  refine ⟨X, W, point, ?_, ?_⟩
  · intro ε hε a b c habc
    exact le_trans (hhw ε hε a b c habc)
      (mul_le_mul_of_nonneg_left (hwv ε hε a b c habc) (by linarith))
  · intro ε hε
    obtain ⟨D₀, hD₀, hunitD⟩ := hunit
    obtain ⟨D₁, hpointD⟩ := hpoint ε hε
    exact cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
      W (point ε hε) hD₀ hunitD (hsplit ε hε) (hptfin ε hε) hpointD

/-- **Implemented reduction slot `ABCFrontier.reduce_pointwiseResidual`.**
The pointwise frontier implies the gap-reduction frontier: `hsplit` from P1 by
`:409`, `hptfin` from P1 by `:432`, and `hpoint` with `D₁ = 0` by chaining
P2 into F4a (the point-height step of `:455`). -/
theorem ABCFrontier.reduce_pointwiseResidual :
    ABCFrontierPointwiseReduced.{u} → ABCFrontier.{u} := by
  rintro ⟨X, W, point, hhw, hwv, hunit, hmem, hvolheight⟩
  refine ABCFrontier.reduce_gapReductionInputs.{u}
    ⟨X, W, point, hhw, hwv, hunit, ?_, ?_, ?_⟩
  · intro ε hε
    exact cor312Gap2_hsplit_of_mem_unitRegion W (point ε hε)
      (fun a b c habc => hmem ε hε a b c habc)
  · intro ε hε
    exact cor312Gap2_hptfin_of_mem_unitRegion W (point ε hε)
      (fun a b c habc => hmem ε hε a b c habc)
  · intro ε hε
    refine ⟨0, fun a b c habc => ?_⟩
    simpa only [add_zero] using
      le_trans (hvolheight ε hε a b c habc) (hhw ε hε a b c habc)

/-! ## 3. Composed chains (frontier reductions to the frozen consumers) -/

/-- Composed chain of the gap-reduction slot: the reduced-input frontier
assembles the frozen interface field by field through
`bridgeInterface_of_frontier`. -/
def bridgeInterface_of_frontierGapReduced (h : ABCFrontierGapReduced.{u}) :
    Cor312ToABCBridgeInterface.{u} :=
  bridgeInterface_of_frontier.{u} (ABCFrontier.reduce_gapReductionInputs.{u} h)

/-- Composed chain of the gap-reduction slot: the reduced-input frontier closes
ABC through `abcConjecture_of_frontier`.  Conditional by construction; no
sub-clause is proved at source level. -/
theorem abcConjecture_of_frontierGapReduced (h : ABCFrontierGapReduced.{u}) :
    ABCConjecture :=
  abcConjecture_of_frontier.{u} (ABCFrontier.reduce_gapReductionInputs.{u} h)

/-- Composed chain of the pointwise-residual slot: the pointwise frontier
assembles the frozen interface field by field. -/
def bridgeInterface_of_frontierPointwiseReduced (h : ABCFrontierPointwiseReduced.{u}) :
    Cor312ToABCBridgeInterface.{u} :=
  bridgeInterface_of_frontier.{u} (ABCFrontier.reduce_pointwiseResidual.{u} h)

/-- Composed chain of the pointwise-residual slot: the pointwise frontier
closes ABC through `abcConjecture_of_frontier`. -/
theorem abcConjecture_of_frontierPointwiseReduced
    (h : ABCFrontierPointwiseReduced.{u}) : ABCConjecture :=
  abcConjecture_of_frontier.{u} (ABCFrontier.reduce_pointwiseResidual.{u} h)

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the implemented reduction slots of `ABCFrontier`:
gap-reduction-inputs factorization and pointwise-residual absorption, with the
per-sub-clause ledger (consumer, tree status, attack surface, upgrade
condition) in `ABCBridge/Bridge/ABCFrontierReductions.lean` and section H of
`logs/coordination/finite-certificate-link-wiring-20261016.md`. -/
def abcFrontierReductionLedger : Obligation :=
  { id := "IUT-III.cor312-to-ABC-frontier-reduction"
    source :=
      "IUT III Corollary 3.12; IUT IV section 2; the frozen interface " ++
        "Cor312ToABCBridgeInterface of ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:404"
    status := VerificationStatus.interface
    note :=
      "The reserved reduction slots of ABCFrontier are implemented in " ++
        "ABCBridge/Bridge/ABCFrontierReductions.lean.  " ++
        "ABCFrontier.reduce_gapReductionInputs factors F4 into " ++
        "FrontierHeightWeightClause (F4a) and FrontierWeightRegionClause (F4b) " ++
        "and replaces F5 by FrontierUnitNormalizationClause (F5a), " ++
        "FrontierSplitClause (F5b), FrontierPointFinitenessClause (F5c) and " ++
        "FrontierPointVolumeWeightClause (F5d) through " ++
        "cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound " ++
        "(Cor312ComparisonGapReduction.lean:306); the reserved :367 assembly is " ++
        "not used because its hval input is refuted (no_oneAdd_valuation_bound).  " ++
        "ABCFrontier.reduce_pointwiseResidual absorbs hsplit and hptfin into " ++
        "FrontierUnitMembershipClause (P1, :409/:432) and hpoint into " ++
        "FrontierPointHeightClause (P2) composed with F4a (:455, D1 = 0), " ++
        "yielding ABCFrontierPointwiseReduced.  Both are sufficient " ++
        "factorizations: the reduced conjunction implies the clause it " ++
        "supports; no strength reduction is claimed, and the calibration " ++
        "fixture does not inhabit the reduced frontiers (the weight/region " ++
        "sub-clause fails there, :232/:272).  Sub-clause statuses: F5a/F5b/F5c " ++
        "have value-realized supplies (Cor312ComparisonGapSupplyLayer.lean:167/:127/:152); " ++
        "P1 and P2 have none (P2 is the frozen Cor312PointwisePointHeightDictionary " ++
        "card); F4a has none (hval route refuted; additive re-freeze " ++
        "ABCHeightArithmeticWeightComparison.lean:158/:167 is the upgrade path); " ++
        "F4b is refuted at the fixture.  NOT proved: any sub-clause at a " ++
        "source-faithful carrier; ABC remains open."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-frontier-ledger",
        "IUT-III.cor312-comparison-gap-reduction",
        "IUT-III.cor312-pointwise-residual-supply",
        "ABC.proof-target" ] }

end LeanFormal.IUT.Audit
