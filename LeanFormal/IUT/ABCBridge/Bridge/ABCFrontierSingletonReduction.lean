import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierReductions
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierConcreteModel

/-!
# ABC frontier: singleton refinement of F4b and refutation of the pointwise absorptions

`ABCBridge/Bridge/ABCFrontierReductions.lean` (imported here, not modified)
refined F4 into F4a/F4b, F5 into F5a-F5d, and — in its pointwise variant —
into P1/P2.  This module continues the down-drill of F4b at its minimal
carrier and records the attackability status of the two pointwise absorptions.

* Section 1 lands the factorization of F4b: F4b follows from the singleton-level
  `ENNReal` comparison (F4bα, `FrontierSingletonWeightVolumeClause`) plus
  finiteness of the comparison-region volume (F4bβ,
  `FrontierRegionFinitenessClause`) — the exact content of
  `cor312Gap1_weight_le_normalizedRegionVolume_of_singletonVolume`
  (`Cor312ComparisonGapReduction.lean:502`) and of its docstring (`:494-501`).
* Section 2 defines the refined gap frontier `ABCFrontierGapReducedV2` and
  proves `ABCFrontierGapReducedV2 -> ABCFrontier -> Cor312ToABCBridgeInterface`
  and `-> ABCConjecture`.
* Section 3 refutes the two pointwise absorptions: membership (P1) is
  incompatible with the weight comparison at any interface, and the
  point-height dictionary (P2) is incompatible with F4bα ∧ F4bβ.  The
  H-layer reduction theorems remain valid implications; the pointwise
  existential `ABCFrontierPointwiseReduced` is empty, and the faithful
  pointwise route is the two-sided `(1 + ε)`-weight form already carried by
  F5d in the gap frontier.

Source-side anchors (read-only): `Cor312ComparisonGapSupplyLayer.lean:185`
supplies the singleton comparison from the point-level degree dictionary, and
`Cor312GapDictionaryLayer.lean` parks both remaining dictionaries with
counterexamples and maximal fragments.
-/

namespace LeanFormal.IUT

noncomputable section

universe u

/-! ## 1. The singleton refinement of F4b -/

/-- Sub-clause F4bα: the gap-1 weight comparison at its minimal carrier, the
scaled named point (`Cor312ComparisonGapReduction.lean:494-501`), at the
`ENNReal` level: `ofReal (arithmeticWeight x) ≤ logVolume {scaleShift point}`.
This is the exact hypothesis of
`cor312Gap1_weight_le_normalizedRegionVolume_of_singletonVolume` (`:502`).

Consumer: `ABCFrontier.reduce_weightRegionInputs`.
Tree status: no abstract supply.  At the value-realized source interface the
singleton comparison is supplied by
`cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary`
(`Cor312ComparisonGapSupplyLayer.lean:185`) from the point-level degree
dictionary `arithmeticWeight x ≤ sourceLocalLogDegree v (λ * p)`; that
dictionary is parked, with obstructions and counterexamples, in
`ABCBridge/Bridge/Cor312GapDictionaryLayer.lean`.
Attack surface: the singleton weight/point-volume comparison at the source
carrier.
Upgrade condition: land the degree dictionary at the source layer. -/
def FrontierSingletonWeightVolumeClause {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) : Prop :=
  ∀ (ε : Real) (hε : 0 < ε) (a b c : Nat), IsABCTriple a b c →
    ENNReal.ofReal (arithmeticWeight (abcRationalPoint a c)) ≤
      W.logVolume {W.scaleShift (point ε hε a b c)}

/-- Sub-clause F4bβ: finiteness of the comparison-region log-volume.  The
docstring of `:502` records that the `.toReal` form of the gap-1 weight input
additionally needs this finiteness, available at the value-realized source
carrier but not at the abstract interface, where `logVolume` may be `⊤` on the
point part.

Consumer: `ABCFrontier.reduce_weightRegionInputs`.
Tree status: proved at the value-realized source carrier
(`Cor312ComparisonGapSupplyLayer.lean:213-229`, through union subadditivity of
the source set volume and finiteness of the scaled unit region); no abstract
supply — the interface carries no union-subadditivity field
(`SourceHullCompactnessReduction.lean:52-81`) and the point part may be `⊤`
(`Cor312PointwiseResidualSupply.lean:47-52`).
Attack surface: region finiteness from part finiteness plus subadditivity.
Upgrade condition: supply the subadditivity/part-finiteness route at the
interface used by the carrier realization. -/
def FrontierRegionFinitenessClause {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) : Prop :=
  ∀ (ε : Real) (hε : 0 < ε) (a b c : Nat), IsABCTriple a b c →
    W.logVolume (normalizedComparisonRegion W (point ε hε) a b c) ≠ ⊤

/-- **Implemented refinement slot `ABCFrontier.reduce_weightRegionInputs`.**
F4b from F4bα and F4bβ: lift the singleton comparison to the region by
monotonicity (`:502`), then descend to the `.toReal` form using region
finiteness (`ENNReal.toReal_mono` and `ENNReal.toReal_ofReal`). -/
theorem ABCFrontier.reduce_weightRegionInputs {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X)
    (hsingle : FrontierSingletonWeightVolumeClause W point)
    (hfin : FrontierRegionFinitenessClause W point) :
    FrontierWeightRegionClause W point := by
  intro ε hε a b c habc
  have h1 := cor312Gap1_weight_le_normalizedRegionVolume_of_singletonVolume W (point ε hε)
    (fun a b c habc => hsingle ε hε a b c habc) a b c habc
  have h2 := ENNReal.toReal_mono (hfin ε hε a b c habc) h1
  rwa [ENNReal.toReal_ofReal (arithmeticWeight_nonneg _)] at h2

/-! ## 2. The refined gap frontier -/

/-- The refined gap frontier: F4b replaced by F4bα
(`FrontierSingletonWeightVolumeClause`) and F4bβ
(`FrontierRegionFinitenessClause`); sufficient for `ABCFrontier` by
`ABCFrontier.reduce_gapReductionInputsV2`. -/
def ABCFrontierGapReducedV2 : Prop :=
  ∃ (X : Type u) (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X),
    FrontierHeightWeightClause ∧ FrontierSingletonWeightVolumeClause W point ∧
      FrontierRegionFinitenessClause W point ∧ FrontierUnitNormalizationClause W ∧
      FrontierSplitClause W point ∧ FrontierPointFinitenessClause W point ∧
      FrontierPointVolumeWeightClause W point

/-- **Implemented reduction slot `ABCFrontier.reduce_gapReductionInputsV2`.**
The F4b-refined gap frontier implies `ABCFrontier`: reassemble F4b through
`ABCFrontier.reduce_weightRegionInputs` and apply the H-layer reduction. -/
theorem ABCFrontier.reduce_gapReductionInputsV2 :
    ABCFrontierGapReducedV2.{u} → ABCFrontier.{u} := by
  rintro ⟨X, W, point, hhw, hsingle, hfin, hunit, hsplit, hptfin, hpoint⟩
  exact ABCFrontier.reduce_gapReductionInputs.{u}
    ⟨X, W, point, hhw, ABCFrontier.reduce_weightRegionInputs W point hsingle hfin,
      hunit, hsplit, hptfin, hpoint⟩

/-- Composed chain of the refined gap slot: the F4b-refined frontier assembles
the frozen interface field by field. -/
def bridgeInterface_of_frontierGapReducedV2 (h : ABCFrontierGapReducedV2.{u}) :
    Cor312ToABCBridgeInterface.{u} :=
  bridgeInterface_of_frontier.{u} (ABCFrontier.reduce_gapReductionInputsV2.{u} h)

/-- Composed chain of the refined gap slot: the F4b-refined frontier closes ABC
through `abcConjecture_of_frontier`.  Conditional by construction; no
sub-clause is proved at a source carrier. -/
theorem abcConjecture_of_frontierGapReducedV2 (h : ABCFrontierGapReducedV2.{u}) :
    ABCConjecture :=
  abcConjecture_of_frontier.{u} (ABCFrontier.reduce_gapReductionInputsV2.{u} h)

/-! ## 3. Refutation of the two pointwise absorptions -/

/-- **The membership absorption (P1) is refuted.**  At any interface, the
unit-region membership of the point map on all ABC triples is incompatible
with the weight comparison: membership collapses the comparison region to the
scaled unit region (finite volume, `unitRegion_logVolume_lt_top`), while the
arithmetic weights are unbounded
(`iqCarrierModel_hmem_hweightvol_incompatible`,
`IQCarrierConcreteModel.lean:531`, with
`iqCarrierModel_arithmeticWeight_unbounded`, `:495`).  `ABCFrontierPointwiseReduced`
contains both `FrontierUnitMembershipClause` (P1) and `FrontierWeightRegionClause`
(F4b) at the same carrier and point, so no witness inhabits it.  The reduction
theorem `ABCFrontier.reduce_pointwiseResidual` remains a valid implication;
the pointwise existential is empty, and only the gap layer — through its
refined form `ABCFrontierGapReducedV2` — is attackable. -/
theorem not_ABCFrontierPointwiseReduced : ¬ ABCFrontierPointwiseReduced.{u} := by
  rintro ⟨X, W, point, hhw, hwv, hunit, hmem, hvolheight⟩
  have hε : (0 : Real) < 1 / 2 := by norm_num
  exact (iqCarrierModel_hmem_hweightvol_incompatible W
      (fun a b c => point (1 / 2) hε a b c)
      (fun a b c habc => hmem (1 / 2) hε a b c habc))
    (fun a b c habc => hwv (1 / 2) hε a b c habc)

/-- **The point-height absorption (P2) is incompatible with the F4b
refinement.**  For every interface and point map, F4bα together with F4bβ and
the point-height clause is unsatisfiable: finiteness turns F4bα into the real
bound `arithmeticWeight x ≤ (logVolume {scaleShift p}).toReal`, P2 bounds the
same truncated singleton volume by `logHeight₁`, and the two together would
force `log 6 ≤ log 3` at the triple `(1, 2, 3)` — the pure arithmetic
obstruction `iqCarrierModel_no_singleMap_bothDictionaries`
(`IQCarrierConcreteModel.lean:473`; at the value-realized carrier the same
obstruction is recorded by `iqCarrierModel_valueCarrier_no_jointDictionaries`,
`:617`).  The faithful pointwise route must therefore use the two-sided
`(1 + ε)`-weight form carried by F5d in the gap frontier, not the `D₁ = 0`
dictionary route. -/
theorem not_frontierSingletonWeight_finiteness_pointHeight
    {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) :
    ¬ (FrontierSingletonWeightVolumeClause W point ∧
      FrontierRegionFinitenessClause W point ∧ FrontierPointHeightClause W point) := by
  rintro ⟨hsingle, hfin, hvolheight⟩
  have hε : (0 : Real) < 1 / 2 := by norm_num
  refine iqCarrierModel_no_singleMap_bothDictionaries
    (fun a b c => (W.logVolume {W.scaleShift (point (1 / 2) hε a b c)}).toReal) ?_
  intro a b c habc
  constructor
  · have hVle : W.logVolume {W.scaleShift (point (1 / 2) hε a b c)} ≤
        W.logVolume (normalizedComparisonRegion W (point (1 / 2) hε) a b c) := by
      refine W.logVolume_mono ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ⟨point (1 / 2) hε a b c, Set.mem_union_right _ (Set.mem_singleton _), rfl⟩
    have hVne : W.logVolume {W.scaleShift (point (1 / 2) hε a b c)} ≠ ⊤ := by
      intro htop
      have htop' : W.logVolume (normalizedComparisonRegion W (point (1 / 2) hε) a b c) = ⊤ :=
        (le_antisymm
          (show (⊤ : ENNReal) ≤
              W.logVolume (normalizedComparisonRegion W (point (1 / 2) hε) a b c) by
            rw [← htop]
            exact hVle)
          le_top).symm
      exact hfin (1 / 2) hε a b c habc htop'
    have h1 := ENNReal.toReal_mono hVne (hsingle (1 / 2) hε a b c habc)
    rwa [ENNReal.toReal_ofReal (arithmeticWeight_nonneg _)] at h1
  · exact hvolheight (1 / 2) hε a b c habc

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the singleton refinement of F4b and the refutation of the
two pointwise absorptions
(`ABCBridge/Bridge/ABCFrontierSingletonReduction.lean`). -/
def abcFrontierSingletonRefinementLedger : Obligation :=
  { id := "IUT-III.cor312-to-ABC-frontier-singleton-refinement"
    source :=
      "IUT III Corollary 3.12; IUT IV section 2; the gap-1 weight input of " ++
        "ABCBridge/Bridge/Cor312ComparisonGapReduction.lean:494-515"
    status := VerificationStatus.interface
    note :=
      "F4b refines to F4bα (FrontierSingletonWeightVolumeClause, the " ++
        "singleton ENNReal comparison) plus F4bβ (FrontierRegionFinitenessClause, " ++
        "region finiteness); ABCFrontier.reduce_weightRegionInputs reassembles " ++
        "F4b, and ABCFrontierGapReducedV2 -> ABCFrontier -> interface -> ABC is " ++
        "proved.  The two pointwise absorptions of the H layer are refuted: P1 " ++
        "(membership) is incompatible with the weight comparison at any " ++
        "interface (iqCarrierModel_hmem_hweightvol_incompatible, " ++
        "IQCarrierConcreteModel.lean:531), so not_ABCFrontierPointwiseReduced " ++
        "holds; and F4bα with F4bβ is incompatible with P2 (point-height " ++
        "dictionary) via iqCarrierModel_no_singleMap_bothDictionaries (:473).  " ++
        "The H-layer reductions remain valid implications; the pointwise " ++
        "existential is empty, and the faithful pointwise route is the " ++
        "two-sided (1 + eps)-weight form already carried by F5d.  No sub-clause " ++
        "is proved at a source carrier; ABC remains open."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-frontier-reduction",
        "IUT-III.cor312-comparison-gap-reduction",
        "IUT-III.cor312-pointwise-residual-supply",
        "ABC.proof-target" ] }

end LeanFormal.IUT.Audit
