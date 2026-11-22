import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.UnprovedTarget

/-!
# The ABC frontier: the explicit enemy and its weakening protocol

`Cor312ToABCBridgeInterface`
(`ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:404`) is the machine-checkable
frontier of the ABC bridge: its conditional closure
`cor312ToABCBridge_abcConjecture` (`:446`) derives `ABCConjecture` from an
inhabitant `D`, and the interface has exactly ABC's strength
(`cor312ToABCBridgeInterface_nonempty_iff_abcConjecture`, `:605`).  This module
re-expresses the interface field by field as the named proposition `ABCFrontier`,
so that each attack round can weaken the frontier in a machine-checkable way
while the chain `ABCFrontier → Cor312ToABCBridgeInterface → ABCConjecture` stays
intact.  Nothing in the interface file is restated or modified.

## The clauses (minimal sufficient supply per field of `D`)

| clause (anchor) | status | attack line |
| --- | --- | --- |
| F1 `carrier` (:406) | fixture supply proved (:521); paper open (:639) | StepXI IQ-carrier |
| F2 `hullData` (:408) | supplies proved (:521, SHCR:112); paper hull open | SourceHull/Haar |
| F3a `logShellPoint` (:230) | data; fixture `c ↦ Real.log c` (:545); paper open | source-facing |
| F4 gap 1 (:236-239) | OPEN paper link (IUT IV sec. 2); no card id | GapReduction :198/:232/:557 |
| F5 gap 2 (:248-251) | OPEN (IUT IV sec. 2 main est.); no card id | GapReduction :306/:367 |

Minimal supplies: F1 any type; F2 the 10-field hull interface; F3a a named point
datum; F4 and F5 are the two displayed shapes (details in each clause below).

Current enemy (one line): the arithmetic content of the frontier is exactly the
two comparison clauses F4 and F5; F1, F2, F3a are data clauses, freely choosable
for the implication `D → ABCConjecture` (the fixture supplies show they are
satisfiable; their paper fidelity is a separate source-facing obligation that
this chain does not require).  The final arithmetic target card remains
`ABC.proof-target` (`UnprovedTarget.lean`).

## Theorems

* `bridgeInterface_of_frontier : ABCFrontier → Cor312ToABCBridgeInterface`,
  field by field.  Existential witnesses are extracted with the standard
  `Classical.choice` pattern (as in `Nonempty.some`); the declaration is a `def`,
  not a `theorem`, because the target is data.
* `abcConjecture_of_frontier : ABCFrontier → ABCConjecture`, through `:446`.
* `abcFrontier_iff_abcConjecture : ABCFrontier.{0} ↔ ABCConjecture` (the
  calibration instantiation, as in `:606`): the frontier contains exactly ABC's
  strength, mirroring `:605` at the clause level.

## Weakening protocol

Do not edit a closed clause.  When an attack round supplies some clauses with
proved data, define a new proposition `ABCFrontier<Name>` whose free clauses are
the strict residual subset at the fixed supplies, prove
`theorem ABCFrontier.reduce_<name> : ABCFrontier<Name> → ABCFrontier`, and keep
`ABCFrontier<Name> → ABCConjecture` by composition; every reduction theorem must
land together with its composed chain.  Naming: reduction theorems
`ABCFrontier.reduce_*`; reduced frontiers `ABCFrontier` + fixture name (worked
example `ABCFrontierRealLine` below).

Worked example (`ABCFrontier.reduce_realLine`): on the calibration carrier
`realLineHullData` with the point datum `c ↦ Real.log c`, the clauses F1, F2, F3a
and F4 are closed by proved supplies (`realLineFrontier_heightComparison`), so
the reduced frontier `ABCFrontierRealLine` is the single clause F5 at the
fixture.  The reduction is tight: `abcFrontierRealLine_iff_abcConjecture` shows
the residual clause still has exactly ABC's strength, so the protocol loses no
content on this fixture.

Implemented reductions (in `ABCBridge/Bridge/ABCFrontierReductions.lean`, the
companion module of this file; each keeps the chain `reduced → ABCFrontier →
Cor312ToABCBridgeInterface → ABCConjecture` intact):

* `ABCFrontier.reduce_gapReductionInputs`: F4 is factored into
  `FrontierHeightWeightClause` (height vs weight) and
  `FrontierWeightRegionClause` (weight vs region volume); F5 is replaced by
  `FrontierUnitNormalizationClause`, `FrontierSplitClause`,
  `FrontierPointFinitenessClause` and `FrontierPointVolumeWeightClause` through
  `cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound`
  (`ABCBridge/Bridge/Cor312ComparisonGapReduction.lean:306`).  The previously
  reserved route through `cor312GapAssembly_epsilonComparisonOfReducedInputs`
  (`:367`) is not used: its `hval` input is refuted
  (`ABCHeightArithmeticWeightComparison.lean:140`);
* `ABCFrontier.reduce_pointwiseResidual`: `hsplit` and `hptfin` are absorbed by
  the membership datum `FrontierUnitMembershipClause` (`:409`, `:432`), and
  `hpoint` by `FrontierPointHeightClause` composed with the height/weight
  clause (`:455`, with `D₁ = 0`), yielding `ABCFrontierPointwiseReduced`.

Both reductions are sufficient factorizations: the reduced conjunction implies
the clause it supports, so the enemy is finer-grained per sub-clause; no
strength reduction is claimed (see the honest boundary below).

## Honest boundary

This module proves no new source-level mathematics.  The fixture closures are
elementary computations on the calibration carrier
(`Cor312ToABCBridgeInterface.lean:521`), a strength-check artifact and not the
paper carrier; the paper-literal carrier, the paper-faithful hull and the two
IUT IV comparison clauses remain open.  `abcConjecture_of_frontier` is
conditional by construction; ABC is not proved here.  The reduced frontiers of
the companion module `ABCBridge/Bridge/ABCFrontierReductions.lean` are
sufficient factorizations, not fixture-tight equivalences: the calibration
fixture does not inhabit them (its weight/region sub-clause fails there,
`Cor312ComparisonGapReduction.lean:232`), and no sub-clause is claimed at a
source-faithful carrier.
-/

namespace LeanFormal.IUT

noncomputable section

universe u

/-! ## 1. Frontier clauses -/

/-- Frontier clause F4: the height comparison of `D.epsilonComparison`.

Field: `Cor312ToABCBridgeInterface.epsilonComparison` →
`Cor312EpsilonArithmeticComparison.height_le_normalizedRegionVolume`
(field anchors `Cor312ToABCBridgeInterface.lean:410-411` → `:236-239`; the
version-2 additive form is `:326-329`).

Status: open paper link (the `ε`-normalized comparison of the height with the
comparison-region log-volume, IUT IV §2); no registered card id supplies the
clause.  Recent attack lines:

* conditional reduction from the proved H1 valuation-bound reduction plus the
  named weight comparison:
  `cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound`
  (`ABCBridge/Bridge/Cor312ComparisonGapReduction.lean:198`);
* the named weight comparison is refuted in general on the calibration carrier
  at the triple `(1, 2, 3)`:
  `cor312Gap1_exists_carrier_arithmeticWeight_gt_normalizedComparisonRegionVolume`
  (`:232`), `cor312Gap1_not_forall_arithmeticWeight_le_normalizedComparisonRegionVolume`
  (`:272`);
* singleton-volume route
  `cor312Gap1_weight_le_normalizedRegionVolume_of_singletonVolume` (`:502`);
  additive route `cor312Gap1_height_le_normalizedRegionVolume_of_additiveBound`
  (`:557`); value-realized supply
  `cor312GapSupply_sourceGap1_of_valuationBound_degreeDictionary`
  (`Cor312ComparisonGapSupplyLayer.lean:247`);
* additive re-freeze v2 (`Cor312ToABCBridgeInterface.lean:298-335`; consumer
  `:348`; contract `ABCHeightArithmeticWeightComparison.lean:158`, equivalence
  `:167`);
* fixture closure on the calibration carrier: `realLineFrontier_heightComparison`
  (this file). -/
def FrontierHeightComparisonClause {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) : Prop :=
  ∀ (ε : Real) (hε : 0 < ε) (a b c : Nat), IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + ε) * (W.logVolume (normalizedComparisonRegion W (point ε hε) a b c)).toReal

/-- Frontier clause F5: the region-volume computation of `D.epsilonComparison`.

Field: `Cor312ToABCBridgeInterface.epsilonComparison` →
`Cor312EpsilonArithmeticComparison.regionVolume_le_normalizedWeight`
(field anchors `Cor312ToABCBridgeInterface.lean:410-411` → `:248-251`).

Status: open paper link (the main log-volume estimate of IUT IV §2, conditional
on the Corollary 3.12 finiteness of the theta-pilot hull bound); no registered
card id supplies the clause.  Recent attack lines:

* reduced five-input form
  `cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound`
  (`ABCBridge/Bridge/Cor312ComparisonGapReduction.lean:306`) and the assembly
  into the exact `D` field `cor312GapAssembly_epsilonComparisonOfReducedInputs`
  (`:367`);
* round-2 partial discharges: `hsplit` and `hptfin` follow from the single
  unit-region membership datum (`:409`, `:432`); value-realized `hsplit`/`hptfin`
  (`Cor312ComparisonGapSupplyLayer.lean:127`, `:152`); pointwise residual
  (`Cor312PointwiseResidualSupply.lean:359`, `:369`, `:409`); spike-carrier
  independence of `hptfin` (`:171`);
* additive-bound forms (`Cor312ComparisonGapReduction.lean:579`, `:599`). -/
def FrontierRegionComparisonClause {X : Type u} (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) : Prop :=
  ∀ (ε : Real) (hε : 0 < ε), ∃ D : Real, ∀ (a b c : Nat), IsABCTriple a b c →
    (W.logVolume (normalizedComparisonRegion W (point ε hε) a b c)).toReal ≤
      (1 + ε) * arithmeticWeight (abcRationalPoint a c) + (W.logVolume W.hull).toReal + D

/-- **The explicit enemy.**  The minimal sufficient supply conjunction for the
fields of `Cor312ToABCBridgeInterface` (`:404`): the ambient carrier F1, the
hull/log-volume interface F2, the named point datum F3a, and the two comparison
clauses F4 (`FrontierHeightComparisonClause`) and F5
(`FrontierRegionComparisonClause`).  Clause statuses, anchors and attack lines
are in the module documentation and at each clause definition.  By
`abcFrontier_iff_abcConjecture` this proposition has exactly the strength of
`ABCConjecture`. -/
def ABCFrontier : Prop :=
  ∃ (X : Type u) (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X),
    FrontierHeightComparisonClause W point ∧ FrontierRegionComparisonClause W point

/-! ## 2. Assembly: frontier → `D` → ABC -/

/-- Field-by-field assembly of the frozen bridge interface from the frontier:
F1 supplies `carrier`, F2 supplies `hullData`, F3a supplies each per-`ε`
`logShellPoint`, and F4, F5 supply the two comparison fields.  The existential
witnesses are extracted with the standard `Classical.choice` pattern (as in
`Nonempty.some`); the declaration is a `def` because the target is data. -/
def bridgeInterface_of_frontier (h : ABCFrontier) : Cor312ToABCBridgeInterface :=
  let hclauses := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))
  { carrier := Classical.choose h
    hullData := Classical.choose (Classical.choose_spec h)
    epsilonComparison := fun ε hε =>
      { logShellPoint :=
          Classical.choose (Classical.choose_spec (Classical.choose_spec h)) ε hε
        height_le_normalizedRegionVolume := hclauses.1 ε hε
        regionVolume_le_normalizedWeight := hclauses.2 ε hε } }

/-- **Conditional closure of the frontier.**  Through the proved assembly and
`cor312ToABCBridge_abcConjecture` (`Cor312ToABCBridgeInterface.lean:446`), an
inhabitant of the frontier yields `ABCConjecture`.  Conditional by construction;
no clause of the frontier is proved here. -/
theorem abcConjecture_of_frontier (h : ABCFrontier) : ABCConjecture :=
  cor312ToABCBridge_abcConjecture (bridgeInterface_of_frontier h)

/-! ## 3. Weakening protocol: the calibration-fixture reduction -/

/-- Fixture point datum for the calibration carrier: the image point of `x = a/c`
is the height value `Real.log c` itself (the choice of the strength witness
`Cor312ToABCBridgeInterface.lean:545`).  Data, not a claim. -/
def realLineFrontierPoint : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → Real :=
  fun _ _ _ _ c => Real.log (c : Real)

/-- **Fixture closure of F4.**  On the calibration carrier `realLineHullData`
(`Cor312ToABCBridgeInterface.lean:521`) with point datum `realLineFrontierPoint`,
the height comparison holds: the comparison-region log-volume is exactly
`ofReal (Real.log c)` (`realLineLogVolume_pair_zero`, `:508`), so F4 reduces to
`Real.log c ≤ (1 + ε) * Real.log c`, which holds since `0 ≤ Real.log c` on ABC
triples.  This is the proved supply closing F4 in the worked reduction
`ABCFrontier.reduce_realLine` below; it is an elementary computation on the
calibration artifact, not the paper comparison. -/
theorem realLineFrontier_heightComparison :
    FrontierHeightComparisonClause realLineHullData realLineFrontierPoint := by
  intro ε hε a b c habc
  have hc1 : (1 : Real) ≤ (c : Real) := by
    have h1 : 1 ≤ c := by
      obtain ⟨ha, hb, hsum, _⟩ := habc
      omega
    exact_mod_cast h1
  have hlogc : 0 ≤ Real.log (c : Real) := Real.log_nonneg hc1
  have hvol : realLineLogVolume (realLineHullData.scaleShift ''
      (realLineHullData.unitRegion ∪ {Real.log (c : Real)})) =
      ENNReal.ofReal (Real.log (c : Real)) := by
    change realLineLogVolume (id '' (({0} : Set Real) ∪ {Real.log (c : Real)})) =
      ENNReal.ofReal (Real.log (c : Real))
    rw [Set.image_id, Set.singleton_union]
    exact realLineLogVolume_pair_zero hlogc
  change Height.logHeight₁ (abcRationalPoint a c) ≤
    (1 + ε) * (realLineLogVolume (realLineHullData.scaleShift ''
      (realLineHullData.unitRegion ∪ {Real.log (c : Real)}))).toReal
  rw [hvol, ENNReal.toReal_ofReal hlogc, abcRationalPoint_logHeight₁ habc]
  nlinarith [hε.le, hlogc]

/-- The reduced frontier `ABCFrontierRealLine`: the calibration fixture fixes F1
(`Real`), F2 (`realLineHullData`), F3a (`realLineFrontierPoint`) and F4
(proved in `realLineFrontier_heightComparison`); the single free clause is F5 at
the fixture.  First ledger entry of the weakening protocol; its reduction
theorem is `ABCFrontier.reduce_realLine` below. -/
def ABCFrontierRealLine : Prop :=
  FrontierRegionComparisonClause realLineHullData realLineFrontierPoint

/-- **Reduction theorem (weakening protocol).**  The reduced frontier implies
the full frontier: F1, F2, F3a are supplied by the fixture, F4 by the proved
`realLineFrontier_heightComparison`, and F5 is the residual hypothesis.  The
composed chain `ABCFrontierRealLine → ABCConjecture` is
`abcConjecture_of_frontierRealLine` below; the reduction is tight by
`abcFrontierRealLine_iff_abcConjecture`. -/
theorem ABCFrontier.reduce_realLine : ABCFrontierRealLine → ABCFrontier.{0} := by
  intro hregion
  exact ⟨Real, realLineHullData, realLineFrontierPoint,
    realLineFrontier_heightComparison, hregion⟩

/-- The fixture residual is not weaker than ABC: from `ABCConjecture`, the
height bound of `abcConjecture_iff_abcArithmeticWeightHeightBound`
(`IUTToABC.lean:64`) converts into the F5 shape at the fixture with
`D = max A 0` (the computation of the strength witness
`Cor312ToABCBridgeInterface.lean:538-593`). -/
theorem abcFrontierRealLine_of_abcConjecture (h : ABCConjecture) : ABCFrontierRealLine := by
  intro ε hε
  obtain ⟨A, hA⟩ := (abcConjecture_iff_abcArithmeticWeightHeightBound.mp h) ε hε
  refine ⟨max A 0, ?_⟩
  intro a b c habc
  have hc1 : (1 : Real) ≤ (c : Real) := by
    have h1 : 1 ≤ c := by
      obtain ⟨ha, hb, hsum, _⟩ := habc
      omega
    exact_mod_cast h1
  have hlogc : 0 ≤ Real.log (c : Real) := Real.log_nonneg hc1
  have hvol : realLineLogVolume (realLineHullData.scaleShift ''
      (realLineHullData.unitRegion ∪ {Real.log (c : Real)})) =
      ENNReal.ofReal (Real.log (c : Real)) := by
    change realLineLogVolume (id '' (({0} : Set Real) ∪ {Real.log (c : Real)})) =
      ENNReal.ofReal (Real.log (c : Real))
    rw [Set.image_id, Set.singleton_union]
    exact realLineLogVolume_pair_zero hlogc
  change (realLineLogVolume (realLineHullData.scaleShift ''
      (realLineHullData.unitRegion ∪ {Real.log (c : Real)}))).toReal ≤
    (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
      (realLineLogVolume (∅ : Set Real)).toReal + max A 0
  rw [hvol, ENNReal.toReal_ofReal hlogc, realLineLogVolume_empty, ENNReal.toReal_zero]
  have hA' := hA a b c habc
  rw [abcRationalPoint_logHeight₁ habc] at hA'
  linarith [le_max_left A 0]

/-- The fixture residual is not stronger than ABC: from the single F5 clause at
the fixture, the height bound holds with `A = D` (the fixture region volume is
`ofReal (Real.log c)` and the hull term vanishes), so `ABCConjecture` follows
through the accepted equivalence. -/
theorem abcConjecture_of_frontierRealLine (h : ABCFrontierRealLine) : ABCConjecture :=
  abcConjecture_iff_abcArithmeticWeightHeightBound.mpr fun ε hε => by
    obtain ⟨D, hD⟩ := h ε hε
    refine ⟨D, fun a b c habc => ?_⟩
    have hc1 : (1 : Real) ≤ (c : Real) := by
      have h1 : 1 ≤ c := by
        obtain ⟨ha, hb, hsum, _⟩ := habc
        omega
      exact_mod_cast h1
    have hlogc : 0 ≤ Real.log (c : Real) := Real.log_nonneg hc1
    have hvol : realLineHullData.logVolume
        (normalizedComparisonRegion realLineHullData (realLineFrontierPoint ε hε) a b c) =
        ENNReal.ofReal (Real.log (c : Real)) := by
      change realLineLogVolume (id '' (({0} : Set Real) ∪ {Real.log (c : Real)})) =
        ENNReal.ofReal (Real.log (c : Real))
      rw [Set.image_id, Set.singleton_union]
      exact realLineLogVolume_pair_zero hlogc
    have hhull : realLineHullData.logVolume realLineHullData.hull = 0 := by
      change realLineLogVolume (∅ : Set Real) = 0
      exact realLineLogVolume_empty
    have hbound := hD a b c habc
    rw [hvol, ENNReal.toReal_ofReal hlogc, hhull, ENNReal.toReal_zero] at hbound
    rw [abcRationalPoint_logHeight₁ habc]
    linarith

/-- **Tightness of the fixture reduction.**  The reduced frontier
`ABCFrontierRealLine` is equivalent to `ABCConjecture`: the worked weakening
removes exactly the fixture-closed clauses and no arithmetic content. -/
theorem abcFrontierRealLine_iff_abcConjecture :
    ABCFrontierRealLine ↔ ABCConjecture :=
  ⟨abcConjecture_of_frontierRealLine, abcFrontierRealLine_of_abcConjecture⟩

/-! ## 4. Frontier calibration -/

/-- The frontier is not stronger than ABC: from `ABCConjecture` the fixture
(proved F4 together with the F5 clause supplied by
`abcFrontierRealLine_of_abcConjecture`) inhabits `ABCFrontier`. -/
theorem abcFrontier_of_abcConjecture (h : ABCConjecture) : ABCFrontier.{0} :=
  ⟨Real, realLineHullData, realLineFrontierPoint, realLineFrontier_heightComparison,
    abcFrontierRealLine_of_abcConjecture h⟩

/-- **Frontier calibration.**  `ABCFrontier` is inhabited if and only if
`ABCConjecture` holds: the frontier contains exactly the unproved arithmetic
content, mirroring `cor312ToABCBridgeInterface_nonempty_iff_abcConjecture`
(`Cor312ToABCBridgeInterface.lean:605`) at the clause level. -/
theorem abcFrontier_iff_abcConjecture : ABCFrontier.{0} ↔ ABCConjecture :=
  ⟨abcConjecture_of_frontier, abcFrontier_of_abcConjecture⟩

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the ABC frontier ledger of
`ABCBridge/Bridge/ABCFrontier.lean`.  The record exposes the enemy as the named
proposition `ABCFrontier` (clauses F1-F5 of the bridge interface) and the
weakening protocol; it does not assert that any clause is closed at source
level or that ABC is proved. -/
def abcFrontierLedger : Obligation :=
  { id := "IUT-III.cor312-to-ABC-frontier-ledger"
    source :=
      "IUT III Corollary 3.12; IUT IV section 2 comparison; the frozen interface " ++
        "Cor312ToABCBridgeInterface of ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean:404"
    status := VerificationStatus.interface
    note :=
      "The ABC frontier is re-expressed as ABCFrontier = F1 carrier and F2 hull " ++
        "interface and F3a point datum and F4 height comparison and F5 " ++
        "region-volume comparison; bridgeInterface_of_frontier assembles the frozen " ++
        "interface field by field and abcConjecture_of_frontier closes ABC through " ++
        "cor312ToABCBridge_abcConjecture.  The frontier has exactly ABC's strength " ++
        "(abcFrontier_iff_abcConjecture).  The weakening protocol is instantiated by " ++
        "the calibration fixture: reduce_realLine shows ABCFrontierRealLine (the " ++
        "single residual clause F5 at realLineHullData with point c maps to Real.log c) " ++
        "implies ABCFrontier, with tightness abcFrontierRealLine_iff_abcConjecture.  " ++
        "NOT proved: F4 and F5 at any source-faithful carrier, the paper-literal " ++
        "carrier, the paper-faithful hull, and any unconditional closure."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface",
        "IUT-III.cor312-to-ABC",
        "ABC.proof-target" ] }

end LeanFormal.IUT.Audit
