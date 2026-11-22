import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierReductions
import LeanFormal.IUT.ABCBridge.Bridge.Cor312PointwiseResidualSupply
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierConcreteModel

/-!
# P1 premise evaluation: the unit-membership datum of the pointwise frontier

Three-route evaluation of `FrontierUnitMembershipClause` (P1,
`ABCBridge/Bridge/ABCFrontierReductions.lean:199`), the unique premise of the
`hsplit` / `hptfin` rewirings consumed by `ABCFrontier.reduce_pointwiseResidual`
(`:273`).  The leaf proves the clause-level absorption, refutes the reverse
absorption, rebases the value-realized supply to the clause shapes, and derives
the frontier-level exclusion.

## Anchor correction

The task anchors `ABCFrontierReductions.lean:409/:432`; that file has 365 lines
and those citations are its own cross-references into
`Cor312ComparisonGapReduction.lean:409-426`
(`cor312Gap2_hsplit_of_mem_unitRegion`) and `:432-445`
(`cor312Gap2_hptfin_of_mem_unitRegion`).  All statements below are against the
actual declarations at those anchors.

## Route accounting (three routes, all attempted)

* Route A (contract absorption, abstract layer) -- proved: P1 implies
  `FrontierSplitClause` and `FrontierPointFinitenessClause`
  (`frontierSplitClause_of_unitMembership`,
  `frontierPointFinitenessClause_of_unitMembership`); the reverse absorption
  fails, refuted by the zero carrier
  (`frontierSplit_and_pointFiniteness_not_imply_unitMembership`).
* Route B (value-realized carrier, clause shapes) -- proved, conditional on the
  StepXI data: the unconditional supply-layer theorems rebased to the exact
  frontier-clause operands at the source interface
  (`frontierSplitClause_sourceInterface`,
  `frontierPointFinitenessClause_sourceInterface`).  P1 membership itself has
  no source-layer supply; see the exclusion.
* Route C (counterexample audit) -- proved negative results: P1 alone is
  satisfiable (spike carrier, point `0`; `frontierUnitMembership_satisfiable`),
  while P1 is incompatible with the weight/region conjunct of its own consumer
  frontier: membership collapses the comparison region to the scaled unit
  region, whose log-volume is finite, whereas the arithmetic weights are
  unbounded (`frontierUnitMembership_weightRegionClause_exclusive`, from
  `iqCarrierModel_hmem_hweightvol_incompatible`,
  `IQCarrierConcreteModel.lean:531`).  Consequently
  `abcFrontierPointwiseReduced_not_inhabited`: the pointwise frontier has no
  inhabitant, so `reduce_pointwiseResidual` (`:273`) and
  `abcConjecture_of_frontierPointwiseReduced` (`:313`) are valid but vacuous.
  P1 cannot be supplied in this consumer shape, at any carrier.

## Residual card for P1

P1 stays unproved and is now known to be unprovable in context.  A repair must
either (i) split the point roles -- membership for a shell point distinct from
the volume-carrying comparison point -- or (ii) drop P1 and keep the
`FrontierSplitClause` / `FrontierPointFinitenessClause` pair (the gap-reduced
frontier, not excluded by this argument), whose working orientation keeps the
point outside the shell (`IQCarrierConcreteModel.lean:25`).  No repair decision
is taken here; P2 (`FrontierPointHeightClause`) is outside this file's scope.

## Honesty notes

No source-level mathematics is proved here.  Every statement is about the
frozen abstract interface shapes and reused calibration carriers; the corpus
anchors (IUT III Corollary 3.12, Remark 3.9.5) are inherited from the frozen
files, and the exclusion is an interface-level theorem, not a paper-literal
claim.  No gap field of `Cor312EpsilonArithmeticComparison` is filled.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT

universe u ua uv upi umon ui

noncomputable section

/-! ## 1. Route A: clause-level absorption of the membership datum -/

/-- **Absorption, `hsplit` side.**  P1 implies `FrontierSplitClause` by the
membership rewiring `cor312Gap2_hsplit_of_mem_unitRegion`
(`Cor312ComparisonGapReduction.lean:409`). -/
theorem frontierSplitClause_of_unitMembership {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) :
    FrontierUnitMembershipClause W point → FrontierSplitClause W point :=
  fun hmem ε hε a b c habc =>
    cor312Gap2_hsplit_of_mem_unitRegion W (point ε hε)
      (fun a b c habc => hmem ε hε a b c habc) a b c habc

/-- **Absorption, `hptfin` side.**  P1 implies `FrontierPointFinitenessClause`
by the membership rewiring `cor312Gap2_hptfin_of_mem_unitRegion`
(`Cor312ComparisonGapReduction.lean:432`). -/
theorem frontierPointFinitenessClause_of_unitMembership {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) :
    FrontierUnitMembershipClause W point → FrontierPointFinitenessClause W point :=
  fun hmem ε hε a b c habc =>
    cor312Gap2_hptfin_of_mem_unitRegion W (point ε hε)
      (fun a b c habc => hmem ε hε a b c habc) a b c habc

/-! ## 2. Route C headline: the frontier-level exclusion -/

/-- **P1 and the weight/region clause are jointly impossible.**  Membership of
the named point in the unit region makes the comparison region collapse to the
scaled unit region, whose log-volume is bounded by the carrier normalization
field, so the weight/region comparison would bound the arithmetic weights on
all ABC triples; the weights are unbounded
(`iqCarrierModel_hmem_hweightvol_incompatible`). -/
theorem frontierUnitMembership_weightRegionClause_exclusive {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X) :
    FrontierUnitMembershipClause W point → ¬ FrontierWeightRegionClause W point := by
  intro hmem hweight
  have hε1 : (0 : Real) < 1 := by norm_num
  exact (iqCarrierModel_hmem_hweightvol_incompatible W (point 1 hε1)
      (fun a b c habc => hmem 1 hε1 a b c habc))
    (fun a b c habc => hweight 1 hε1 a b c habc)

/-- The same exclusion in existential form: no carrier and point map realize
the membership and weight/region clauses jointly. -/
theorem frontierUnitMembership_weightRegionClause_not_jointly :
    ¬ (∃ (X : Type u) (W : IQHullLogVolumeInterface X)
        (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X),
        FrontierUnitMembershipClause W point ∧ FrontierWeightRegionClause W point) := by
  rintro ⟨X, W, point, hmem, hweight⟩
  exact frontierUnitMembership_weightRegionClause_exclusive W point hmem hweight

/-- **The pointwise frontier has no inhabitant.**  `ABCFrontierPointwiseReduced`
(`ABCFrontierReductions.lean:243`) contains both the membership clause P1 and
the weight/region clause F4b on the same point map; the exclusion above makes
the conjunction unsatisfiable.  Hence `reduce_pointwiseResidual` (`:273`) and
`abcConjecture_of_frontierPointwiseReduced` (`:313`) are valid implications
with empty premise: the P1 route cannot contribute at the frozen shapes. -/
theorem abcFrontierPointwiseReduced_not_inhabited :
    ¬ ABCFrontierPointwiseReduced.{u} := by
  rintro ⟨X, W, point, -, hweight, -, hmem, -⟩
  exact frontierUnitMembership_weightRegionClause_exclusive W point hmem hweight

/-! ## 3. Route A negative: the reverse absorption fails -/

/-- The zero carrier on the unit type: empty regions, zero log-volume, empty
scaling.  Every `IQHullLogVolumeInterface` field holds; the membership of the
only point in the empty unit region fails. -/
noncomputable def frontierZeroCarrier : IQHullLogVolumeInterface Unit where
  imageSet := ∅
  hull := ∅
  imageSet_subset_hull := Set.empty_subset _
  logVolume := fun _ => 0
  logVolume_mono := fun _ => le_refl 0
  unitRegion := ∅
  scaleShift := id
  hull_subset_scaleShift := Set.empty_subset _
  unitRegion_logVolume_lt_top := ENNReal.zero_lt_top
  scaleShift_unitRegion_logVolume_le := le_refl 0

theorem frontierZeroCarrier_logVolume_eq_zero (S : Set Unit) :
    frontierZeroCarrier.logVolume S = 0 := rfl

theorem frontierZeroCarrier_unitRegion_eq_empty :
    frontierZeroCarrier.unitRegion = ∅ := rfl

theorem frontierZeroCarrier_splitClause :
    FrontierSplitClause frontierZeroCarrier (fun _ _ _ _ _ => ()) := by
  intro ε hε a b c habc
  simp only [frontierZeroCarrier_logVolume_eq_zero]
  exact zero_le

theorem frontierZeroCarrier_pointFinitenessClause :
    FrontierPointFinitenessClause frontierZeroCarrier (fun _ _ _ _ _ => ()) := by
  intro ε hε a b c habc
  simp only [frontierZeroCarrier_logVolume_eq_zero]
  exact ENNReal.zero_lt_top

theorem frontierZeroCarrier_unitMembership_absurd :
    ¬ FrontierUnitMembershipClause frontierZeroCarrier (fun _ _ _ _ _ => ()) := by
  intro hmem
  have hε1 : (0 : Real) < 1 := by norm_num
  have hmem' : (() : Unit) ∈ (∅ : Set Unit) :=
    hmem 1 hε1 1 2 3 ⟨Nat.one_pos, by norm_num, by norm_num, Nat.coprime_one_left 2⟩
  simp at hmem'

/-- **Split plus finiteness do not imply membership.**  The zero carrier makes
`FrontierSplitClause` and `FrontierPointFinitenessClause` hold while the
membership clause fails, so the absorption of Section 1 does not reverse: P1 is
strictly stronger than the pair it absorbs. -/
theorem frontierSplit_and_pointFiniteness_not_imply_unitMembership :
    ¬ (∀ (X : Type) (W : IQHullLogVolumeInterface X)
        (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X),
        FrontierSplitClause W point → FrontierPointFinitenessClause W point →
          FrontierUnitMembershipClause W point) :=
  fun h => frontierZeroCarrier_unitMembership_absurd
    (h Unit frontierZeroCarrier (fun _ _ _ _ _ => ())
      frontierZeroCarrier_splitClause frontierZeroCarrier_pointFinitenessClause)

/-- P1 is not an interface theorem: the zero carrier witnesses that membership
does not follow from the `IQHullLogVolumeInterface` fields alone. -/
theorem frontierUnitMembership_not_interface_theorem :
    ¬ (∀ (X : Type) (W : IQHullLogVolumeInterface X)
        (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → X),
        FrontierUnitMembershipClause W point) :=
  fun h => frontierZeroCarrier_unitMembership_absurd
    (h Unit frontierZeroCarrier (fun _ _ _ _ _ => ()))

/-! ## 4. Route C satisfiability witness: P1 is not a vacuous premise -/

/-- P1 is satisfiable as a standalone statement: on the spike carrier the unit
region is `{0}` and the constant point `0` lies in it.  The membership datum is
therefore non-vacuous; its failure is specifically the incompatibility with the
weight/region conjunct (Section 2). -/
theorem frontierUnitMembership_satisfiable :
    ∃ (W : IQHullLogVolumeInterface ℝ)
      (point : ∀ ε : Real, 0 < ε → Nat → Nat → Nat → ℝ),
      FrontierUnitMembershipClause W point :=
  ⟨cor312Pointwise_spikeCarrier, (fun _ _ _ _ _ => 0),
    fun _ _ _ _ _ _ => Set.mem_singleton 0⟩

/-! ## 5. Route B: the value-realized carrier supplies both clauses -/

namespace Theorem311Source

namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}

variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- **Split clause at the value-realized carrier.**  For the source interface
`I.sourceUnitRegionHaarInterface v R n D` and an `ε`-independent point map,
the exact `hsplit` operand of `ABCFrontier.reduce_pointwiseResidual` holds
unconditionally by the supply-layer theorem
`cor312GapSupply_sourceInterface_hsplit`
(`Cor312ComparisonGapSupplyLayer.lean:127`); conditional only on the StepXI
data `R` and `D`. -/
theorem frontierSplitClause_sourceInterface (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v) :
    FrontierSplitClause (I.sourceUnitRegionHaarInterface v R n D)
      (fun _ _ => p) :=
  fun ε hε a b c habc =>
    I.cor312GapSupply_sourceInterface_hsplit v R n D p a b c habc

/-- **Point-finiteness clause at the value-realized carrier.**  Same rebasing
for the `hptfin` operand, from `cor312GapSupply_sourceInterface_hptfin`
(`Cor312ComparisonGapSupplyLayer.lean:152`). -/
theorem frontierPointFinitenessClause_sourceInterface (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v) :
    FrontierPointFinitenessClause (I.sourceUnitRegionHaarInterface v R n D)
      (fun _ _ => p) :=
  fun _ _ a b c _ => I.cor312GapSupply_sourceInterface_hptfin v R n D p a b c

end OriginalInput

end Theorem311Source

end

end LeanFormal.IUT
