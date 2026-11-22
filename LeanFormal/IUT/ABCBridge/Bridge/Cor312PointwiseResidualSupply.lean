import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapSupplyLayer

/-!
  # Pointwise residual supply for the Corollary 3.12 comparison gap 2
  (`hptfin`, `hpoint`)

  Down-drill of the two pointwise residual inputs of the frozen reduced-input
  interface `ABCBridge/Bridge/Cor312ComparisonGapReduction.lean` (SHA 512DA3E1…,
  imported here, not modified):

  * `hptfin` (`Cor312ComparisonGapReduction.lean:314`, `:381`):
    `W.logVolume {W.scaleShift (logShellPoint a b c)} < ⊤` on ABC triples;
  * `hpoint` (`Cor312ComparisonGapReduction.lean:316`, `:383`):
    `(W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
      (1 + ε) · arithmeticWeight (abcRationalPoint a c) + D₁` on ABC triples.

  ## Corpus anchors

  * IUT III, Corollary 3.12 (corpus text lines 10324-10358): the
    procession-normalized mono-analytic log-volume `−|log(Θ)| ∈ R ∪ {+∞}` of
    the holomorphic hull of the union of the possible images of a Θ-pilot
    object [Remark 3.9.5, (i)].  The `{+∞}` alternative is the exact content
    behind `hptfin`: finiteness of the point volume is a statement to be
    supplied, not a definitional consequence of the carrier fields.
  * IUT IV, Proposition 1.4, (i) (corpus lines 671-682): after normalization
    the log-volume `μlog` is "valued in R" on compact open subsets of the
    relevant tensor products — the finiteness datum behind `hptfin`.
  * IUT IV, Theorem A / Corollary 2.3 (corpus lines 93-105):
    `ht_{ωX(D)} ≲ (1 + ϵ)(log-diffX + log-condD)` — the `(1 + ε)·`-weight
    shape consumed by `hpoint`, supplied arithmetically by the proved H1
    reduction `ABCHeightArithmeticWeightComparison.lean` (DSH-B).
  * Explicit estimates in IUTeich (corpus text line 1609): "explicit
    log-volume estimates" section.

  ## Route accounting

  * `hptfin`, value-realized layer (route R2, closure):
    `cor312Pointwise_sourceInterface_hptfin` rewires the proved
    `cor312GapSupply_sourceInterface_hptfin`
    (`Cor312ComparisonGapSupplyLayer.lean:152-160`) into the exact consumer
    shape of `Cor312ComparisonGapReduction.lean:381`; the singleton volume is
    `ofReal` of the real log-degree, hence finite, with no ABC hypothesis.
  * `hptfin`, abstract layer (route R1, conditional):
    `cor312Pointwise_sourceInterface_hptfin_of_mem_unitRegion` rewires the
    membership-to-finiteness conditional `cor312Gap2_hptfin_of_mem_unitRegion`
    (`Cor312ComparisonGapReduction.lean:432`) at the realized carrier.
  * `hptfin`, independence (route R3, precise negative result):
    `cor312Pointwise_not_forall_singleton_logVolume_lt_top` exhibits the spike
    carrier `cor312Pointwise_spikeCarrier` on `ℝ`, satisfying every
    `IQHullLogVolumeInterface` field, whose singleton volume at a point outside
    the unit region is `⊤`.  Hence the carrier fields alone do not imply
    `hptfin`; the PARKED note of the frozen file is hereby a formal witness.
  * `hpoint`, conditional closure (route R1):
    `cor312Pointwise_sourceInterface_hpoint_of_volHeightDictionary` composes
    the point-height dictionary (the precise missing interface, frozen as
    `Cor312PointwisePointHeightDictionary`) with the H1 reduction, giving
    `hpoint` with `D₁ = 0`;
    `cor312Pointwise_sourceInterface_hpoint_of_volHeightDictionary_additive`
    gives the additive mirror with `D₁ = A` under the approved additive input
    (`ABCHeightWeightAdditiveBoundV2` shape, IUT IV Theorem A).
  * `hpoint`, dictionary analysis (routes R2/R3):
    `cor312PointwisePointHeightDictionary_iff_max` reduces the dictionary to
    its normal form `max (sourceLocalLogDegree v (λ·pt)) 0 ≤ logHeight₁ x`,
    and `cor312Pointwise_scaledPoint_logDegree_le_of_mem_unitRegion` records
    the only in-tree log-degree estimate for the scaled point — an upper bound
    by `max degreeBound 0`, i.e. by the hull-side normalization constant.
    No declaration in the tree bridges `sourceLocalLogDegree`
    (`SourceVolumeIndex`-indexed p-adic log-degrees of theta-pilot values) to
    `Height.logHeight₁ (abcRationalPoint a c)` or to `arithmeticWeight`; the
    dictionary is therefore recorded as the minimal implementation spec (card)
    for `hpoint` and remains unproved.

  ## Honesty notes

  * `SourceImageRealization` / `SourceUnitRegionHaarData` are named additional
    data of the StepXI layer, not consequences of `OriginalInput`; every
    value-realized statement below is an implication from these data.
  * O1 boundary: under degree-faithful carriers the realized hull volume is `⊤`
    (`sourceHullVolume_eq_top_of_degreeFaithful`,
    `SourceImageHullVolume.lean:428`), so the Card A datum space is empty;
    nothing here presumes non-emptiness of the realized-data space.
  * `IQCarrierConcreteModel.lean` (`:373`, `:386`) is a calibration instance
    only, not a theta-pilot true carrier; no gap field of
    `Cor312EpsilonArithmeticComparison` is filled here, and the distance to
    the Card-HULLREAL obligation is unchanged.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT

universe ua uv upi umon ui

noncomputable section

/-! ## 1. `hptfin` independence witness (route R3, abstract layer)

The spike carrier satisfies every field of `IQHullLogVolumeInterface` while
assigning `⊤` to the singleton at a point outside the unit region, so `hptfin`
is not derivable from the carrier fields alone. -/

/-- **The spike carrier on the real line.**  The image union and the hull are
`{0}`, the unit region is `{0}`, the scaling is the identity, and the
log-volume assigns `⊤` to every region containing the spike point `1` and the
normalized value `1` to every other nonempty region.  All carrier fields hold;
the singleton log-volume at the spike point is `⊤`. -/
noncomputable def cor312Pointwise_spikeCarrier : IQHullLogVolumeInterface ℝ := by
  classical
  exact
    { imageSet := {0}
      hull := {0}
      imageSet_subset_hull := by intro x hx; exact hx
      logVolume := fun S => if (1 : ℝ) ∈ S then ⊤ else if S.Nonempty then 1 else 0
      logVolume_mono := by
        intro S T hST
        by_cases h1 : (1 : ℝ) ∈ S
        · rw [if_pos h1, if_pos (hST h1)]
        · rw [if_neg h1]
          by_cases hS : S.Nonempty
          · have hT : T.Nonempty := hS.mono hST
            by_cases h1T : (1 : ℝ) ∈ T
            · rw [if_pos hS, if_pos h1T]
              exact le_top
            · rw [if_pos hS, if_neg h1T, if_pos hT]
          · rw [if_neg hS]
            exact zero_le
      unitRegion := {0}
      scaleShift := id
      hull_subset_scaleShift := by intro x hx; exact ⟨x, hx, rfl⟩
      unitRegion_logVolume_lt_top := by
        have h1 : ¬ (1 : ℝ) ∈ ({0} : Set ℝ) := by simp
        have hne : ({0} : Set ℝ).Nonempty := ⟨0, rfl⟩
        change (if (1 : ℝ) ∈ ({0} : Set ℝ) then ⊤
          else if ({0} : Set ℝ).Nonempty then 1 else 0) < ⊤
        rw [if_neg h1, if_pos hne]
        exact ENNReal.one_lt_top
      scaleShift_unitRegion_logVolume_le := by
        rw [Set.image_id] }

/-- In the spike carrier, the singleton over the spike point has log-volume
`⊤`. -/
theorem cor312Pointwise_spikeCarrier_logVolume_singleton :
    cor312Pointwise_spikeCarrier.logVolume ({1} : Set ℝ) = ⊤ := by
  classical
  change (if (1 : ℝ) ∈ ({1} : Set ℝ) then (⊤ : ENNReal)
    else if ({1} : Set ℝ).Nonempty then (1 : ENNReal) else 0) = ⊤
  rw [if_pos (show (1 : ℝ) ∈ ({1} : Set ℝ) from rfl)]

/-- The point at the spike has infinite singleton log-volume in the spike
carrier (with the constant point map `1`). -/
theorem cor312Pointwise_spikeCarrier_pt_not_finite :
    ¬ (cor312Pointwise_spikeCarrier.logVolume
      {cor312Pointwise_spikeCarrier.scaleShift ((fun _ _ _ => (1 : ℝ)) 1 2 3)} < ⊤) := by
  intro hfin
  have htop : cor312Pointwise_spikeCarrier.logVolume ({1} : Set ℝ) = ⊤ :=
    cor312Pointwise_spikeCarrier_logVolume_singleton
  have hset : ({cor312Pointwise_spikeCarrier.scaleShift
      ((fun _ _ _ => (1 : ℝ)) 1 2 3)} : Set ℝ) = ({1} : Set ℝ) :=
    congrArg (fun y : ℝ => ({y} : Set ℝ))
      (show cor312Pointwise_spikeCarrier.scaleShift
          ((fun _ _ _ => (1 : ℝ)) 1 2 3) = 1 from rfl)
  rw [hset, htop] at hfin
  exact (lt_irrefl (⊤ : ENNReal)) hfin

/-- **`hptfin` is not an interface theorem.**  There is a carrier satisfying
all `IQHullLogVolumeInterface` fields and a point map on which the `hptfin`
assertion of `Cor312ComparisonGapReduction.lean:314` fails; the finiteness
input must come from membership of the named point in the unit region or from
the value-realized carrier, not from the carrier fields. -/
theorem cor312Pointwise_not_forall_singleton_logVolume_lt_top :
    ¬ (∀ (W : IQHullLogVolumeInterface ℝ) (logShellPoint : Nat → Nat → Nat → ℝ),
        ∀ a b c : Nat, IsABCTriple a b c →
          W.logVolume {W.scaleShift (logShellPoint a b c)} < ⊤) := by
  intro h
  have habc : IsABCTriple 1 2 3 :=
    ⟨Nat.one_pos, by norm_num, by norm_num, Nat.coprime_one_left 2⟩
  exact cor312Pointwise_spikeCarrier_pt_not_finite
    (h cor312Pointwise_spikeCarrier (fun _ _ _ => (1 : ℝ)) 1 2 3 habc)

end

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

noncomputable section

/-! ## 2. `hptfin` at the value-realized carrier (routes R1/R2) -/

/-- **Consumer-shaped `hptfin` for the value-realized carrier (route R2).**
The rewiring of `cor312GapSupply_sourceInterface_hptfin`
(`Cor312ComparisonGapSupplyLayer.lean:152-160`) to the exact `hptfin` operand
shape of `Cor312ComparisonGapReduction.lean:381`; no ABC hypothesis is needed,
since the singleton set volume is `ofReal` of a real log-degree. -/
theorem cor312Pointwise_sourceInterface_hptfin (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v) :
    ∀ a b c : Nat, IsABCTriple a b c →
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
        {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)} < ⊤ :=
  fun a b c _ => I.cor312GapSupply_sourceInterface_hptfin v R n D p a b c

/-- **Membership-route `hptfin` at the value-realized carrier (route R1).**
The rewiring of the abstract conditional `cor312Gap2_hptfin_of_mem_unitRegion`
(`Cor312ComparisonGapReduction.lean:432`): unit-region membership of the named
point on ABC triples suffices at the realized carrier as well. -/
theorem cor312Pointwise_sourceInterface_hptfin_of_mem_unitRegion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    (hmem : ∀ a b c : Nat, IsABCTriple a b c → p a b c ∈ D.unitRegion) :
    ∀ a b c : Nat, IsABCTriple a b c →
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
        {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)} < ⊤ :=
  cor312Gap2_hptfin_of_mem_unitRegion (I.sourceUnitRegionHaarInterface v R n D) p hmem

/-! ## 3. `hpoint`: normal form of the point-height dictionary -/

/-- **Normal form of the realized singleton volume.**  The realized point
volume is `ofReal` of the real log-degree; its `toReal` is the positive part
`max (logDegree) 0`.  This is the normal form in which the point-height
dictionary compares the value-side log-degree with the arithmetic height. -/
theorem cor312Pointwise_sourceSetVolume_singleton_toReal_eq_max (v : V)
    (x : I.ThetaPilotPoint v) :
    (I.sourceSetVolume v {x}).toReal = max (I.sourceLocalLogDegree v x) 0 := by
  rw [I.cor312GapSupply_sourceSetVolume_singleton v x]
  change (ENNReal.ofReal (I.sourceLocalLogDegree v x)).toReal =
    max (I.sourceLocalLogDegree v x) 0
  by_cases h : 0 ≤ I.sourceLocalLogDegree v x
  · rw [ENNReal.toReal_ofReal h, max_eq_left h]
  · have h' : I.sourceLocalLogDegree v x ≤ 0 := (not_le.mp h).le
    rw [ENNReal.ofReal_eq_zero.mpr h', ENNReal.toReal_zero, max_eq_right h']

/-- **The point-height dictionary (minimal implementation spec for `hpoint`).**
The precise missing interface: the realized singleton log-volume of the scaled
named point is dominated by the canonical height of the ABC rational point.
This is the exact hypothesis consumed by
`cor312Gap2_pointBound_of_singletonVolume_le_logHeight`
(`Cor312ComparisonGapReduction.lean:455`) at the realized carrier; no
construction is available in the tree (see the route accounting in the module
docstring). -/
def Cor312PointwisePointHeightDictionary (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    ((I.sourceUnitRegionHaarInterface v R n D).logVolume
      {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)}).toReal ≤
      Height.logHeight₁ (abcRationalPoint a c)

/-- **Dictionary normal form.**  The dictionary is equivalent to the
`max (logDegree) 0`-comparison of the scaled point against the canonical
height — the shape in which the missing bridge to the arithmetic side would
have to be stated. -/
theorem cor312PointwisePointHeightDictionary_iff_max (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v) :
    Cor312PointwisePointHeightDictionary (I := I) v R n D p ↔
      ∀ a b c : Nat, IsABCTriple a b c →
        max (I.sourceLocalLogDegree v (D.scaling * p a b c)) 0 ≤
          Height.logHeight₁ (abcRationalPoint a c) := by
  constructor
  · intro h a b c habc
    have hh := h a b c habc
    change (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
      Height.logHeight₁ (abcRationalPoint a c) at hh
    rwa [I.cor312Pointwise_sourceSetVolume_singleton_toReal_eq_max v
      (D.scaling * p a b c)] at hh
  · intro h a b c habc
    change (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
      Height.logHeight₁ (abcRationalPoint a c)
    rw [I.cor312Pointwise_sourceSetVolume_singleton_toReal_eq_max v
      (D.scaling * p a b c)]
    exact h a b c habc

/-- **The only in-tree log-degree estimate for the scaled point (route R2
exploration).**  Under unit-region membership, the scaled point's log-degree is
dominated by `max degreeBound 0`: the degree bound of the unit region plus the
nonpositivity of the scaling degree.  This bounds the point volume by the
hull-side normalization constant `degreeBound` only; it contains no height or
weight information, which is the exact block of route R2 (see the module
docstring). -/
theorem cor312Pointwise_scaledPoint_logDegree_le_of_mem_unitRegion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v) {a b c : Nat}
    (hmem : p a b c ∈ D.unitRegion) :
    I.sourceLocalLogDegree v (D.scaling * p a b c) ≤ max D.degreeBound 0 := by
  rw [I.sourceLocalLogDegree_mul v D.scaling (p a b c)]
  have h1 : I.sourceLocalLogDegree v (p a b c) ≤ D.degreeBound :=
    D.unitRegion_logDegree_le (p a b c) hmem
  have h2 : I.sourceLocalLogDegree v D.scaling ≤ 0 := D.scaling_logDegree_nonpos
  have h3 : D.degreeBound ≤ max D.degreeBound 0 := le_max_left D.degreeBound 0
  linarith

/-! ## 4. `hpoint` at the value-realized carrier (route R1, conditional closure) -/

/-- **Conditional closure of `hpoint` (valuation route, `D₁ = 0`).**  The
point-height dictionary plus the proved H1 reduction of
`ABCHeightArithmeticWeightComparison.lean` (DSH-B) closes the `hpoint` operand
of `Cor312ComparisonGapReduction.lean:383` at the realized carrier via
`cor312Gap2_pointBound_of_singletonVolume_le_logHeight`
(`Cor312ComparisonGapReduction.lean:455`). -/
theorem cor312Pointwise_sourceInterface_hpoint_of_volHeightDictionary (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hvolheight : Cor312PointwisePointHeightDictionary (I := I) v R n D p)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : ℝ)) ≤ 1 + eps) :
    ∀ a b c : Nat, IsABCTriple a b c →
      ((I.sourceUnitRegionHaarInterface v R n D).logVolume
        {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) :=
  cor312Gap2_pointBound_of_singletonVolume_le_logHeight
    (I.sourceUnitRegionHaarInterface v R n D) p heps hvolheight hval

/-- **Conditional closure of `hpoint` (additive route, `D₁ = A`).**  Mirror of
`cor312Pointwise_sourceInterface_hpoint_of_volHeightDictionary` under the
approved additive arithmetic input (IUT IV Theorem A shape,
`ABCHeightWeightAdditiveBoundV2`). -/
theorem cor312Pointwise_sourceInterface_hpoint_of_volHeightDictionary_additive (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    {eps A : ℝ}
    (hvolheight : Cor312PointwisePointHeightDictionary (I := I) v R n D p)
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A) :
    ∀ a b c : Nat, IsABCTriple a b c →
      ((I.sourceUnitRegionHaarInterface v R n D).logVolume
        {(I.sourceUnitRegionHaarInterface v R n D).scaleShift (p a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312Gap2_pointBound_of_singletonVolume_le_logHeight_of_additiveBound
    (I.sourceUnitRegionHaarInterface v R n D) p hvolheight hadd

/-! ## 5. Frozen pointwise residual datum and consumer composites -/

/-- **Frozen pointwise residual datum.**  The carrier plus the point-height
dictionary — the minimal named data through which the two pointwise inputs
close at the value-realized carrier: `hptfin` is discharged by the carrier
realization alone, and `hpoint` is discharged by the dictionary (route R1). -/
structure Cor312PointwiseResidualData (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (p : Nat → Nat → Nat → I.ThetaPilotPoint v) where
  /-- The true-carrier hypothesis: a unit-region/Haar datum. -/
  carrier : I.SourceUnitRegionHaarData v R n
  /-- The point-height dictionary (the minimal spec card for `hpoint`). -/
  pointHeightDictionary : Cor312PointwisePointHeightDictionary (I := I) v R n carrier p

/-- **`hptfin` closure through the frozen datum.**  The finiteness input is
discharged by the carrier realization alone (no use of the dictionary). -/
theorem cor312PointwiseResidualData_hptfin (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    (C : Cor312PointwiseResidualData (I := I) v R n p) :
    ∀ a b c : Nat, IsABCTriple a b c →
      (I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
        {(I.sourceUnitRegionHaarInterface v R n C.carrier).scaleShift (p a b c)} < ⊤ :=
  cor312Pointwise_sourceInterface_hptfin (I := I) v R n C.carrier p

/-- **`hpoint` closure through the frozen datum (valuation route, `D₁ = 0`).** -/
theorem cor312PointwiseResidualData_hpoint (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    (C : Cor312PointwiseResidualData (I := I) v R n p)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : ℝ)) ≤ 1 + eps) :
    ∀ a b c : Nat, IsABCTriple a b c →
      ((I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
        {(I.sourceUnitRegionHaarInterface v R n C.carrier).scaleShift (p a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) :=
  cor312Pointwise_sourceInterface_hpoint_of_volHeightDictionary (I := I) v R n
    C.carrier p heps C.pointHeightDictionary hval

/-- **`hpoint` closure through the frozen datum (additive route, `D₁ = A`).** -/
theorem cor312PointwiseResidualData_hpoint_additive (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    (C : Cor312PointwiseResidualData (I := I) v R n p)
    {eps A : ℝ}
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A) :
    ∀ a b c : Nat, IsABCTriple a b c →
      ((I.sourceUnitRegionHaarInterface v R n C.carrier).logVolume
        {(I.sourceUnitRegionHaarInterface v R n C.carrier).scaleShift (p a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A :=
  cor312Pointwise_sourceInterface_hpoint_of_volHeightDictionary_additive (I := I) v R n
    C.carrier p C.pointHeightDictionary hadd

/-- **Consumer composite (valuation route).**  Feeds
`cor312GapAssembly_epsilonComparisonOfReducedInputs`
(`Cor312ComparisonGapReduction.lean:367-393`) at the value-realized carrier
with `hsplit` and `hptfin` discharged (theorems of the supply layer and
Section 2), `hunit` from the Card A degree-bound comparison, `hweightvol` from
the degree dictionary, and `hpoint` from the point-height dictionary
(`D₁ = 0`); the two gap fields are produced as fields of
`Cor312EpsilonArithmeticComparison`, i.e. in the ToABCBridge consumer shape
(`Cor312ToABCBridgeInterface.lean:247-250`, `:331-334`). -/
noncomputable def cor312PointwiseResidualData_epsilonComparison (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    (C : Cor312PointwiseResidualData (I := I) v R n p)
    {eps D₀ : ℝ} (heps : 0 ≤ eps) (hD₀ : 0 ≤ D₀)
    (hB : ENNReal.ofReal C.carrier.degreeBound ≤
      I.sourceHullVolume v R n + ENNReal.ofReal D₀)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : ℝ)) ≤ 1 + eps)
    (hdeg : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v (C.carrier.scaling * p a b c)) :
    Cor312EpsilonArithmeticComparison
      (I.sourceUnitRegionHaarInterface v R n C.carrier) eps :=
  cor312GapAssembly_epsilonComparisonOfReducedInputs
    (W := I.sourceUnitRegionHaarInterface v R n C.carrier) (logShellPoint := p)
    (D₀ := D₀) (D₁ := 0) heps hD₀ hval
    (I.cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary v R n
      C.carrier p hdeg)
    (I.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume v R n
      C.carrier hD₀ hB)
    (I.cor312GapSupply_sourceInterface_hsplit v R n C.carrier p)
    (fun a b c _ => I.cor312GapSupply_sourceInterface_hptfin v R n C.carrier p a b c)
    (fun a b c habc => by
      simpa only [add_zero] using
        cor312Gap2_pointBound_of_singletonVolume_le_logHeight
          (I.sourceUnitRegionHaarInterface v R n C.carrier) p heps
          C.pointHeightDictionary hval a b c habc)

/-- **Consumer composite (additive route).**  Version-2 mirror of
`cor312PointwiseResidualData_epsilonComparison` through
`cor312GapAssembly_epsilonComparisonOfAdditiveInput`
(`Cor312ComparisonGapReduction.lean:599-627`); the additive input replaces the
valuation bound and the conclusion is the additive comparison
`Cor312EpsilonArithmeticComparisonAdditive`. -/
noncomputable def cor312PointwiseResidualData_epsilonComparisonAdditive (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    (C : Cor312PointwiseResidualData (I := I) v R n p)
    {eps D₀ A : ℝ} (heps : 0 ≤ eps) (hD₀ : 0 ≤ D₀)
    (hB : ENNReal.ofReal C.carrier.degreeBound ≤
      I.sourceHullVolume v R n + ENNReal.ofReal D₀)
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A)
    (hdeg : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v (C.carrier.scaling * p a b c)) :
    Cor312EpsilonArithmeticComparisonAdditive
      (I.sourceUnitRegionHaarInterface v R n C.carrier) eps A :=
  cor312GapAssembly_epsilonComparisonOfAdditiveInput
    (W := I.sourceUnitRegionHaarInterface v R n C.carrier) (logShellPoint := p)
    (D₀ := D₀) (D₁ := A) heps hD₀ hadd
    (I.cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary v R n
      C.carrier p hdeg)
    (I.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume v R n
      C.carrier hD₀ hB)
    (I.cor312GapSupply_sourceInterface_hsplit v R n C.carrier p)
    (fun a b c _ => I.cor312GapSupply_sourceInterface_hptfin v R n C.carrier p a b c)
    (fun a b c habc =>
      cor312Gap2_pointBound_of_singletonVolume_le_logHeight_of_additiveBound
        (I.sourceUnitRegionHaarInterface v R n C.carrier) p
        C.pointHeightDictionary hadd a b c habc)

end

end OriginalInput
end Theorem311Source

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the pointwise residual supply (`hptfin`, `hpoint`) of the
Corollary 3.12 comparison gap 2. -/
def cor312PointwiseResidualSupply : Obligation :=
  { id := "IUT-III.cor312-pointwise-residual-supply"
    source :=
      "IUT III, Corollary 3.12 (log-volume estimates for Θ-pilot objects; " ++
        "corpus lines 10324-10358); Remark 3.9.5, (i); IUT IV, Proposition " ++
        "1.4, (i) (corpus lines 671-682) and Theorem A / Corollary 2.3 " ++
        "(corpus lines 93-105); consumer chain " ++
        "Cor312ComparisonGapSupplyLayer.lean -> " ++
        "Cor312ComparisonGapReduction.lean:367-393 -> " ++
        "Cor312ToABCBridgeInterface.lean:247-250/:331-334"
    status := VerificationStatus.interface
    note :=
      "Pointwise-residual slice of the gap-reduction down-drill. hptfin: " ++
        "DISCHARGED at the value-realized carrier " ++
        "(cor312Pointwise_sourceInterface_hptfin, no ABC hypothesis; singleton " ++
        "volume = ofReal log-degree), rewired to the consumer slot " ++
        "GapReduction:381; abstract-layer conditional from unit-region " ++
        "membership (GapReduction:432 rewired); independence witness " ++
        "cor312Pointwise_not_forall_singleton_logVolume_lt_top (spike carrier " ++
        "on R with singleton volume top): the carrier fields alone do not " ++
        "imply hptfin. hpoint: CONDITIONALLY CLOSED via the point-height " ++
        "dictionary Cor312PointwisePointHeightDictionary (normal form " ++
        "max (sourceLocalLogDegree (lambda*pt)) 0 <= logHeight1; " ++
        "cor312PointwisePointHeightDictionary_iff_max), valuation route D1 = 0 " ++
        "and additive route D1 = A (IUT IV Theorem A shape). The dictionary " ++
        "itself is NOT proved: no tree declaration bridges sourceLocalLogDegree " ++
        "to logHeight1 (abcRationalPoint) or arithmeticWeight, and the only " ++
        "in-tree estimate is the hull-side bound " ++
        "sourceLocalLogDegree (scaled pt) <= max degreeBound 0. Consumer " ++
        "composites (valuation and additive routes) feed GapReduction:367-393 " ++
        "with hsplit and hptfin discharged; no gap field is filled, and the " ++
        "Card-HULLREAL distance is unchanged (d5 model = calibration only; " ++
        "degree-faithful O1 emptiness unaffected)."
    dependsOn :=
      [ "IUT-III.cor312-comparison-gap-reduction",
        "IUT-III.cor312-hull-normalization-conditional-closure",
        "IUT-III.corollary-3.12-iq-carrier-haar-data",
        "IUT-III.corollary-3.12-source-image-hull-volume" ] }

end LeanFormal.IUT.Audit
