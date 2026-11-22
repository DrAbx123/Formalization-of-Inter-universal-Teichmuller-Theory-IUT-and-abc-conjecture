import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-!
  # Reduced-input forms of the two Corollary 3.12 comparison gaps

  Companion of `ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean` (imported here,
  not modified).  That file freezes the conditional Corollary 3.12 → ABC bridge on
  the concrete comparison region

  `normalizedComparisonRegion W logShellPoint a b c =
     W.scaleShift '' (W.unitRegion ∪ {logShellPoint a b c})`

  with the two named gap fields of `Cor312EpsilonArithmeticComparison W epsilon`:

  * gap 1 (`height_le_normalizedRegionVolume`):
    `logHeight₁ (abcRationalPoint a c) ≤ (1 + ε) · (logVolume region).toReal`;
  * gap 2 (`regionVolume_le_normalizedWeight`), with a triple-independent `D`:
    `(logVolume region).toReal ≤ (1 + ε) · arithmeticWeight (abcRationalPoint a c)
       + (logVolume hull).toReal + D`.

  This module does not fill those fields, does not prove them, and does not change
  the interface file.  It records exact reductions of the two gaps toward the
  paper inputs, with every remaining input named.

  ## Gap 1 (conditionalized on the arithmetic weight comparison)

  The arithmetic input is the proved H1 reduction of
  `ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean` (DSH-B;
  SHA 4BD5B904…), consumed here as
  `abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_of_valuation_bound`:
  a uniform local valuation bound `max 0 (−v_q) ≤ 1 + ε` on the arithmetic prime
  support of `x = a/c` gives `logHeight₁ x ≤ (1 + ε) · arithmeticWeight x`.
  Theorem `cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound` then
  derives the exact gap-1 shape at fixed carrier, point datum, and `ε ≥ 0`, from
  that valuation bound plus the single named comparison

  `arithmeticWeight (abcRationalPoint a c) ≤
     (logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal`.

  That comparison is *not* an interface theorem:
  `cor312Gap1_exists_carrier_arithmeticWeight_gt_normalizedComparisonRegionVolume`
  exhibits the calibration carrier `realLineHullData` (point map `c ↦ Real.log c`)
  at the ABC triple `(1, 2, 3)`, where `arithmeticWeight (abcRationalPoint 1 3) =
  Real.log 6 > Real.log 3 = (logVolume region).toReal`; see also
  `cor312Gap1_not_forall_arithmeticWeight_le_normalizedComparisonRegionVolume`.

  ## Gap 2 (reduced to four named inputs, `D = D₀ + D₁`)

  `cor312Gap2_normalizedComparisonRegion_eq_scaleShift_union` proves, purely at
  the Set level, the decomposition

  `region = scaleShift '' unitRegion ∪ {scaleShift (logShellPoint a b c)}`.

  Theorem `cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound`
  derives the exact gap-2 shape from four named inputs:

  * `hunit` : `logVolume unitRegion ≤ logVolume hull + ofReal D₀` (`0 ≤ D₀`) — the
    normalization of the unit log-shell against the Corollary 3.12 θ-pilot hull
    bound; the carrier field `scaleShift_unitRegion_logVolume_le` transports it
    to `logVolume (scaleShift '' unitRegion)`;
  * `hsplit` : `logVolume region ≤ logVolume (scaleShift '' unitRegion) +
    logVolume {scaleShift (logShellPoint a b c)}` — subadditivity of `logVolume`
    over the actual two components of the decomposition; it follows from the
    single structural input `∀ S T, logVolume (S ∪ T) ≤ logVolume S + logVolume T`
    by `cor312Gap2_region_logVolume_le_add_of_subadditive`, and is not derivable
    from the carrier fields alone;
  * `hptfin` : `logVolume {scaleShift (logShellPoint a b c)} < ⊤` — needed because
    `.toReal` is order-faithful only on finite values (`(⊤).toReal = 0`);
  * `hpoint` : `(logVolume {scaleShift (logShellPoint a b c)}).toReal ≤
    (1 + ε) · arithmeticWeight (abcRationalPoint a c) + D₁` — the normalized
    point-volume bound on the named datum `logShellPoint`.

  `cor312GapAssembly_epsilonComparisonOfReducedInputs` assembles both reduced
  input families into an honest `Cor312EpsilonArithmeticComparison W ε`, so the
  reductions land in exactly the consumer interface (e.g.
  `cor312ToABCBridge_heightBound`), with no change of statement.

  ## What remains open (PARKED, exact hypotheses listed above)

  None of the five inputs (`hweightvol`, `hunit`, `hsplit`, `hptfin`, `hpoint`) is
  derivable at this interface: `logVolume` is constrained only by the carrier
  fields and monotonicity, so it may take arbitrarily large values (even `⊤`) on
  the point part of the region.  The only unconditional region-volume facts
  available are the *lower* bounds
  `cor312Gap2_hull_logVolume_le_normalizedComparisonRegion` and
  `cor312Gap2_scaleShift_unitRegion_logVolume_le_normalizedComparisonRegion`
  (with `scaleShift_unitRegion_logVolume_le`), all in the direction opposite to
  what gap 2 needs.  The carrier field `unitRegion_subset_hull` mentioned in some
  task descriptions does not exist in the current `IQHullLogVolumeInterface`; if
  it were added, `D₀ = 0` would become admissible for `hunit`.  This module
  neither assumes nor claims it.

  No statement below is weaker than the quoted shapes, and no gap field is
  claimed filled: the two named gap fields of `Cor312EpsilonArithmeticComparison`
  remain hypotheses.

  ## Round-2 supply-layer addendum (Section 5)

  Section 5 adds further reductions of the same five inputs, without touching any
  existing statement.  The gap-2 split input and the point-finiteness input both
  follow from the single unit-region membership datum
  `logShellPoint a b c ∈ W.unitRegion` on ABC triples; the `hpoint` input follows
  from the named point-volume/height comparison composed with the H1
  valuation-bound reduction, with `D₁ = 0`; that comparison is an identity on
  every ABC triple in the real-line calibration; and the gap-1 weight input is
  shown to have its minimal carrier at the point singleton.  The value-realized
  source-side discharges of these inputs are in the companion
  `ABCBridge/Bridge/Cor312ComparisonGapSupplyLayer.lean`.  The PARKED status of
  the abstract interface described above is unchanged.
-/

namespace LeanFormal.IUT

noncomputable section

universe u

/-! ## 1. Set-level facts of the normalized comparison region -/

/-- **The region is the union of the scaled unit region and the scaled point.**
The concrete comparison region `scaleShift '' (unitRegion ∪ {logShellPoint a b c})`
decomposes, purely by Set arithmetic, into `scaleShift '' unitRegion` and the
image singleton `{scaleShift (logShellPoint a b c)}`.  This is the exact
Set-level content behind the "arithmetic part + point" split used by the gap-2
reduction
`cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound`. -/
theorem cor312Gap2_normalizedComparisonRegion_eq_scaleShift_union {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    (a b c : Nat) :
    normalizedComparisonRegion W logShellPoint a b c =
      W.scaleShift '' W.unitRegion ∪ {W.scaleShift (logShellPoint a b c)} := by
  unfold normalizedComparisonRegion
  rw [Set.image_union, Set.image_singleton]

/-- **Lower-bound chain (proved, no hypotheses).**  The hull log-volume is at most
the comparison-region log-volume: `hull ⊆ scaleShift '' unitRegion` is a carrier
field and the scaled unit region is one component of the region.  This is the
only direction the carrier fields give for free; the upper bound needed by gap 2
is the named input below. -/
theorem cor312Gap2_hull_logVolume_le_normalizedComparisonRegion {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    (a b c : Nat) :
    W.logVolume W.hull ≤
      W.logVolume (normalizedComparisonRegion W logShellPoint a b c) := by
  unfold normalizedComparisonRegion
  exact W.logVolume_mono
    (Set.Subset.trans W.hull_subset_scaleShift (Set.image_mono Set.subset_union_left))

/-- **Lower-bound chain (proved, no hypotheses).**  The scaled unit-region
log-volume is at most the comparison-region log-volume. -/
theorem cor312Gap2_scaleShift_unitRegion_logVolume_le_normalizedComparisonRegion {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    (a b c : Nat) :
    W.logVolume (W.scaleShift '' W.unitRegion) ≤
      W.logVolume (normalizedComparisonRegion W logShellPoint a b c) := by
  unfold normalizedComparisonRegion
  exact W.logVolume_mono (Set.image_mono Set.subset_union_left)

/-- **The gap-2 split input reduces to structural subadditivity of `logVolume`.**
If `logVolume (S ∪ T) ≤ logVolume S + logVolume T` for all sets (the paper's
log-volume is a measure-like functional; this structural property is *not* among
the carrier fields, whose only supply for `logVolume` is monotonicity plus the
finiteness/normalization data), then the per-triple split hypothesis `hsplit` of
the gap-2 reduction holds, with the two components of
`cor312Gap2_normalizedComparisonRegion_eq_scaleShift_union`. -/
theorem cor312Gap2_region_logVolume_le_add_of_subadditive {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    (hsubadd : ∀ S T : Set X, W.logVolume (S ∪ T) ≤ W.logVolume S + W.logVolume T)
    (a b c : Nat) :
    W.logVolume (normalizedComparisonRegion W logShellPoint a b c) ≤
      W.logVolume (W.scaleShift '' W.unitRegion) +
        W.logVolume {W.scaleShift (logShellPoint a b c)} := by
  rw [cor312Gap2_normalizedComparisonRegion_eq_scaleShift_union]
  exact hsubadd _ _

/-! ## 2. Gap 1: conditionalization on the arithmetic weight comparison -/

/-- **Gap-1 shape from H1 and the named weight comparison.**  Fix the carrier
`W`, the named point datum `logShellPoint`, and `ε ≥ 0`.

The arithmetic input is exactly the proved H1 reduction of
`ABCHeightArithmeticWeightComparison.lean` (DSH-B, SHA 4BD5B904…), consumed here
through `abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_of_valuation_bound`:
the uniform local valuation bound `max 0 (−v_q) ≤ 1 + ε` on the arithmetic prime
support of `x = a/c` yields `logHeight₁ x ≤ (1 + ε) · arithmeticWeight x`.

The only remaining input is the named comparison of the arithmetic weight with
the log-volume of the comparison region,
`arithmeticWeight (abcRationalPoint a c) ≤
   (logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal`.
Given it, the `(1 + ε)` factor transports by nonnegativity (`ε ≥ 0`), and the
conclusion is exactly the gap-1 field shape at `W`, `logShellPoint`, `ε`.

The comparison is *not* an interface theorem — see
`cor312Gap1_exists_carrier_arithmeticWeight_gt_normalizedComparisonRegionVolume`
— so this conditionalization is the faithful reduction, not a cosmetic one. -/
theorem cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : ℝ)) ≤ 1 + eps)
    (hweightvol : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) *
          (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal := by
  intro a b c habc
  have hH1 :=
    abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_of_valuation_bound
      habc heps (hval a b c habc)
  have hcoeff : 0 ≤ 1 + eps := by linarith
  exact le_trans hH1 (mul_le_mul_of_nonneg_left (hweightvol a b c habc) hcoeff)

/-- **Negative calibration: the weight comparison is a genuine extra hypothesis.**
There is a carrier instance of `IQHullLogVolumeInterface` — the calibration
witness `realLineHullData` on `ℝ` with the point map `c ↦ Real.log c` — and an ABC
triple (namely `(1, 2, 3)`) at which the named gap-1 comparison fails:

`arithmeticWeight (abcRationalPoint 1 3) = Real.log 6 > Real.log 3 =
   (logVolume (normalizedComparisonRegion realLineHullData
     (fun _ _ c => Real.log c) 1 2 3)).toReal`.

The carrier is the one already used to calibrate the bridge interface; the weight
of `x = 1/3` on the triple `(1,2,3)` is `log (radical (1·2·3)) = log 6` by
`arithmeticWeight_abcRationalPoint`, while the region is `{0, log 3}` with
log-volume `ofReal (log 3)`.  Consequently the comparison cannot be derived from
the carrier fields alone, and gap 1 genuinely needs it as an input. -/
theorem cor312Gap1_exists_carrier_arithmeticWeight_gt_normalizedComparisonRegionVolume :
    ∃ (W : IQHullLogVolumeInterface ℝ) (logShellPoint : Nat → Nat → Nat → ℝ)
      (a b c : Nat), IsABCTriple a b c ∧
      (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal <
        arithmeticWeight (abcRationalPoint a c) := by
  have hrad6 : natRadical 6 = 6 := by
    have h2 : natRadical 2 = 2 := by
      rw [natRadical_eq_prod_primeFactors,
        Nat.Prime.primeFactors (by norm_num : Nat.Prime 2)]
      simp
    have h3 : natRadical 3 = 3 := by
      rw [natRadical_eq_prod_primeFactors,
        Nat.Prime.primeFactors (by norm_num : Nat.Prime 3)]
      simp
    have h23 : natRadical (2 * 3) = natRadical 2 * natRadical 3 :=
      natRadical_mul_of_coprime (by norm_num : Nat.Coprime 2 3)
    rw [h2, h3] at h23
    norm_num at h23
    exact h23
  have hweight : arithmeticWeight (abcRationalPoint 1 3) = Real.log 6 := by
    have habc : IsABCTriple 1 2 3 :=
      ⟨Nat.one_pos, by norm_num, by norm_num, Nat.coprime_one_left 2⟩
    rw [arithmeticWeight_abcRationalPoint habc]
    change Real.log (natRadical 6 : ℝ) = Real.log 6
    rw [hrad6]
    norm_num
  refine ⟨realLineHullData, fun _ _ c => Real.log (c : ℝ), 1, 2, 3, ?_, ?_⟩
  · exact ⟨Nat.one_pos, by norm_num, by norm_num, Nat.coprime_one_left 2⟩
  · change (realLineLogVolume (id ''
        (({0} : Set ℝ) ∪ {Real.log (3 : ℝ)}))).toReal <
      arithmeticWeight (abcRationalPoint 1 3)
    rw [Set.image_id, Set.singleton_union,
      realLineLogVolume_pair_zero (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)),
      ENNReal.toReal_ofReal (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)),
      hweight]
    exact Real.log_lt_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) < 6)

/-- The weight comparison, universally quantified over the real-line carriers ala
the interface, fails; equivalently, the named comparison of the gap-1
conditionalization cannot be dropped and is not an interface theorem. -/
theorem cor312Gap1_not_forall_arithmeticWeight_le_normalizedComparisonRegionVolume :
    ¬ (∀ (W : IQHullLogVolumeInterface ℝ) (logShellPoint : Nat → Nat → Nat → ℝ),
        ∀ a b c : Nat, IsABCTriple a b c →
          arithmeticWeight (abcRationalPoint a c) ≤
            (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) := by
  intro h
  obtain ⟨W, logShellPoint, a, b, c, habc, hlt⟩ :=
    cor312Gap1_exists_carrier_arithmeticWeight_gt_normalizedComparisonRegionVolume
  exact (not_le.mpr hlt) (h W logShellPoint a b c habc)

/-! ## 3. Gap 2: reduction to named unit-region, split, and point inputs -/

/-- **Gap-2 shape from four named inputs (`D = D₀ + D₁`).**  Fix the carrier `W`,
the named point datum `logShellPoint`, and real constants `D₀ ≥ 0`, `D₁`, `ε`.
From

* `hunit` : `logVolume unitRegion ≤ logVolume hull + ofReal D₀`,
* `hsplit` : `logVolume region ≤ logVolume (scaleShift '' unitRegion) +
    logVolume {scaleShift (logShellPoint a b c)}`,
* `hptfin` : `logVolume {scaleShift (logShellPoint a b c)} < ⊤`,
* `hpoint` : `(logVolume {scaleShift (logShellPoint a b c)}).toReal ≤
    (1 + ε) · arithmeticWeight (abcRationalPoint a c) + D₁`,

the exact gap-2 field shape holds with `D = D₀ + D₁`.  Proof chain (all in
`ENNReal` until the final real comparison): the carrier field
`scaleShift_unitRegion_logVolume_le` followed by `hunit` bounds the scaled
unit-region component by `logVolume hull + ofReal D₀`; `hsplit` then bounds the
region; `hull_logVolume_lt_top`, `ofReal_lt_top`, and `hptfin` make the dominating
side finite, so `ENNReal.toReal_mono` applies and the `.toReal` of the sum splits
by `ENNReal.toReal_add` (`ofReal D₀` is `D₀` by `ENNReal.toReal_ofReal` because
`0 ≤ D₀`); `hpoint` then closes the real comparison.

No hypothesis here is derivable from the carrier fields: see the module header
for the precise PARKED status of each input. -/
theorem cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
    {X : Type u} (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    {eps D₀ D₁ : ℝ} (hD₀ : 0 ≤ D₀)
    (hunit : W.logVolume W.unitRegion ≤ W.logVolume W.hull + ENNReal.ofReal D₀)
    (hsplit : ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume (normalizedComparisonRegion W logShellPoint a b c) ≤
        W.logVolume (W.scaleShift '' W.unitRegion) +
          W.logVolume {W.scaleShift (logShellPoint a b c)})
    (hptfin : ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume {W.scaleShift (logShellPoint a b c)} < ⊤)
    (hpoint : ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁) :
    ∃ D : ℝ, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D := by
  refine ⟨D₀ + D₁, fun a b c habc => ?_⟩
  have hunit' : W.logVolume (W.scaleShift '' W.unitRegion) ≤
      W.logVolume W.hull + ENNReal.ofReal D₀ :=
    le_trans W.scaleShift_unitRegion_logVolume_le hunit
  have hsum : W.logVolume (normalizedComparisonRegion W logShellPoint a b c) ≤
      (W.logVolume W.hull + ENNReal.ofReal D₀) +
        W.logVolume {W.scaleShift (logShellPoint a b c)} :=
    le_trans (hsplit a b c habc) (add_le_add hunit' le_rfl)
  have hptfin' : W.logVolume {W.scaleShift (logShellPoint a b c)} < ⊤ :=
    hptfin a b c habc
  have hfin : W.logVolume W.hull + ENNReal.ofReal D₀ ≠ ⊤ :=
    ne_of_lt (ENNReal.add_lt_top.mpr ⟨W.hull_logVolume_lt_top, ENNReal.ofReal_lt_top⟩)
  have hsumFin : (W.logVolume W.hull + ENNReal.ofReal D₀) +
      W.logVolume {W.scaleShift (logShellPoint a b c)} ≠ ⊤ :=
    ne_of_lt (ENNReal.add_lt_top.mpr
      ⟨ENNReal.add_lt_top.mpr ⟨W.hull_logVolume_lt_top, ENNReal.ofReal_lt_top⟩, hptfin'⟩)
  have hreal : (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
      ((W.logVolume W.hull + ENNReal.ofReal D₀) +
        W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal :=
    ENNReal.toReal_mono hsumFin hsum
  have htoReal : ((W.logVolume W.hull + ENNReal.ofReal D₀) +
      W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal =
      (W.logVolume W.hull).toReal + D₀ +
        (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal := by
    simp only [ENNReal.toReal_add hfin (ne_of_lt hptfin'),
      ENNReal.toReal_add (ne_of_lt W.hull_logVolume_lt_top) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hD₀]
  rw [htoReal] at hreal
  have hpoint' := hpoint a b c habc
  linarith

/-! ## 4. Assembly: reduced inputs give the per-`ε` comparison -/

/-- **Assembly of the reduced inputs into `Cor312EpsilonArithmeticComparison W ε`.**
The gap-1 conditionalization `cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound`
and the gap-2 reduction
`cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound`
produce the two gap fields of `Cor312EpsilonArithmeticComparison W eps` at the
same carrier `W`, the same named point datum `logShellPoint`, and `eps ≥ 0`; the
additive constant of the second field is `D₀ + D₁`.  Hence the reductions land in
exactly the consumer interface shape consumed by, e.g.,
`cor312ToABCBridge_heightBound`, with no change of statement; the two gap fields
remain open (this is a conditional assembly from the named inputs, not a proof of
them). -/
def cor312GapAssembly_epsilonComparisonOfReducedInputs {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    {eps D₀ D₁ : ℝ} (heps : 0 ≤ eps) (hD₀ : 0 ≤ D₀)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : ℝ)) ≤ 1 + eps)
    (hweightvol : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal)
    (hunit : W.logVolume W.unitRegion ≤ W.logVolume W.hull + ENNReal.ofReal D₀)
    (hsplit : ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume (normalizedComparisonRegion W logShellPoint a b c) ≤
        W.logVolume (W.scaleShift '' W.unitRegion) +
          W.logVolume {W.scaleShift (logShellPoint a b c)})
    (hptfin : ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume {W.scaleShift (logShellPoint a b c)} < ⊤)
    (hpoint : ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁) :
    Cor312EpsilonArithmeticComparison W eps :=
  { logShellPoint := logShellPoint
    height_le_normalizedRegionVolume :=
      cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound
        W logShellPoint heps hval hweightvol
    regionVolume_le_normalizedWeight :=
      cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
        W logShellPoint hD₀ hunit hsplit hptfin hpoint }

/-! ## 5. Supply-layer fragments: named inputs reduced to smaller named data

Each declaration below strictly reduces one of the five named inputs of
`cor312GapAssembly_epsilonComparisonOfReducedInputs` -- or records a calibration
identity -- without altering any statement above.  The abstract carrier's PARKED
status is unchanged: none of these hypotheses is derivable from the carrier
fields alone, and no gap field is filled. -/

/-- **The gap-2 split input from a unit-region membership datum.**  If the named
point `logShellPoint a b c` lies in `W.unitRegion` on every ABC triple, then
`unitRegion ∪ {logShellPoint a b c} = unitRegion`, so the comparison region is
exactly the scaled unit region and the split inequality holds.  A strictly
smaller named datum replaces `hsplit`: membership of the named point, instead of
subadditivity of `logVolume` over arbitrary pairs. -/
theorem cor312Gap2_hsplit_of_mem_unitRegion {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    (hmem : ∀ a b c : Nat, IsABCTriple a b c → logShellPoint a b c ∈ W.unitRegion) :
    ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume (normalizedComparisonRegion W logShellPoint a b c) ≤
        W.logVolume (W.scaleShift '' W.unitRegion) +
          W.logVolume {W.scaleShift (logShellPoint a b c)} := by
  intro a b c habc
  have hunion : W.unitRegion ∪ {logShellPoint a b c} = W.unitRegion :=
    Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr (hmem a b c habc))
  have hregion : normalizedComparisonRegion W logShellPoint a b c =
      W.scaleShift '' W.unitRegion := by
    unfold normalizedComparisonRegion
    rw [hunion]
  rw [hregion]
  have h := add_le_add (le_refl (W.logVolume (W.scaleShift '' W.unitRegion)))
    (bot_le : (0 : ENNReal) ≤ W.logVolume {W.scaleShift (logShellPoint a b c)})
  simpa only [bot_eq_zero, add_zero] using h

/-- **The point-finiteness input from the same membership datum.**  The scaled
point lies in the scaled unit region, whose log-volume is finite by the carrier
contraction field composed with the unit-region finiteness field; so `hptfin`
follows from `logShellPoint a b c ∈ W.unitRegion` on ABC triples. -/
theorem cor312Gap2_hptfin_of_mem_unitRegion {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    (hmem : ∀ a b c : Nat, IsABCTriple a b c → logShellPoint a b c ∈ W.unitRegion) :
    ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume {W.scaleShift (logShellPoint a b c)} < ⊤ := by
  intro a b c habc
  have hsubset : ({W.scaleShift (logShellPoint a b c)} : Set X) ⊆
      W.scaleShift '' W.unitRegion := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨logShellPoint a b c, hmem a b c habc, hx.symm⟩
  exact lt_of_le_of_lt
    (le_trans (W.logVolume_mono hsubset) W.scaleShift_unitRegion_logVolume_le)
    W.unitRegion_logVolume_lt_top

/-- **The `hpoint` input from the named point-volume/height comparison.**  Given
`(logVolume {scaleShift (logShellPoint a b c)}).toReal ≤ logHeight₁ (abcRationalPoint a c)`
on ABC triples -- the point-height dictionary direction -- and the uniform
valuation bound of the proved H1 reduction (DSH-B,
`ABCHeightArithmeticWeightComparison.lean`, consumed below), the `hpoint` input
of the gap-2 reduction holds with `D₁ = 0`.  This is the exact attachment point
for the arithmetic side in the `hpoint` slot: nothing else about the point
volume is used. -/
theorem cor312Gap2_pointBound_of_singletonVolume_le_logHeight {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hvolheight : ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
        Height.logHeight₁ (abcRationalPoint a c))
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : ℝ)) ≤ 1 + eps) :
    ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) := by
  intro a b c habc
  exact le_trans (hvolheight a b c habc)
    (abcRationalPoint_logHeight₁_le_oneAdd_mul_arithmeticWeight_of_valuation_bound
      habc heps (hval a b c habc))

/-- **Calibration identity for the point-height comparison.**  In the real-line
calibration the named comparison consumed by
`cor312Gap2_pointBound_of_singletonVolume_le_logHeight` holds with equality on
every ABC triple: the singleton log-volume of the realized point is exactly the
height of `abcRationalPoint a c`.  This is a check on the shape of the supplier,
not a model of the paper's carrier. -/
theorem realLineHullData_singletonVolume_eq_logHeight {a b c : Nat}
    (habc : IsABCTriple a b c) :
    (realLineHullData.logVolume
        {realLineHullData.scaleShift (Real.log (c : ℝ))}).toReal =
      Height.logHeight₁ (abcRationalPoint a c) := by
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by
    have h1 : 1 ≤ c := by
      obtain ⟨ha, hb, hsum, _⟩ := habc
      omega
    exact_mod_cast h1
  have hlogc : 0 ≤ Real.log (c : ℝ) := Real.log_nonneg hc1
  change (realLineLogVolume ({Real.log (c : ℝ)} : Set ℝ)).toReal =
    Height.logHeight₁ (abcRationalPoint a c)
  rw [realLineLogVolume_singleton, ENNReal.toReal_ofReal hlogc,
    abcRationalPoint_logHeight₁ habc]

/-- **The gap-1 weight input has its minimal carrier at the point singleton.**
From the singleton-level weight comparison at the `ENNReal` level,
`ofReal (arithmeticWeight x) ≤ logVolume {scaleShift point}`, the region-level
`hweightvol` input follows by monotonicity alone: the scaled point is a member of
the comparison region.  The `toReal` form of the gap-1 input additionally needs
finiteness of the region volume, which is available in the value-realized source
carrier but not at the abstract interface (where `logVolume` may be `⊤` on the
point part). -/
theorem cor312Gap1_weight_le_normalizedRegionVolume_of_singletonVolume {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    (h : ∀ a b c : Nat, IsABCTriple a b c →
      ENNReal.ofReal (arithmeticWeight (abcRationalPoint a c)) ≤
        W.logVolume {W.scaleShift (logShellPoint a b c)}) :
    ∀ a b c : Nat, IsABCTriple a b c →
      ENNReal.ofReal (arithmeticWeight (abcRationalPoint a c)) ≤
        W.logVolume (normalizedComparisonRegion W logShellPoint a b c) := by
  intro a b c habc
  refine le_trans (h a b c habc) (W.logVolume_mono ?_)
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact ⟨logShellPoint a b c, Set.mem_union_right _ (Set.mem_singleton _), rfl⟩

/-- **The `hpoint` input is satisfiable in the real-line calibration.**  With the
calibration identity `realLineHullData_singletonVolume_eq_logHeight`, the
valuation bound of the H1 reduction yields the `hpoint` shape with `D₁ = 0` for
the calibration carrier and the point map `c ↦ log c`.  Together with
`cor312Gap1_exists_carrier_arithmeticWeight_gt_normalizedComparisonRegionVolume`
this shows that in this calibration the two arithmetic directions genuinely
differ: the weight-against-volume direction of gap 1 fails there, while the
point-volume/weight direction holds (given the valuation bound). -/
theorem cor312Gap2_realLineHullData_pointBound_of_valuation_bound
    {eps : ℝ} (heps : 0 ≤ eps)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : ℝ)) ≤ 1 + eps) :
    ∀ a b c : Nat, IsABCTriple a b c →
      (realLineHullData.logVolume
          {realLineHullData.scaleShift (Real.log (c : ℝ))}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) := by
  intro a b c habc
  simpa using cor312Gap2_pointBound_of_singletonVolume_le_logHeight realLineHullData
    (fun _ _ c => Real.log c) heps
    (fun a b c habc => le_of_eq (realLineHullData_singletonVolume_eq_logHeight habc))
    hval a b c habc

/-! ## 7. Versioned additive input (re-freeze 2026-10-16, contract v2)

The `hval` input of sections 2, 4 and 5 — the uniform valuation bound of
`ABCHeightArithmeticWeightComparison.lean` — is refuted
(`no_oneAdd_valuation_bound`, probe `H1UniformValuationBoundCounterexampleProbe.lean`,
family `(1, 2^k − 1, 2^k)`), so every declaration above that consumes `hval` is a
conditional with an unsatisfiable premise.  The mirrors below leave all statements
and proofs above untouched and replace `hval` by the version-2 additive input
`height ≤ (1 + ε) · weight + A` (`ABCHeightWeightAdditiveBoundV2`), landing in the
versioned structure `Cor312EpsilonArithmeticComparisonAdditive` (additive height
field, unchanged log-volume field).  Old and new declarations coexist. -/

/-- **Gap-1 shape from the additive input.**  Version-2 mirror of
`cor312Gap1_height_le_normalizedRegionVolume_of_weight_bound`: the height input is
the additive bound `height ≤ (1 + ε) · weight + A`; the only volume input is the
same weight/comparison-region comparison.  The conclusion is the additive height
field of `Cor312EpsilonArithmeticComparisonAdditive`. -/
theorem cor312Gap1_height_le_normalizedRegionVolume_of_additiveBound {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    {eps A : Real} (heps : 0 ≤ eps)
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A)
    (hweightvol : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal) :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) *
          (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal + A := by
  intro a b c habc
  have hcoeff : 0 ≤ 1 + eps := by linarith
  exact le_trans (hadd a b c habc)
    (add_le_add (mul_le_mul_of_nonneg_left (hweightvol a b c habc) hcoeff) (le_refl A))

/-- **The `hpoint` input from the additive height input** (version-2 mirror of
`cor312Gap2_pointBound_of_singletonVolume_le_logHeight`): composing the
point-volume/height comparison with the additive height bound yields the `hpoint`
slot with `D₁ = A`. -/
theorem cor312Gap2_pointBound_of_singletonVolume_le_logHeight_of_additiveBound {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    {eps A : Real}
    (hvolheight : ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
        Height.logHeight₁ (abcRationalPoint a c))
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A) :
    ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A := by
  intro a b c habc
  exact le_trans (hvolheight a b c habc) (hadd a b c habc)

/-- **The version-2 reduced-input assembly.**  Same carrier, point datum, and named
inputs as `cor312GapAssembly_epsilonComparisonOfReducedInputs`, with the refuted
`hval` replaced by the additive input and the conclusion landing in
`Cor312EpsilonArithmeticComparisonAdditive W eps A`.  The log-volume-computation
field is discharged by the same unchanged gap-2 reduction. -/
def cor312GapAssembly_epsilonComparisonOfAdditiveInput {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat → Nat → Nat → X)
    {eps D₀ D₁ A : Real} (heps : 0 ≤ eps) (hD₀ : 0 ≤ D₀)
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A)
    (hweightvol : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal)
    (hunit : W.logVolume W.unitRegion ≤ W.logVolume W.hull + ENNReal.ofReal D₀)
    (hsplit : ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume (normalizedComparisonRegion W logShellPoint a b c) ≤
        W.logVolume (W.scaleShift '' W.unitRegion) +
          W.logVolume {W.scaleShift (logShellPoint a b c)})
    (hptfin : ∀ a b c : Nat, IsABCTriple a b c →
      W.logVolume {W.scaleShift (logShellPoint a b c)} < ⊤)
    (hpoint : ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume {W.scaleShift (logShellPoint a b c)}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D₁) :
    Cor312EpsilonArithmeticComparisonAdditive W eps A :=
  { logShellPoint := logShellPoint
    height_le_normalizedRegionVolume_add :=
      cor312Gap1_height_le_normalizedRegionVolume_of_additiveBound
        W logShellPoint heps hadd hweightvol
    regionVolume_le_normalizedWeight :=
      cor312Gap2_regionVolume_le_normalizedWeight_of_split_pointBound_unitRegionBound
        W logShellPoint hD₀ hunit hsplit hptfin hpoint }

/-- **The real-line calibration of the additive `hpoint` input** (version-2 mirror
of `cor312Gap2_realLineHullData_pointBound_of_valuation_bound`). -/
theorem cor312Gap2_realLineHullData_pointBound_of_additiveBound
    {eps A : Real}
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A) :
    ∀ a b c : Nat, IsABCTriple a b c →
      (realLineHullData.logVolume
          {realLineHullData.scaleShift (Real.log (c : Real))}).toReal ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A := by
  intro a b c habc
  exact cor312Gap2_pointBound_of_singletonVolume_le_logHeight_of_additiveBound
    realLineHullData (fun _ _ c => Real.log c)
    (fun a b c habc => le_of_eq (realLineHullData_singletonVolume_eq_logHeight habc))
    hadd a b c habc

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the reduced-input forms of the two Corollary 3.12 comparison
gaps of `ABCBridge/Bridge/Cor312ComparisonGapReduction.lean`.  The record
documents what is proved (the conditionalization, the Set-level decomposition,
the lower-bound chain, the negative calibration, the assembly) and what remains a
named input; it does not assert that the gap fields are filled. -/
def cor312ComparisonGapReductionObligation : Obligation :=
  { id := "IUT-III.cor312-comparison-gap-reduction"
    source :=
      "IUT III Corollary 3.12 → IUT IV §2 comparison gaps; companion of " ++
        "ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean"
    status := VerificationStatus.interface
    note :=
      "Reduced-input forms of the two named gaps of Cor312EpsilonArithmeticComparison. " ++
        "Gap 1 is conditionalized: the proved H1 reduction " ++
        "(ABCHeightArithmeticWeightComparison.lean, SHA 4BD5B904…) with a uniform " ++
        "valuation bound max 0 (-v_q) <= 1 + eps, plus the named comparison " ++
        "arithmeticWeight <= (logVolume region).toReal, yields the exact gap-1 " ++
        "shape at fixed carrier, point map, and eps >= 0. The named comparison " ++
        "is a genuine extra hypothesis: the realLineHullData calibration fails " ++
        "it at (1,2,3) (log 6 > log 3), so it is not an interface theorem. Gap 2 " ++
        "is reduced to four named inputs (hunit: vol unitRegion <= vol hull + " ++
        "ofReal D0; hsplit: subadditivity over the proved decomposition region " ++
        "= scaleShift '' unitRegion union {scaleShift point}; hptfin: point " ++
        "singleton volume finite; hpoint: point volume <= (1+eps)*weight + D1) " ++
        "via the carrier field scaleShift_unitRegion_logVolume_le and the " ++
        "lower-bound chain hull subset-of region; the assembly " ++
        "cor312GapAssembly_epsilonComparisonOfReducedInputs produces " ++
        "Cor312EpsilonArithmeticComparison W eps from these inputs with D = " ++
        "D0 + D1. NOT proved: any of the five named inputs, and no claim that " ++
        "the gap fields are filled; the only unconditional region-volume facts " ++
        "are in the opposite (lower-bound) direction. The carrier field " ++
        "unitRegion_subset_hull referenced in some task descriptions does not " ++
        "exist in the current IQHullLogVolumeInterface."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC-conditional-interface",
        "ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison" ] }

end LeanFormal.IUT.Audit
