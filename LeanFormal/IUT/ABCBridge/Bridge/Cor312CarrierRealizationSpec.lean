import LeanFormal.IUT.ABCBridge.Bridge.Cor312GapDictionaryLayer

/-!
  # Carrier realization spec for the Cor 3.12 comparison (minimum-card packaging)

  Companion of `ABCBridge/Bridge/Cor312GapDictionaryLayer.lean` (imported; no
  existing file is modified).  This module packages the remaining
  carrier-realization obligations of the `ε`-comparison into a single frozen
  structure and records, by proof, which of the four frozen obligations are
  consumed, which are satisfiable, and which combinations are refutable.

  ## The frozen four-field obligation package

  For the value-realized carrier `W = I.sourceUnitRegionHaarInterface v R n D`, the
  named point map `p`, and the constant `D₀`, the four obligations are:

  * (a) membership: `∀ a b c, IsABCTriple a b c → p a b c ∈ D.unitRegion`
    (`Cor312CarrierRealizationSpec.memUnitRegion`);
  * (b) hunit comparison: `ofReal D.degreeBound ≤ sourceHullVolume + ofReal D₀`
    (`Cor312CarrierRealizationSpec.hunitComparison`);
  * (c) weight dictionary: `arithmeticWeight x ≤ sourceLocalLogDegree v (λ * p abc)`
    (`Cor312CarrierRealizationSpec.weightDictionary`);
  * (d) point-height dictionary in the minimal real form
    `sourceLocalLogDegree v (λ * p abc) ≤ logHeight₁ x`
    (`Cor312CarrierRealizationSpec.pointHeightDictionary`), equivalent to the
    truncated form `(vol {λ * p abc}).toReal ≤ logHeight₁ x`
    (`cor312CarrierSpec_pointHeightDictionary_iff_truncated`).

  The structure carries all four fields, so it is content-equivalent to the frozen
  obligation list; the judge table below fixes the minimum-card status of each field
  for the assembly.

  ## Judge table (each item: verdict + grounds, proved in this module)

  1. Membership (a): not consumed by the assembly.  Its only abstract-carrier
     consumers are `cor312Gap2_hsplit_of_mem_unitRegion` and
     `cor312Gap2_hptfin_of_mem_unitRegion` (frozen), producing the `hsplit` and
     `hptfin` inputs of gap 2; at the value-realized carrier both inputs are
     unconditional theorems of the supply layer
     (`cor312GapSupply_sourceInterface_hsplit`, `cor312GapSupply_sourceInterface_hptfin`).
     Membership itself is satisfiable for every `D`
     (`cor312CarrierSpec_exists_pointMap_memUnitRegion`, every ABC triple is sent to
     one point of `unitRegion`, extracted from nonemptiness of the hull).
  2. hunit comparison (b): kept in the exact consumer shape of the frozen d2 path
     `cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume` (which
     consumes this comparison together with `0 ≤ D₀`).  It is satisfiable with the
     canonical constant `D₀ := max D.degreeBound 0`
     (`cor312CarrierSpec_exists_hunitConstant`), and the assembly also runs from the
     canonical instance alone, so (b) is absorbable into the constant of the
     conclusion (`cor312CarrierSpec_epsilonComparison_of_dictionaries`).
  3. Weight dictionary (c): a genuine card.  Not a theorem
     (`cor312GapDict_weightDictionary_not_universal`, frozen); exact shape is the
     scaling-separated form `cor312GapDict_weightDictionary_iff_scalingSeparated`; it
     implies the scaling-free form `cor312GapDict_weightDictionary_implies_scalingFree`
     (so weakening to the scaling-free form loses the `logDegree λ` slack and is not
     the consumer shape for the region point `λ * q`); satisfiable under degree
     faithfulness (`cor312GapDict_exists_pointMap_weightDictionary`, frozen).
  4. Point-height dictionary (d): a genuine card, in the minimal real form obtained
     from the frozen `cor312GapDict_singletonVolume_toReal_le_iff`
     (`cor312GapDict_singletonVolume_toReal_eq_max` eliminates all `ENNReal`/`toReal`
     content).  Not a theorem (`cor312GapDict_pointHeightDictionary_not_universal`,
     frozen); satisfiable under degree faithfulness
     (`cor312CarrierSpec_exists_pointMap_pointHeightDictionary`).
  5. **Joint status: the four-field package is refutable, and no sub-package
     reaches the conclusion without the two cards that clash.**  Proved here:
     * (c) and (d) force `arithmeticWeight x ≤ logHeight₁ x` on every ABC triple,
       which fails at `(1, 2, 3)`: `log 6 > log 3`
       (`cor312CarrierSpec_arithmeticWeight_gt_logHeight₁_one_two_three`,
       `cor312CarrierSpec_no_real_between_weight_and_height`); hence no point map
       satisfies both dictionaries for a fixed scaling
       (`cor312CarrierSpec_dictionaries_jointly_refutable`) and the structure has no
       inhabitant (`cor312CarrierSpec_not_inhabited`);
     * (a) and (c) force the bounded log-degree of the unit region to dominate the
       unbounded arithmetic weight
       (`cor312CarrierSpec_exists_isABCTriple_arithmeticWeight_gt`,
       `cor312CarrierSpec_memUnitRegion_weightDictionary_jointly_refutable`);
     * the frozen reductions consume a weight card (only (c) among the four,
       through `cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary`) and a
       point card (only (d) among the four in the `D₁ = 0` route, through
       `cor312GapDict_sourcePointBound_of_degree_le_height`), so the essential
       content of the package is exactly the refuted pair `{(c), (d)}`.  A viable
       replacement must supply a direct point-volume card
       `(vol {λ * p abc}).toReal ≤ (1 + ε) * arithmeticWeight x + D₁` (compatible
       with (c)) or an equivalent comparison not tied to the height; that choice is
       a task-level decision and is not taken here.

  ## Assembly theorems

  `cor312CarrierSpec_epsilonComparison` consumes the four-field package plus the
  valuation bound and proves `Cor312EpsilonArithmeticComparison W ε` through the
  frozen `cor312GapAssembly_epsilonComparisonOfReducedInputs`;
  `cor312CarrierSpec_epsilonComparison_of_dictionaries` proves the same conclusion
  from the two dictionaries alone (membership discharged, hunit canonicalized).
  Both are valid conditionals; per the judge table both hypothesis families are
  refutable through (c) + (d) at `(1, 2, 3)`, so the proofs — which are constructive
  compositions of the frozen reductions and do not use the refutation — remain
  valid for any repaired package of these field shapes.

  ## Consumers

  * `Cor312CarrierRealizationSpec` — instantiation target for a concrete model
    (mind the joint-refutability finding);
  * `cor312CarrierSpec_epsilonComparison`,
    `cor312CarrierSpec_epsilonComparison_of_dictionaries` — assembly interface;
  * the frozen `Cor312ToABCBridgeInterface` (via
    `cor312ToABCBridge_heightBound`) consumes only
    `Cor312EpsilonArithmeticComparison`, so any instantiation of the above lands
    there unchanged.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT

universe ua uv upi umon ui

/-! ## 0. The arithmetic obstruction at `(1, 2, 3)` and the canonical constant -/

/-- `(1, 2, 3)` is an ABC triple: `1 + 2 = 3` with pairwise coprime entries. -/
theorem cor312CarrierSpec_isABCTriple_one_two_three : IsABCTriple 1 2 3 :=
  ⟨Nat.one_pos, by norm_num, by norm_num, Nat.coprime_one_left 2⟩

/-- The arithmetic weight of `x = 1/3` is `log 6 = log (rad (1 * 2 * 3))`. -/
theorem cor312CarrierSpec_arithmeticWeight_abcRationalPoint_one_two_three :
    arithmeticWeight (abcRationalPoint 1 3) = Real.log 6 := by
  rw [arithmeticWeight_abcRationalPoint cor312CarrierSpec_isABCTriple_one_two_three]
  change Real.log (natRadical 6 : ℝ) = Real.log 6
  have hrad6 : natRadical 6 = 6 := by
    have h2 : natRadical 2 = 2 := by
      rw [natRadical_eq_prod_primeFactors, Nat.Prime.primeFactors (by norm_num : Nat.Prime 2)]
      simp
    have h3 : natRadical 3 = 3 := by
      rw [natRadical_eq_prod_primeFactors, Nat.Prime.primeFactors (by norm_num : Nat.Prime 3)]
      simp
    have h23 : natRadical (2 * 3) = natRadical 2 * natRadical 3 :=
      natRadical_mul_of_coprime (by norm_num : Nat.Coprime 2 3)
    rw [h2, h3] at h23
    norm_num at h23
    exact h23
  rw [hrad6]
  norm_num

/-- The logarithmic height of `x = 1/3` is `log 3`. -/
theorem cor312CarrierSpec_logHeight₁_abcRationalPoint_one_two_three :
    Height.logHeight₁ (abcRationalPoint 1 3) = Real.log 3 := by
  rw [abcRationalPoint_logHeight₁ cor312CarrierSpec_isABCTriple_one_two_three]
  norm_num

/-- **The weight of `1/3` strictly exceeds its height** (`log 6 > log 3`). -/
theorem cor312CarrierSpec_arithmeticWeight_gt_logHeight₁_one_two_three :
    Height.logHeight₁ (abcRationalPoint 1 3) <
      arithmeticWeight (abcRationalPoint 1 3) := by
  rw [cor312CarrierSpec_logHeight₁_abcRationalPoint_one_two_three,
    cor312CarrierSpec_arithmeticWeight_abcRationalPoint_one_two_three]
  exact Real.log_lt_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) < 6)

/-- **No real value lies between the weight and the height at `(1, 2, 3)`.**  A
two-sided chain `weight (1/3) ≤ t ≤ height (1/3)` is refutable; this is the
arithmetic core of the joint refutability of the weight and point-height
dictionaries, whose conjunction forces such a chain at `t = λ * p 1 2 3`. -/
theorem cor312CarrierSpec_no_real_between_weight_and_height :
    ¬ ∃ t : ℝ, arithmeticWeight (abcRationalPoint 1 3) ≤ t ∧
      t ≤ Height.logHeight₁ (abcRationalPoint 1 3) := by
  rintro ⟨t, hwt, hth⟩
  exact absurd (le_trans hwt hth)
    (not_le.mpr cor312CarrierSpec_arithmeticWeight_gt_logHeight₁_one_two_three)

/-- **The arithmetic weight on ABC triples is unbounded above**: for every real
`C` some ABC triple has weight above `C`.  Witnesses are the triples
`(1, p, p + 1)` for primes `p`, whose weight is at least `log p` (the radical of
`p * (p + 1)` contains the prime `p`). -/
theorem cor312CarrierSpec_exists_isABCTriple_arithmeticWeight_gt (C : ℝ) :
    ∃ a b c : Nat, IsABCTriple a b c ∧ C < arithmeticWeight (abcRationalPoint a c) := by
  rcases le_or_gt C 0 with hC | hC
  · exact ⟨1, 2, 3, cor312CarrierSpec_isABCTriple_one_two_three, by
      rw [cor312CarrierSpec_arithmeticWeight_abcRationalPoint_one_two_three]
      exact lt_of_le_of_lt hC (Real.log_pos (by norm_num))⟩
  · obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp C)
    obtain ⟨p, hpn, hpprime⟩ := Nat.exists_infinite_primes n
    have hpgt : Real.exp C < (p : ℝ) := lt_of_lt_of_le hn (Nat.cast_le.mpr hpn)
    have hplog : C < Real.log (p : ℝ) :=
      (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr hpprime.pos)).mpr hpgt
    have habc : IsABCTriple 1 p (p + 1) :=
      ⟨Nat.one_pos, hpprime.pos, by omega, Nat.coprime_one_left p⟩
    refine ⟨1, p, p + 1, habc, ?_⟩
    rw [arithmeticWeight_abcRationalPoint habc]
    have hradp : natRadical p = p := by
      rw [natRadical_eq_prod_primeFactors, Nat.Prime.primeFactors hpprime]
      simp
    have hcop : Nat.Coprime p (p + 1) :=
      (Nat.coprime_self_add_right (m := p) (n := 1)).mpr (Nat.coprime_one_right p)
    have hradmul : natRadical (p * (p + 1)) = natRadical p * natRadical (p + 1) :=
      natRadical_mul_of_coprime hcop
    have hle : p ≤ natRadical (p * (p + 1)) := by
      rw [hradmul, hradp]
      have h1 : (1 : Nat) ≤ natRadical (p + 1) :=
        Nat.succ_le_of_lt (natRadical_pos (p + 1))
      calc p = p * 1 := (Nat.mul_one p).symm
        _ ≤ p * natRadical (p + 1) := Nat.mul_le_mul_left p h1
    have hplog' : Real.log (p : ℝ) ≤ Real.log (natRadical (p * (p + 1)) : ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr hpprime.pos) (Nat.cast_le.mpr hle)
    rw [show 1 * p * (p + 1) = p * (p + 1) from by rw [one_mul]]
    exact lt_of_lt_of_le hplog hplog'

/-- `ENNReal.ofReal` does not see the sign normalization of a real constant:
`ofReal (max D₀ 0) = ofReal D₀`.  Used to pass from the frozen hunit comparison
at an arbitrary constant to the nonnegative normal form consumed by the
assembly. -/
theorem cor312CarrierSpec_ofReal_max_zero (D₀ : ℝ) :
    ENNReal.ofReal (max D₀ 0) = ENNReal.ofReal D₀ := by
  rcases le_or_gt 0 D₀ with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right (le_of_lt h), ENNReal.ofReal_of_nonpos (le_of_lt h),
      ENNReal.ofReal_zero]

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

noncomputable section

/-! ## 1. The frozen four-field spec package -/

/-- **Carrier realization spec** — the frozen four-field obligation package of the
Cor 3.12 carrier realization, at the value-realized carrier
`W = I.sourceUnitRegionHaarInterface v R n D` with named point map `p` and hunit
constant `D₀`.

Field roles (judge table in the module docstring):

* `memUnitRegion` is the abstract-layer membership premise; it is not consumed by
  the assembly because its two consumers are unconditional at the value-realized
  carrier (`cor312CarrierSpec_epsilonComparison_of_dictionaries` does without it);
* `hunitComparison` is the exact frozen d2-consumer shape for hunit, and is also
  canonically satisfiable;
* `weightDictionary` and `pointHeightDictionary` are the two genuine cards, in the
  exact frozen shapes, and they are **jointly refutable** at `(1, 2, 3)`
  (`cor312CarrierSpec_not_inhabited`). -/
structure Cor312CarrierRealizationSpec (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat → Nat → Nat → I.ThetaPilotPoint v) (D₀ : ℝ) : Prop where
  /-- (a) Abstract-layer membership: the named point of every ABC triple lies in
  the unit region. -/
  memUnitRegion : ∀ a b c : Nat, IsABCTriple a b c → p a b c ∈ D.unitRegion
  /-- (b) The hunit comparison: the unit-region degree bound is dominated by the
  hull volume plus the constant `D₀`; the exact consumer shape of the frozen
  `cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume`. -/
  hunitComparison : ENNReal.ofReal D.degreeBound ≤
    I.sourceHullVolume v R n + ENNReal.ofReal D₀
  /-- (c) The weight dictionary at the carrier's own point map: the arithmetic
  weight is dominated by the realized log-degree of `λ * p abc`; the exact shape of
  `cor312GapDict_weightDictionary_iff_scalingSeparated` and of the frozen consumer
  `cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary`. -/
  weightDictionary : ∀ a b c : Nat, IsABCTriple a b c →
    arithmeticWeight (abcRationalPoint a c) ≤
      I.sourceLocalLogDegree v (D.scaling * p a b c)
  /-- (d) The point-height dictionary in the minimal real form (all
  `ENNReal`/`toReal` content eliminated by
  `cor312GapDict_singletonVolume_toReal_le_iff`); equivalent to the truncated form
  `(vol {λ * p abc}).toReal ≤ logHeight₁ x` by
  `cor312CarrierSpec_pointHeightDictionary_iff_truncated`. -/
  pointHeightDictionary : ∀ a b c : Nat, IsABCTriple a b c →
    I.sourceLocalLogDegree v (D.scaling * p a b c) ≤
      Height.logHeight₁ (abcRationalPoint a c)

/-! ## 2. Per-field satisfiability evidence -/

/-- **Satisfiability of the membership field (a).**  For every unit-region datum
`D` some point map sends all ABC triples into `D.unitRegion`: the hull is
nonempty, lies in `λ · unitRegion`, so `unitRegion` has a point, and the constant
map to it satisfies the membership shape. -/
theorem cor312CarrierSpec_exists_pointMap_memUnitRegion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) :
    ∃ p : Nat → Nat → Nat → I.ThetaPilotPoint v,
      ∀ a b c : Nat, IsABCTriple a b c → p a b c ∈ D.unitRegion := by
  obtain ⟨x, hx⟩ := I.possibleThetaPilotImageSet_nonempty v R n
  have hxHull : x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
    I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n hx
  obtain ⟨y, hy, _⟩ := (mem_scaledRegionImage_iff).mp (D.hull_subset_scaledRegionImage hxHull)
  exact ⟨fun _ _ _ => y, fun _ _ _ _ => hy⟩

/-- **Satisfiability of the hunit comparison (b).**  The canonical constant
`D₀ := max D.degreeBound 0` satisfies the comparison for every unit-region datum:
`ofReal D.degreeBound ≤ ofReal D₀ ≤ hull + ofReal D₀`. -/
theorem cor312CarrierSpec_exists_hunitConstant (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) :
    ∃ D₀ : ℝ, 0 ≤ D₀ ∧
      ENNReal.ofReal D.degreeBound ≤ I.sourceHullVolume v R n + ENNReal.ofReal D₀ := by
  refine ⟨max D.degreeBound 0, le_max_right _ _, ?_⟩
  calc ENNReal.ofReal D.degreeBound
      ≤ ENNReal.ofReal (max D.degreeBound 0) :=
        ENNReal.ofReal_le_ofReal (le_max_left _ _)
    _ ≤ I.sourceHullVolume v R n + ENNReal.ofReal (max D.degreeBound 0) := by
        simpa only [zero_add] using
          add_le_add zero_le
            (le_refl (ENNReal.ofReal (max D.degreeBound 0)))

/-- **The minimal real form of the point-height dictionary is exactly the frozen
truncated form.**  On ABC triples the height is nonnegative
(`cor312GapDict_abcRationalPoint_logHeight₁_nonneg`), so the frozen
`cor312GapDict_singletonVolume_toReal_le_iff` identifies the two shapes with no
residual content. -/
theorem cor312CarrierSpec_pointHeightDictionary_iff_truncated (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (p : Nat → Nat → Nat → I.ThetaPilotPoint v) :
    (∀ a b c : Nat, IsABCTriple a b c →
      I.sourceLocalLogDegree v (D.scaling * p a b c) ≤
        Height.logHeight₁ (abcRationalPoint a c)) ↔
    (∀ a b c : Nat, IsABCTriple a b c →
      (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
        Height.logHeight₁ (abcRationalPoint a c)) := by
  constructor
  · intro h a b c habc
    exact (I.cor312GapDict_singletonVolume_toReal_le_iff v _
      (cor312GapDict_abcRationalPoint_logHeight₁_nonneg habc)).mpr (h a b c habc)
  · intro h a b c habc
    exact (I.cor312GapDict_singletonVolume_toReal_le_iff v _
      (cor312GapDict_abcRationalPoint_logHeight₁_nonneg habc)).mp (h a b c habc)

/-- **Satisfiability of the point-height dictionary (d) in the minimal real
form.**  Under degree faithfulness some point map satisfies the untruncated
inequality `logDegree (λ * p abc) ≤ logHeight₁ x` on all ABC triples: convert the
frozen truncated witness
`cor312GapDict_exists_pointMap_pointHeightDictionary` through
`cor312GapDict_singletonVolume_toReal_le_iff`. -/
theorem cor312CarrierSpec_exists_pointMap_pointHeightDictionary (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (hdeg : ∀ b : Real, I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ∃ p : Nat → Nat → Nat → I.ThetaPilotPoint v,
      ∀ a b c : Nat, IsABCTriple a b c →
        I.sourceLocalLogDegree v (D.scaling * p a b c) ≤
          Height.logHeight₁ (abcRationalPoint a c) := by
  obtain ⟨p, hp⟩ := I.cor312GapDict_exists_pointMap_pointHeightDictionary v R n D hdeg
  exact ⟨p, fun a b c habc =>
    (I.cor312GapDict_singletonVolume_toReal_le_iff v _
      (cor312GapDict_abcRationalPoint_logHeight₁_nonneg habc)).mp (hp a b c habc)⟩

/-! ## 3. Derived shapes and joint refutability of the cards -/

/-- The weight dictionary in the frozen scaling-separated form:
`weight ≤ logDegree λ + logDegree q` (`cor312GapDict_weightDictionary_iff_scalingSeparated`). -/
theorem cor312CarrierSpec_weightDictionary_scalingSeparated (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    (hw : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v (D.scaling * p a b c)) :
    ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v D.scaling + I.sourceLocalLogDegree v (p a b c) :=
  fun a b c habc =>
    (I.cor312GapDict_weightDictionary_iff_scalingSeparated v D.scaling (p a b c) a c).mp
      (hw a b c habc)

/-- The scaling-free necessary condition of the weight dictionary:
`weight ≤ logDegree q` (`cor312GapDict_weightDictionary_implies_scalingFree` at the
frozen nonpositive scaling). -/
theorem cor312CarrierSpec_weightDictionary_scalingFree (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    (hw : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v (D.scaling * p a b c)) :
    ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤ I.sourceLocalLogDegree v (p a b c) :=
  fun a b c habc =>
    I.cor312GapDict_weightDictionary_implies_scalingFree v D.scaling (p a b c)
      D.scaling_logDegree_nonpos (hw a b c habc)

/-- **The weight and point-height dictionaries are jointly refutable.**  No point
map satisfies both dictionaries at a fixed scaling `lam`: at the ABC triple
`(1, 2, 3)` the two inequalities would give `log 6 ≤ logDegree (lam * p 1 2 3) ≤
log 3`, contradicting `log 3 < log 6`
(`cor312CarrierSpec_no_real_between_weight_and_height`). -/
theorem cor312CarrierSpec_dictionaries_jointly_refutable (v : V)
    (lam : I.ThetaPilotPoint v) :
    ¬ ∃ p : Nat → Nat → Nat → I.ThetaPilotPoint v,
      (∀ a b c : Nat, IsABCTriple a b c →
        arithmeticWeight (abcRationalPoint a c) ≤
          I.sourceLocalLogDegree v (lam * p a b c)) ∧
      (∀ a b c : Nat, IsABCTriple a b c →
        I.sourceLocalLogDegree v (lam * p a b c) ≤
          Height.logHeight₁ (abcRationalPoint a c)) := by
  rintro ⟨p, hw, hh⟩
  exact cor312CarrierSpec_no_real_between_weight_and_height
    ⟨I.sourceLocalLogDegree v (lam * p 1 2 3),
      hw 1 2 3 cor312CarrierSpec_isABCTriple_one_two_three,
      hh 1 2 3 cor312CarrierSpec_isABCTriple_one_two_three⟩

/-- **The frozen four-field package has no inhabitant.**  The two dictionary
fields alone are refutable at `(1, 2, 3)`, regardless of the membership and hunit
fields. -/
theorem cor312CarrierSpec_not_inhabited (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    (D₀ : ℝ) : ¬ Cor312CarrierRealizationSpec I v R n D p D₀ := by
  intro S
  exact cor312CarrierSpec_no_real_between_weight_and_height
    ⟨I.sourceLocalLogDegree v (D.scaling * p 1 2 3),
      S.weightDictionary 1 2 3 cor312CarrierSpec_isABCTriple_one_two_three,
      S.pointHeightDictionary 1 2 3 cor312CarrierSpec_isABCTriple_one_two_three⟩

/-- **The membership field and the weight dictionary are jointly refutable.**
Membership forces the log-degree of `λ * p abc` below the bounded region degree
`D.degreeBound`, while the dictionary forces it above the unbounded weight
(`cor312CarrierSpec_exists_isABCTriple_arithmeticWeight_gt`). -/
theorem cor312CarrierSpec_memUnitRegion_weightDictionary_jointly_refutable (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) :
    ¬ ∃ p : Nat → Nat → Nat → I.ThetaPilotPoint v,
      (∀ a b c : Nat, IsABCTriple a b c → p a b c ∈ D.unitRegion) ∧
      (∀ a b c : Nat, IsABCTriple a b c →
        arithmeticWeight (abcRationalPoint a c) ≤
          I.sourceLocalLogDegree v (D.scaling * p a b c)) := by
  rintro ⟨p, hmem, hw⟩
  obtain ⟨a, b, c, habc, hgt⟩ :=
    cor312CarrierSpec_exists_isABCTriple_arithmeticWeight_gt D.degreeBound
  have hpdeg : I.sourceLocalLogDegree v (p a b c) ≤ D.degreeBound :=
    D.unitRegion_logDegree_le (p a b c) (hmem a b c habc)
  have hscaled : I.sourceLocalLogDegree v (D.scaling * p a b c) ≤ D.degreeBound := by
    rw [I.sourceLocalLogDegree_mul v D.scaling (p a b c)]
    linarith [D.scaling_logDegree_nonpos, hpdeg]
  exact not_lt.mpr (le_trans (hw a b c habc) hscaled) hgt

/-! ## 4. Assembly: cards in, `Cor312EpsilonArithmeticComparison` out -/

/-- **Assembly from the two dictionaries alone (essential minimal card set).**
The membership field is discharged (the `hsplit`/`hptfin` inputs are the
unconditional supply-layer theorems) and the hunit comparison is instantiated at
the canonical constant (`cor312CarrierSpec_exists_hunitConstant`), so the two
dictionaries plus the valuation bound yield
`Cor312EpsilonArithmeticComparison W ε` at `W = I.sourceUnitRegionHaarInterface v R n D`
with `D₁ = 0` and the canonical `D₀`.  The proof is the constructive composition
of the frozen reductions; by `cor312CarrierSpec_not_inhabited` this hypothesis
family is refutable through its two cards, so the theorem stands as the exact
conditional interface for repaired packages of the same field shapes. -/
def cor312CarrierSpec_epsilonComparison_of_dictionaries (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : ℝ)) ≤ 1 + eps)
    (weightDictionary : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v (D.scaling * p a b c))
    (pointHeightDictionary : ∀ a b c : Nat, IsABCTriple a b c →
      I.sourceLocalLogDegree v (D.scaling * p a b c) ≤
        Height.logHeight₁ (abcRationalPoint a c)) :
    Cor312EpsilonArithmeticComparison
      (I.sourceUnitRegionHaarInterface v R n D) eps := by
  let hunitExists := cor312CarrierSpec_exists_hunitConstant I v R n D
  let D₀ : ℝ := Classical.choose hunitExists
  have hD₀ : 0 ≤ D₀ := (Classical.choose_spec hunitExists).1
  have hB : ENNReal.ofReal D.degreeBound ≤
      I.sourceHullVolume v R n + ENNReal.ofReal D₀ := (Classical.choose_spec hunitExists).2
  refine cor312GapAssembly_epsilonComparisonOfReducedInputs
    (D₁ := 0) (I.sourceUnitRegionHaarInterface v R n D) p heps hD₀ hval ?_ ?_ ?_ ?_ ?_
  · exact I.cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary v R n D p
      weightDictionary
  · exact I.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume v R n D
      hD₀ hB
  · exact I.cor312GapSupply_sourceInterface_hsplit v R n D p
  · exact fun a b c _ => I.cor312GapSupply_sourceInterface_hptfin v R n D p a b c
  · intro a b c habc
    change (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + 0
    simpa only [add_zero] using
      I.cor312GapDict_sourcePointBound_of_degree_le_height v R n D p
        heps hval pointHeightDictionary a b c habc

/-- **Assembly from the frozen four-field package: one package in, one
conclusion out.**  Consumes the package `S : Cor312CarrierRealizationSpec` (all
four frozen fields), the valuation bound, and `0 ≤ ε`.  The hunit field is
normalized to `max D₀ 0` (`cor312CarrierSpec_ofReal_max_zero`), the `hsplit` and
`hptfin` inputs are the unconditional supply-layer theorems (the membership field
is not needed), the weight dictionary becomes the gap-1 comparison, and the
point-height dictionary becomes the gap-2 point bound with `D₁ = 0`.  By
`cor312CarrierSpec_not_inhabited` the package is refutable through its two
dictionary fields, so this is a valid but vacuous conditional at the frozen
package; the proof is constructive and does not use the refutation. -/
def cor312CarrierSpec_epsilonComparison (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    {D₀ eps : ℝ} (heps : 0 ≤ eps)
    (hval : ∀ a b c : Nat, IsABCTriple a b c →
      ∀ q ∈ arithmeticPrimeSupport (abcRationalPoint a c),
        max 0 (-(padicValRat q (abcRationalPoint a c) : ℝ)) ≤ 1 + eps)
    (S : Cor312CarrierRealizationSpec I v R n D p D₀) :
    Cor312EpsilonArithmeticComparison
      (I.sourceUnitRegionHaarInterface v R n D) eps := by
  have hD₀' : 0 ≤ max D₀ 0 := le_max_right _ _
  have hB : ENNReal.ofReal D.degreeBound ≤
      I.sourceHullVolume v R n + ENNReal.ofReal (max D₀ 0) := by
    rw [cor312CarrierSpec_ofReal_max_zero D₀]
    exact S.hunitComparison
  refine cor312GapAssembly_epsilonComparisonOfReducedInputs
    (D₁ := 0) (I.sourceUnitRegionHaarInterface v R n D) p heps hD₀' hval ?_ ?_ ?_ ?_ ?_
  · exact I.cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary v R n D p
      S.weightDictionary
  · exact I.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume v R n D
      hD₀' hB
  · exact I.cor312GapSupply_sourceInterface_hsplit v R n D p
  · exact fun a b c _ => I.cor312GapSupply_sourceInterface_hptfin v R n D p a b c
  · intro a b c habc
    change (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + 0
    simpa only [add_zero] using
      I.cor312GapDict_sourcePointBound_of_degree_le_height v R n D p
        heps hval S.pointHeightDictionary a b c habc

/-- **Assembly from the two dictionaries plus the additive input (version-2
mirror of `cor312CarrierSpec_epsilonComparison_of_dictionaries`).**  The refuted
uniform valuation bound is replaced by the approved additive input
`height ≤ (1 + ε) · weight + A` (contract `ABCHeightWeightAdditiveBoundV2`,
IUT IV Theorem A shape); the two dictionary inputs, the canonical hunit
constant, and the unconditional `hsplit`/`hptfin` discharges are unchanged, and
the conclusion is the additive structure
`Cor312EpsilonArithmeticComparisonAdditive` with the explicit constant `A`.
The `hpoint` slot is supplied by the additive form of the
point-height-dictionary attachment with `D₁ = A`
(`cor312GapDict_sourcePointBound_of_additiveBound`). -/
def cor312CarrierSpec_epsilonComparisonAdditive_of_dictionaries (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    {eps A : ℝ} (heps : 0 ≤ eps)
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A)
    (weightDictionary : ∀ a b c : Nat, IsABCTriple a b c →
      arithmeticWeight (abcRationalPoint a c) ≤
        I.sourceLocalLogDegree v (D.scaling * p a b c))
    (pointHeightDictionary : ∀ a b c : Nat, IsABCTriple a b c →
      I.sourceLocalLogDegree v (D.scaling * p a b c) ≤
        Height.logHeight₁ (abcRationalPoint a c)) :
    Cor312EpsilonArithmeticComparisonAdditive
      (I.sourceUnitRegionHaarInterface v R n D) eps A := by
  let hunitExists := cor312CarrierSpec_exists_hunitConstant I v R n D
  let D₀ : ℝ := Classical.choose hunitExists
  have hD₀ : 0 ≤ D₀ := (Classical.choose_spec hunitExists).1
  have hB : ENNReal.ofReal D.degreeBound ≤
      I.sourceHullVolume v R n + ENNReal.ofReal D₀ := (Classical.choose_spec hunitExists).2
  refine cor312GapAssembly_epsilonComparisonOfAdditiveInput
    (D₁ := A) (I.sourceUnitRegionHaarInterface v R n D) p heps hD₀ hadd ?_ ?_ ?_ ?_ ?_
  · exact I.cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary v R n D p
      weightDictionary
  · exact I.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume v R n D
      hD₀ hB
  · exact I.cor312GapSupply_sourceInterface_hsplit v R n D p
  · exact fun a b c _ => I.cor312GapSupply_sourceInterface_hptfin v R n D p a b c
  · intro a b c habc
    change (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A
    exact I.cor312GapDict_sourcePointBound_of_additiveBound v R n D p
      heps hadd pointHeightDictionary a b c habc

/-- **Assembly from the frozen four-field package plus the additive input
(version-2 mirror of `cor312CarrierSpec_epsilonComparison`).**  Same package
consumption and hunit normalization as the original; the refuted uniform
valuation bound is replaced by the approved additive input and the conclusion
is the additive structure with the explicit constant `A`. -/
def cor312CarrierSpec_epsilonComparisonAdditive (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (p : Nat → Nat → Nat → I.ThetaPilotPoint v)
    {D₀ eps A : ℝ} (heps : 0 ≤ eps)
    (hadd : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A)
    (S : Cor312CarrierRealizationSpec I v R n D p D₀) :
    Cor312EpsilonArithmeticComparisonAdditive
      (I.sourceUnitRegionHaarInterface v R n D) eps A := by
  have hD₀' : 0 ≤ max D₀ 0 := le_max_right _ _
  have hB : ENNReal.ofReal D.degreeBound ≤
      I.sourceHullVolume v R n + ENNReal.ofReal (max D₀ 0) := by
    rw [cor312CarrierSpec_ofReal_max_zero D₀]
    exact S.hunitComparison
  refine cor312GapAssembly_epsilonComparisonOfAdditiveInput
    (D₁ := A) (I.sourceUnitRegionHaarInterface v R n D) p heps hD₀' hadd ?_ ?_ ?_ ?_ ?_
  · exact I.cor312GapSupply_sourceInterface_weightvol_of_degreeDictionary v R n D p
      S.weightDictionary
  · exact I.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume v R n D
      hD₀' hB
  · exact I.cor312GapSupply_sourceInterface_hsplit v R n D p
  · exact fun a b c _ => I.cor312GapSupply_sourceInterface_hptfin v R n D p a b c
  · intro a b c habc
    change (I.sourceSetVolume v {D.scaling * p a b c}).toReal ≤
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A
    exact I.cor312GapDict_sourcePointBound_of_additiveBound v R n D p
      heps hadd S.pointHeightDictionary a b c habc

end

end OriginalInput
end Theorem311Source

end LeanFormal.IUT
