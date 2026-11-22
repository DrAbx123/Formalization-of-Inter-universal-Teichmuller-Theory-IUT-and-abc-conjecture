import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierHaarData
import LeanFormal.IUT.Audit.Status

/-!
# Concrete carrier-model spike for the Corollary 3.12 carrier layer (task d5)

Companions (imported, none modified): `IQCarrierHaarData.lean`,
`SourceHullInterfaceDischarge.lean`, `SourceHullCompactnessReduction.lean`,
`SourceImageHull.lean`, `SourceImageHullVolume.lean`, and the frozen reduced-input
consumers `Cor312ComparisonGapReduction.lean` / `Cor312ComparisonGapSupplyLayer.lean`
(the assembly `cor312GapAssembly_epsilonComparisonOfReducedInputs` lands in
`Cor312EpsilonArithmeticComparison`, consumed by `cor312ToABCBridge_heightBound`).

## What this module is

A concrete real-line carrier model of the unit-region/Haar interface
(`IQHullLogVolumeInterface`), in the style of the calibration carriers
(`realLineHullData`, `singletonRealWitness`), together with the exact status of the
four d5 acceptance targets at this model:

* (a) unit-region membership `logShellPoint a b c in W.unitRegion`: provable for
  the model's unit-shell point (`iqCarrierModelUnitShellPoint`), but incompatible
  with the volume form of the weight dictionary at any carrier
  (`iqCarrierModel_hmem_hweightvol_incompatible`: the comparison region collapses
  to the scaled unit region, whose log-volume is finite, while arithmetic weights
  are unbounded).  The main model therefore keeps its named point outside the
  shell; the point carries the comparison volume, the shell is the bounded part.
* (b) the `hunit` normalization comparison: provable with `D₀ = 0`, in both the
  interface form (`iqCarrierModel_hunit_unitRegion`) and the reduced degree-bound
  form (`iqCarrierModel_hunit_degreeBound`).
* (c) the weight dictionary `arithmeticWeight x <= ld (lam * q)` at the model's
  own point map: provable with equality for the weight point
  `iqCarrierModelPointWeight` (`iqCarrierModel_weightDictionary`); this point also
  supplies `hweightvol` and `hpoint` (with `D₁ = 0`) for the frozen assembly.
* (d) the point-height dictionary `ld (lam * q) <= logHeight₁`: provable with
  equality for the separate height point `iqCarrierModelPointHeight`
  (`iqCarrierModel_pointHeightDictionary`); the single-map form of (c) and (d)
  together is refuted at the triple `(1, 2, 3)`, where the weight is `log 6` and
  the height is `log 3` (`iqCarrierModel_no_singleMap_bothDictionaries`,
  `iqCarrierModel_valueCarrier_no_jointDictionaries`).

## The d2 structural warning

`SourceHullInterfaceDischarge.lean:232-240` (with `SourceImageHullVolume.lean:376-448`)
proves that under pointwise degree faithfulness the value-monoid hull is unbounded,
so `ValueHullCompactnessInput` / `SourceUnitRegionHaarData` is unsatisfiable there.
The model bypasses this by construction, in the way the frozen audit prescribes:
its `hull` is explicit bounded hull data (`Set.Iic 0`, the closed log-shell of the
unit), not the least value-monoid candidate hull of `SourceImageHull.lean`; no
degree faithfulness is assumed, and the unboundedness statement (about the closure
under all nonzero-component scalings) does not apply to this datum.  The resolution
is exactly the additional carrier structure the frozen audit names: the paper's
hull lives in the ring-of-integers/O-module structure of the inductive-system
carrier, which is not a consequence of `OriginalInput`.

## Honest boundaries

The carrier is the real line; nothing here realizes the paper's inductive system,
fills a gap field of `Cor312EpsilonArithmeticComparison` at the value-realized
carrier, or bears on ABC.  The model's arithmetic point values are the actual tree
values `arithmeticWeight (abcRationalPoint a c)` and
`Height.logHeight₁ (abcRationalPoint a c)`; the `(1, 2, 3)` evaluations are
elementary exact computations (`natRadical 6 = 6`, `logHeight₁ (1/3) = log 3`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

universe u ua uv upi umon ui

noncomputable section

/-! ## 1. The concrete real-line carrier model -/

/-- The model log-degree: the additive mirror of the value-monoid degree, the
real number itself. -/
def iqCarrierModelLogDegree (x : Real) : Real := x

/-- The additive mirror of the multiplicativity of the log-degree
(`ld (lam * x) = ld lam + ld x`): translation adds. -/
theorem iqCarrierModelLogDegree_add (x y : Real) :
    iqCarrierModelLogDegree (x + y) =
      iqCarrierModelLogDegree x + iqCarrierModelLogDegree y :=
  rfl

/-- The model scaling has log-degree zero (the neutral scaling). -/
def iqCarrierModelScaling : Real := 0

/-- The model scaling shift: the additive mirror of `x |-> lam * x`. -/
def iqCarrierModelScaleShift (x : Real) : Real := iqCarrierModelScaling + x

/-- The model unit region: the closed log-shell `Set.Iic 0` of unit-modulus
points (the role of the ring-of-integers/log-shell region). -/
def iqCarrierModelUnitRegion : Set Real := Set.Iic 0

/-- The model log-degree bound of the unit region. -/
def iqCarrierModelUnitDegreeBound : Real := 0

/-- The model hull: explicit bounded hull data (the closed log-shell itself), the
role of the O-module hull of the inductive-system carrier.  It is deliberately
*not* the least value-monoid candidate hull of `SourceImageHull.lean`. -/
def iqCarrierModelHull : Set Real := Set.Iic 0

/-- The model image set (the theta-pilot image union inside the log-shell). -/
def iqCarrierModelImageSet : Set Real := Set.Iic 0

/-- Every point of the model unit region has log-degree at most the model bound. -/
theorem iqCarrierModelUnitRegion_logDegree_le :
    forall y, y ∈ iqCarrierModelUnitRegion ->
      iqCarrierModelLogDegree y <= iqCarrierModelUnitDegreeBound :=
  fun _ hy => hy

/-- The model scaling of the unit region is the unit region itself. -/
theorem iqCarrierModelScaleShift_image_unitRegion :
    iqCarrierModelScaleShift '' iqCarrierModelUnitRegion = iqCarrierModelUnitRegion := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [iqCarrierModelScaleShift, iqCarrierModelScaling] using hy
  · intro hx
    exact ⟨x, hx, by simp [iqCarrierModelScaleShift, iqCarrierModelScaling]⟩

/-- The scaled unit region in the unfolded realizability form used by the
interface fields: the image of the closed log-shell under the model scaling is the
closed log-shell itself. -/
theorem iqCarrierModelScaleShift_image_Iic_zero :
    iqCarrierModelScaleShift '' Set.Iic (0 : Real) = Set.Iic (0 : Real) :=
  iqCarrierModelScaleShift_image_unitRegion

/-- The model log-volume of the log-shell is zero (the sup of `ofReal` over
nonpositive reals). -/
theorem iqCarrierModelLogVolume_Iic_zero :
    realLineLogVolume (Set.Iic (0 : Real)) = 0 := by
  refine le_antisymm ?_ bot_le
  refine iSup_le fun x => iSup_le fun hx => ?_
  rw [Set.mem_Iic] at hx
  exact le_of_eq (ENNReal.ofReal_of_nonpos hx)

/-- The model log-volume of the log-shell with an added point `y` is
`ofReal (max y 0)`. -/
theorem iqCarrierModelLogVolume_Iic_zero_union (y : Real) :
    realLineLogVolume (Set.Iic (0 : Real) ∪ {y}) = ENNReal.ofReal (max y 0) := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun x => iSup_le fun hx => ?_
    rcases hx with hx | hx
    · rw [Set.mem_Iic] at hx
      rw [ENNReal.ofReal_of_nonpos hx]
      exact zero_le
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ENNReal.ofReal_le_ofReal (le_max_left y 0)
  · by_cases hy : 0 <= y
    · rw [max_eq_left hy]
      exact le_iSup_of_le y (le_iSup_of_le (by simp) le_rfl)
    · calc ENNReal.ofReal (max y 0) = ENNReal.ofReal 0 :=
            congrArg ENNReal.ofReal (max_eq_right (le_of_lt (not_le.mp hy)))
        _ = 0 := ENNReal.ofReal_zero
        _ <= realLineLogVolume (Set.Iic (0 : Real) ∪ {y}) := zero_le

/-- Subadditivity of the model log-volume over unions (the sup structure), the
mirror of `cor312GapSupply_sourceSetVolume_union_le` at the model. -/
theorem iqCarrierModelLogVolume_union_le (S T : Set Real) :
    realLineLogVolume (S ∪ T) <= realLineLogVolume S + realLineLogVolume T := by
  unfold realLineLogVolume
  refine iSup_le fun x => iSup_le fun hx => ?_
  rcases hx with hx | hx
  · have h1 : ENNReal.ofReal x <= (iSup fun y : Real => (iSup fun _ : y ∈ S => ENNReal.ofReal y)) :=
      le_iSup_of_le x (le_iSup_of_le hx le_rfl)
    have h2 : (iSup fun y : Real => (iSup fun _ : y ∈ S => ENNReal.ofReal y)) <=
        (iSup fun y : Real => (iSup fun _ : y ∈ S => ENNReal.ofReal y)) +
          (iSup fun y : Real => (iSup fun _ : y ∈ T => ENNReal.ofReal y)) := by
      simpa only [bot_eq_zero, add_zero] using
        add_le_add (le_refl (iSup fun y : Real => (iSup fun _ : y ∈ S => ENNReal.ofReal y)))
          (bot_le : (0 : ENNReal) <=
            (iSup fun y : Real => (iSup fun _ : y ∈ T => ENNReal.ofReal y)))
    exact le_trans h1 h2
  · have h1 : ENNReal.ofReal x <= (iSup fun y : Real => (iSup fun _ : y ∈ T => ENNReal.ofReal y)) :=
      le_iSup_of_le x (le_iSup_of_le hx le_rfl)
    have h2 : (iSup fun y : Real => (iSup fun _ : y ∈ T => ENNReal.ofReal y)) <=
        (iSup fun y : Real => (iSup fun _ : y ∈ S => ENNReal.ofReal y)) +
          (iSup fun y : Real => (iSup fun _ : y ∈ T => ENNReal.ofReal y)) := by
      simpa only [bot_eq_zero, zero_add] using
        add_le_add (bot_le : (0 : ENNReal) <=
          (iSup fun y : Real => (iSup fun _ : y ∈ S => ENNReal.ofReal y)))
          (le_refl (iSup fun y : Real => (iSup fun _ : y ∈ T => ENNReal.ofReal y)))
    exact le_trans h1 h2

/-- The concrete real-line carrier model of the unit-region/Haar interface. -/
def iqCarrierModelInterface : IQHullLogVolumeInterface Real where
  imageSet := iqCarrierModelImageSet
  hull := iqCarrierModelHull
  imageSet_subset_hull := fun _ hx => hx
  logVolume := realLineLogVolume
  logVolume_mono := fun hST => realLineLogVolume_mono hST
  unitRegion := iqCarrierModelUnitRegion
  scaleShift := iqCarrierModelScaleShift
  hull_subset_scaleShift := by
    intro x hx
    exact ⟨x, hx, by simp [iqCarrierModelScaleShift, iqCarrierModelScaling]⟩
  unitRegion_logVolume_lt_top := by
    change realLineLogVolume (Set.Iic (0 : Real)) < ⊤
    rw [iqCarrierModelLogVolume_Iic_zero]
    exact ENNReal.zero_lt_top
  scaleShift_unitRegion_logVolume_le := by
    change realLineLogVolume (iqCarrierModelScaleShift '' Set.Iic (0 : Real)) <=
      realLineLogVolume (Set.Iic (0 : Real))
    calc realLineLogVolume (iqCarrierModelScaleShift '' Set.Iic (0 : Real))
        = realLineLogVolume (Set.Iic (0 : Real)) :=
          congrArg realLineLogVolume iqCarrierModelScaleShift_image_Iic_zero
      _ <= realLineLogVolume (Set.Iic (0 : Real)) := le_rfl

/-! ## 2. Point data: the weight point, the height point, the shell point -/

/-- The weight point of the model at the ABC triple `(a, b, c)`: the actual
arithmetic weight of the tree's rational-point dictionary. -/
def iqCarrierModelPointWeight (a b c : Nat) : Real :=
  arithmeticWeight (abcRationalPoint a c)

/-- The height point of the model at the triple `(a, b, c)`: the actual
logarithmic height of the tree's rational-point dictionary. -/
def iqCarrierModelPointHeight (a b c : Nat) : Real :=
  Height.logHeight₁ (abcRationalPoint a c)

/-- The named point datum of the model used by the frozen consumers: the weight
point, deliberately outside the unit region. -/
def iqCarrierModelLogShellPoint (a b c : Nat) : Real :=
  iqCarrierModelPointWeight a b c

/-- The unit-shell point: the zero log-degree point, which does lie in the model
unit region. -/
def iqCarrierModelUnitShellPoint (_a _b _c : Nat) : Real := 0

/-- The model weight point is nonnegative. -/
theorem iqCarrierModelPointWeight_nonneg (a b c : Nat) :
    0 <= iqCarrierModelPointWeight a b c :=
  arithmeticWeight_nonneg _

/-- The unit-shell point lies in the model unit region (target (a), realizable). -/
theorem iqCarrierModelUnitShellPoint_mem_unitRegion (a b c : Nat) :
    iqCarrierModelUnitShellPoint a b c ∈ iqCarrierModelUnitRegion := by
  change iqCarrierModelUnitShellPoint a b c <= (0 : Real)
  rw [iqCarrierModelUnitShellPoint]

/-! ## 3. Exact evaluations at the triple `(1, 2, 3)` -/

/-- The project radical at `6`. -/
theorem iqCarrierModel_radical_six : natRadical 6 = 6 := by
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

/-- The weight point at `(1, 2, 3)` is `log 6`. -/
theorem iqCarrierModel_pointWeight_triple_123 :
    iqCarrierModelPointWeight 1 2 3 = Real.log 6 := by
  have h123 : IsABCTriple 1 2 3 :=
    ⟨Nat.one_pos, by norm_num, by norm_num, Nat.coprime_one_left 2⟩
  have hcast : (natRadical 6 : Real) = 6 := by
    rw [iqCarrierModel_radical_six]
    norm_num
  calc iqCarrierModelPointWeight 1 2 3
      = Real.log (natRadical (1 * 2 * 3) : Real) :=
        arithmeticWeight_abcRationalPoint h123
    _ = Real.log (natRadical 6 : Real) := by
        rw [show (1 * 2 * 3 : Nat) = 6 by norm_num]
    _ = Real.log 6 := by rw [hcast]

/-- The height point at `(1, 2, 3)` is `log 3`. -/
theorem iqCarrierModel_pointHeight_triple_123 :
    iqCarrierModelPointHeight 1 2 3 = Real.log 3 := by
  have h123 : IsABCTriple 1 2 3 :=
    ⟨Nat.one_pos, by norm_num, by norm_num, Nat.coprime_one_left 2⟩
  simpa [iqCarrierModelPointHeight] using abcRationalPoint_logHeight₁ h123

/-- **Target (a) is not free.**  The model's named point (the weight point) is
not in the unit region: at the triple `(1, 2, 3)` its log-degree is `log 6 > 0`. -/
theorem iqCarrierModelLogShellPoint_triple_123_not_mem :
    iqCarrierModelLogShellPoint 1 2 3 ∉ iqCarrierModelUnitRegion := by
  intro hmem
  have hle : iqCarrierModelPointWeight 1 2 3 <= (0 : Real) := hmem
  have hgt : (0 : Real) < iqCarrierModelPointWeight 1 2 3 := by
    rw [iqCarrierModel_pointWeight_triple_123]
    exact Real.log_pos (by norm_num)
  linarith

/-! ## 4. Target (b): the hunit normalization comparison with `D₀ = 0` -/

/-- **Target (b), interface form.**  `hunit` holds at the model with `D₀ = 0`:
the unit-region log-volume is at most the hull log-volume (they coincide). -/
theorem iqCarrierModel_hunit_unitRegion :
    iqCarrierModelInterface.logVolume iqCarrierModelInterface.unitRegion <=
      iqCarrierModelInterface.logVolume iqCarrierModelInterface.hull +
        ENNReal.ofReal 0 := by
  change realLineLogVolume (Set.Iic (0 : Real)) <=
    realLineLogVolume (Set.Iic (0 : Real)) + ENNReal.ofReal 0
  calc realLineLogVolume (Set.Iic (0 : Real)) = 0 := iqCarrierModelLogVolume_Iic_zero
    _ <= realLineLogVolume (Set.Iic (0 : Real)) + ENNReal.ofReal 0 := zero_le

/-- **Target (b), reduced degree-bound form.**  `ofReal degreeBound <= hull volume
+ ofReal D₀` holds at the model with `D₀ = 0`; this is the minimal form consumed by
the frozen supply layer. -/
theorem iqCarrierModel_hunit_degreeBound :
    ENNReal.ofReal iqCarrierModelUnitDegreeBound <=
      iqCarrierModelInterface.logVolume iqCarrierModelInterface.hull +
        ENNReal.ofReal 0 := by
  change ENNReal.ofReal (0 : Real) <= realLineLogVolume (Set.Iic (0 : Real)) +
    ENNReal.ofReal 0
  calc ENNReal.ofReal (0 : Real) = 0 := ENNReal.ofReal_zero
    _ <= realLineLogVolume (Set.Iic (0 : Real)) + ENNReal.ofReal 0 := zero_le

/-! ## 5. The five reduced inputs at the model -/

/-- The comparison region of the model at the named point is the log-shell with
the point added, of volume `ofReal` of the point's weight. -/
theorem iqCarrierModelLogVolume_region_eq (a b c : Nat) :
    iqCarrierModelInterface.logVolume
        (normalizedComparisonRegion iqCarrierModelInterface
          iqCarrierModelLogShellPoint a b c) =
      ENNReal.ofReal (iqCarrierModelPointWeight a b c) := by
  change realLineLogVolume
      (iqCarrierModelScaleShift ''
        (iqCarrierModelUnitRegion ∪ {iqCarrierModelLogShellPoint a b c})) =
    ENNReal.ofReal (iqCarrierModelPointWeight a b c)
  rw [Set.image_union, iqCarrierModelScaleShift_image_unitRegion, Set.image_singleton]
  have hpt : iqCarrierModelScaleShift (iqCarrierModelLogShellPoint a b c) =
      iqCarrierModelPointWeight a b c := by
    simp [iqCarrierModelScaleShift, iqCarrierModelScaling, iqCarrierModelLogShellPoint]
  rw [hpt, iqCarrierModelUnitRegion, iqCarrierModelLogVolume_Iic_zero_union,
    max_eq_left (iqCarrierModelPointWeight_nonneg a b c)]

/-- `hweightvol` at the model: the weight is at most the comparison-region volume,
with equality. -/
theorem iqCarrierModel_hweightvol :
    forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        (iqCarrierModelInterface.logVolume
          (normalizedComparisonRegion iqCarrierModelInterface
            iqCarrierModelLogShellPoint a b c)).toReal := by
  intro a b c _
  rw [iqCarrierModelLogVolume_region_eq a b c,
    ENNReal.toReal_ofReal (iqCarrierModelPointWeight_nonneg a b c)]
  exact le_of_eq rfl

/-- `hsplit` at the model: subadditivity over the two components of the region. -/
theorem iqCarrierModel_hsplit :
    forall a b c : Nat, IsABCTriple a b c ->
      iqCarrierModelInterface.logVolume
          (normalizedComparisonRegion iqCarrierModelInterface
            iqCarrierModelLogShellPoint a b c) <=
        iqCarrierModelInterface.logVolume
            (iqCarrierModelInterface.scaleShift '' iqCarrierModelInterface.unitRegion) +
          iqCarrierModelInterface.logVolume
            {iqCarrierModelInterface.scaleShift
              (iqCarrierModelLogShellPoint a b c)} := by
  intro a b c _
  rw [cor312Gap2_normalizedComparisonRegion_eq_scaleShift_union]
  exact iqCarrierModelLogVolume_union_le _ _

/-- `hptfin` at the model: the scaled point has finite log-volume. -/
theorem iqCarrierModel_hptfin :
    forall a b c : Nat, IsABCTriple a b c ->
      iqCarrierModelInterface.logVolume
        {iqCarrierModelInterface.scaleShift
          (iqCarrierModelLogShellPoint a b c)} < ⊤ := by
  intro a b c _
  change realLineLogVolume
    {iqCarrierModelScaleShift (iqCarrierModelLogShellPoint a b c)} < ⊤
  rw [realLineLogVolume_singleton]
  exact ENNReal.ofReal_lt_top

/-- `hpoint` at the model with `D₁ = 0`, in the two-sided `(1 + eps)`-weight form
(the form the assembly consumes; the strict height dictionary is *not* used). -/
theorem iqCarrierModel_hpoint {eps : Real} (heps : 0 <= eps) :
    forall a b c : Nat, IsABCTriple a b c ->
      (iqCarrierModelInterface.logVolume
        {iqCarrierModelInterface.scaleShift
          (iqCarrierModelLogShellPoint a b c)}).toReal <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + 0 := by
  intro a b c _
  have hw := iqCarrierModelPointWeight_nonneg a b c
  change (realLineLogVolume
    {iqCarrierModelScaleShift (iqCarrierModelLogShellPoint a b c)}).toReal <=
    (1 + eps) * arithmeticWeight (abcRationalPoint a c) + 0
  have h0 : (0 : Real) <= iqCarrierModelScaleShift (iqCarrierModelLogShellPoint a b c) := by
    simpa [iqCarrierModelScaleShift, iqCarrierModelScaling, iqCarrierModelLogShellPoint]
      using hw
  rw [realLineLogVolume_singleton, ENNReal.toReal_ofReal h0]
  simp only [iqCarrierModelScaleShift, iqCarrierModelScaling, zero_add, add_zero,
    iqCarrierModelLogShellPoint, iqCarrierModelPointWeight]
  calc arithmeticWeight (abcRationalPoint a c)
      = 1 * arithmeticWeight (abcRationalPoint a c) := (one_mul _).symm
    _ <= (1 + eps) * arithmeticWeight (abcRationalPoint a c) :=
        mul_le_mul_of_nonneg_right (by linarith) hw

/-- **The frozen assembly fires at the model.**  From the five inputs above and
the H1 valuation bound (the named arithmetic input of the frozen reduction), the
assembly produces `Cor312EpsilonArithmeticComparison` at the model for every
`eps >= 0`.  This is a consistency check of the reduced-input set at a concrete
carrier, not a proof of the gaps at the value-realized carrier. -/
def iqCarrierModel_epsilonComparison {eps : Real} (heps : 0 <= eps)
    (hval : forall a b c : Nat, IsABCTriple a b c ->
      forall q, q ∈ arithmeticPrimeSupport (abcRationalPoint a c) ->
        max 0 (-(padicValRat q (abcRationalPoint a c) : Real)) <= 1 + eps) :
    Cor312EpsilonArithmeticComparison iqCarrierModelInterface eps :=
  cor312GapAssembly_epsilonComparisonOfReducedInputs
    (W := iqCarrierModelInterface) (logShellPoint := iqCarrierModelLogShellPoint)
    (D₀ := 0) (D₁ := 0) heps le_rfl hval iqCarrierModel_hweightvol
    iqCarrierModel_hunit_unitRegion iqCarrierModel_hsplit iqCarrierModel_hptfin
    (fun a b c habc => iqCarrierModel_hpoint heps a b c habc)

/-- **The frozen assembly fires at the model, additive form (version-2 mirror of
`iqCarrierModel_epsilonComparison`).**  The refuted uniform valuation bound is
replaced by the approved additive input `height ≤ (1 + ε) · weight + A`
(contract `ABCHeightWeightAdditiveBoundV2`, IUT IV Theorem A shape); the five
model inputs are the same unconditional theorems, and the conclusion is the
additive structure `Cor312EpsilonArithmeticComparisonAdditive` with the
explicit constant `A`. -/
def iqCarrierModel_epsilonComparisonAdditive {eps A : Real} (heps : 0 <= eps)
    (hadd : forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c) <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A) :
    Cor312EpsilonArithmeticComparisonAdditive iqCarrierModelInterface eps A :=
  cor312GapAssembly_epsilonComparisonOfAdditiveInput
    (W := iqCarrierModelInterface) (logShellPoint := iqCarrierModelLogShellPoint)
    (D₀ := 0) (D₁ := 0) heps le_rfl hadd iqCarrierModel_hweightvol
    iqCarrierModel_hunit_unitRegion iqCarrierModel_hsplit iqCarrierModel_hptfin
    (fun a b c habc => iqCarrierModel_hpoint heps a b c habc)

/-! ## 6. Targets (c) and (d) and the single-map obstruction -/

/-- **Target (c).**  The weight dictionary holds at the model's own point map,
with equality: the weight point realizes exactly the arithmetic weight. -/
theorem iqCarrierModel_weightDictionary :
    forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        iqCarrierModelLogDegree
          (iqCarrierModelScaleShift (iqCarrierModelLogShellPoint a b c)) := by
  intro a b c _
  change arithmeticWeight (abcRationalPoint a c) <=
    0 + arithmeticWeight (abcRationalPoint a c)
  linarith

/-- **Target (d).**  The point-height dictionary (minimal real form) holds at the
model's separate height point map, with equality. -/
theorem iqCarrierModel_pointHeightDictionary :
    forall a b c : Nat, IsABCTriple a b c ->
      iqCarrierModelLogDegree
          (iqCarrierModelScaleShift (iqCarrierModelPointHeight a b c)) <=
        Height.logHeight₁ (abcRationalPoint a c) := by
  intro a b c _
  change 0 + Height.logHeight₁ (abcRationalPoint a c) <=
    Height.logHeight₁ (abcRationalPoint a c)
  exact le_of_eq (zero_add _)

/-- **The single-map form of (c) plus (d) is refuted** for any real-valued point
datum: no `r` can satisfy the weight dictionary and the point-height dictionary at
the same time, because at the triple `(1, 2, 3)` this would force
`log 6 <= log 3`.  This is a pure arithmetic fact about the tree's dictionaries,
independent of any carrier. -/
theorem iqCarrierModel_no_singleMap_bothDictionaries (r : Nat -> Nat -> Nat -> Real) :
    Not (forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <= r a b c ∧
        r a b c <= Height.logHeight₁ (abcRationalPoint a c)) := by
  intro h
  have h123 : IsABCTriple 1 2 3 :=
    ⟨Nat.one_pos, by norm_num, by norm_num, Nat.coprime_one_left 2⟩
  obtain ⟨hle1, hle2⟩ := h 1 2 3 h123
  have hbad : Real.log 6 <= Real.log 3 := by
    calc Real.log 6 = arithmeticWeight (abcRationalPoint 1 3) :=
          iqCarrierModel_pointWeight_triple_123.symm
      _ <= r 1 2 3 := hle1
      _ <= Height.logHeight₁ (abcRationalPoint 1 3) := hle2
      _ = Real.log 3 := by
            simpa [iqCarrierModelPointHeight] using iqCarrierModel_pointHeight_triple_123
  exact absurd hbad
    (not_le.mpr (Real.log_lt_log (by norm_num) (by norm_num)))

/-! ## 7. Structural finding: shell membership versus the weight volume -/

/-- The arithmetic weights of the tree's ABC rational points are unbounded: the
triples `(1, p, p + 1)` for primes `p` have weight at least `log p`. -/
theorem iqCarrierModel_arithmeticWeight_unbounded (C : Real) :
    exists a b c : Nat, IsABCTriple a b c ∧
      C < arithmeticWeight (abcRationalPoint a c) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp C)
  obtain ⟨p, hnp, hpprime⟩ := Nat.exists_infinite_primes n
  have htriple : IsABCTriple 1 p (p + 1) :=
    ⟨Nat.one_pos, hpprime.pos, Nat.add_comm 1 p, Nat.coprime_one_left p⟩
  refine ⟨1, p, p + 1, htriple, ?_⟩
  have hcop : Nat.Coprime p (p + 1) :=
    Nat.coprime_self_add_right.mpr (Nat.coprime_one_right p)
  have hprad : natRadical p = p := by
    rw [natRadical_eq_prod_primeFactors, hpprime.primeFactors]
    simp
  have hrad : natRadical (p * (p + 1)) = p * natRadical (p + 1) := by
    rw [natRadical_mul_of_coprime hcop, hprad]
  have hge : p <= natRadical (1 * p * (p + 1)) := by
    rw [show (1 * p * (p + 1) : Nat) = p * (p + 1) by ring, hrad]
    exact Nat.le_mul_of_pos_right p (natRadical_pos (p + 1))
  have hlog : (p : Real) <= (natRadical (1 * p * (p + 1)) : Real) := by
    exact_mod_cast hge
  have hpgt : Real.exp C < (p : Real) :=
    lt_of_lt_of_le hn (by exact_mod_cast hnp)
  have hCp : C < Real.log (p : Real) :=
    (Real.lt_log_iff_exp_lt (by exact_mod_cast hpprime.pos)).mpr hpgt
  calc C < Real.log (p : Real) := hCp
    _ <= Real.log (natRadical (1 * p * (p + 1)) : Real) :=
        Real.log_le_log (by exact_mod_cast hpprime.pos) hlog
    _ = arithmeticWeight (abcRationalPoint 1 (p + 1)) :=
        (arithmeticWeight_abcRationalPoint htriple).symm

/-- **Target (a) versus the weight supply.**  At *any* interface, if the named
point lies in the unit region on every ABC triple then the volume form of the
weight dictionary cannot hold: the comparison region collapses to the scaled unit
region, whose log-volume is finite, while the arithmetic weights are unbounded.
The shell-membership datum and the weight-carrying point are therefore mutually
exclusive; the working supply keeps the point outside the shell. -/
theorem iqCarrierModel_hmem_hweightvol_incompatible {X : Type u}
    (W : IQHullLogVolumeInterface X) (logShellPoint : Nat -> Nat -> Nat -> X)
    (hmem : forall a b c : Nat, IsABCTriple a b c ->
      logShellPoint a b c ∈ W.unitRegion) :
    Not (forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        (W.logVolume
          (normalizedComparisonRegion W logShellPoint a b c)).toReal) := by
  intro hweightvol
  obtain ⟨a, b, c, habc, hgt⟩ :=
    iqCarrierModel_arithmeticWeight_unbounded (W.logVolume W.unitRegion).toReal
  have hunion : W.unitRegion ∪ {logShellPoint a b c} = W.unitRegion :=
    Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr (hmem a b c habc))
  have hregion : normalizedComparisonRegion W logShellPoint a b c =
      W.scaleShift '' W.unitRegion := by
    unfold normalizedComparisonRegion
    rw [hunion]
  have hle : (W.logVolume
        (normalizedComparisonRegion W logShellPoint a b c)).toReal <=
      (W.logVolume W.unitRegion).toReal := by
    rw [hregion]
    exact ENNReal.toReal_mono (ne_of_lt W.unitRegion_logVolume_lt_top)
      W.scaleShift_unitRegion_logVolume_le
  linarith [hweightvol a b c habc]

/-- The unit-shell point does satisfy (a) at the model, and consequently the
volume form of the weight dictionary fails for it (an instance of the general
incompatibility above). -/
theorem iqCarrierModel_not_hweightvol_unitShellPoint :
    Not (forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c) <=
        (iqCarrierModelInterface.logVolume
          (normalizedComparisonRegion iqCarrierModelInterface
            iqCarrierModelUnitShellPoint a b c)).toReal) :=
  iqCarrierModel_hmem_hweightvol_incompatible iqCarrierModelInterface
    iqCarrierModelUnitShellPoint
    (fun a b c _ => iqCarrierModelUnitShellPoint_mem_unitRegion a b c)

end

/-! ## 8. Consequences at the value-realized carrier -/

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Under pointwise degree faithfulness the unit-region/Haar datum of the
value-realized carrier is empty (it maps into `ValueHullCompactnessInput`, which
is refuted there by the frozen theorem): the conditional existence witnesses that
assume both the datum and faithfulness are vacuous at the realized carrier. -/
theorem iqCarrierModel_sourceHaarData_not_nonempty_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    Not (Nonempty (I.SourceUnitRegionHaarData v R n)) := by
  rintro ⟨D⟩
  exact I.not_nonempty_valueHullCompactnessInput_of_degreeFaithful v R n hdeg
    ⟨I.sourceUnitRegionHaarData_to_compactnessInput v R n D⟩

/-- At the value-realized carrier, unit-region membership of the point map is
incompatible with the degree-weight dictionary: membership bounds the point's
log-degree by the constant `ld scaling + degreeBound`, while the weights are
unbounded. -/
theorem iqCarrierModel_valueCarrier_hmem_degreeDictionary_incompatible (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (p : Nat -> Nat -> Nat -> I.ThetaPilotPoint v) :
    Not ((forall a b c : Nat, IsABCTriple a b c -> p a b c ∈ D.unitRegion) ∧
      (forall a b c : Nat, IsABCTriple a b c ->
        arithmeticWeight (abcRationalPoint a c) <=
          I.sourceLocalLogDegree v (D.scaling * p a b c))) := by
  rintro ⟨hmem, hdict⟩
  obtain ⟨a, b, c, habc, hgt⟩ := iqCarrierModel_arithmeticWeight_unbounded
    (I.sourceLocalLogDegree v D.scaling + D.degreeBound)
  have h1 := hdict a b c habc
  rw [I.sourceLocalLogDegree_mul] at h1
  have h2 := D.unitRegion_logDegree_le (p a b c) (hmem a b c habc)
  linarith

/-- At the value-realized carrier, no single point map satisfies the weight
dictionary and the point-height dictionary of the task simultaneously: the
dictionaries would force `log 6 <= log 3` at the triple `(1, 2, 3)`.  Any carrier
realization must route the `hpoint` slot through the two-sided `(1 + eps)`-weight
form instead (as the real-line model above does). -/
theorem iqCarrierModel_valueCarrier_no_jointDictionaries (v : V)
    (lam : I.ThetaPilotPoint v) (p : Nat -> Nat -> Nat -> I.ThetaPilotPoint v) :
    Not ((forall a b c : Nat, IsABCTriple a b c ->
        arithmeticWeight (abcRationalPoint a c) <=
          I.sourceLocalLogDegree v (lam * p a b c)) ∧
      (forall a b c : Nat, IsABCTriple a b c ->
        I.sourceLocalLogDegree v (lam * p a b c) <=
          Height.logHeight₁ (abcRationalPoint a c))) := by
  intro h
  exact iqCarrierModel_no_singleMap_bothDictionaries
    (fun a b c => I.sourceLocalLogDegree v (lam * p a b c))
    (fun a b c habc => ⟨h.1 a b c habc, h.2 a b c habc⟩)

end OriginalInput
end Theorem311Source

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the concrete carrier-model spike of the Corollary 3.12
carrier layer (task d5): the real-line model, the five reduced inputs it realizes
at the weight point, and the three proved structural findings. -/
def iqCarrierConcreteModel : Obligation :=
  { id := "IUT-III.corollary-3.12-iq-carrier-concrete-model-spike"
    source :=
      "Corollary 3.12 carrier-layer task d5; companions: IQCarrierHaarData.lean, " ++
        "SourceHullInterfaceDischarge.lean, Cor312ComparisonGapReduction.lean, " ++
        "Cor312ComparisonGapSupplyLayer.lean"
    status := VerificationStatus.interface
    note :=
      "Concrete real-line carrier model of IQHullLogVolumeInterface with explicit " ++
        "bounded hull data (the closed log-shell), bypassing the d2 degree-faithfulness " ++
        "obstruction by construction (no value-monoid closure, no faithfulness " ++
        "hypothesis). At the model's weight point (the actual arithmeticWeight values) " ++
        "the five reduced inputs of cor312GapAssembly_epsilonComparisonOfReducedInputs " ++
        "hold (hunit with D₀ = 0 in both forms; hsplit by sup-subadditivity; hptfin; " ++
        "hweightvol with equality; hpoint with D₁ = 0 in the two-sided (1 + eps)-weight " ++
        "form), so the frozen assembly fires at the model given the H1 valuation bound. " ++
        "Proved structural findings: (F1) no single point datum satisfies the weight " ++
        "dictionary and the point-height dictionary jointly ((1,2,3): weight log 6 > " ++
        "height log 3), at the model and at the value-realized carrier; (F2) the " ++
        "unit-region-membership datum is incompatible with the volume weight " ++
        "comparison at any interface (region collapses to the finite scaled unit " ++
        "region versus unbounded weights) and with the degree dictionary at the " ++
        "realized carrier; (F3) under degree faithfulness SourceUnitRegionHaarData is " ++
        "empty, so conditional existence witnesses assuming it together with " ++
        "faithfulness are vacuous at the realized carrier. NOT proved: realization of " ++
        "the paper carrier, any gap field of Cor312EpsilonArithmeticComparison, and " ++
        "any arithmetic statement; the model is a consistency and supply-pattern " ++
        "spike on the real line."
    dependsOn :=
      [ "IUT-III.corollary-3.12-iq-hull-log-volume-interface",
        "IUT-III.corollary-3.12-iq-carrier-haar-data",
        "IUT-III.cor312-comparison-gap-reduction" ] }

end LeanFormal.IUT.Audit
