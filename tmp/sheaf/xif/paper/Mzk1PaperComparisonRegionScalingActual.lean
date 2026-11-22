/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import Mathlib.Tactic

/-!
# A622 paper comparison REGION with triple-dependent scaling (mainline)

`Mzk1S1902BridgeInterfaceActual` used the actual S1902 hull interface, but that
interface's `scaleShift` is the identity: specializing `comparisonRegion` to it makes
the height comparison pointwise-false (A618 audit: e.g. 3 + 125 = 128, height exceeds
the arithmetic weight).  This file therefore exposes the **triple-dependent scaling**
shape of the paper comparison region, without changing any green file or theorem
conclusion:

* `tripleScale a b c : S1902Carrier T → S1902Carrier T` is the triple-indexed scaling
  (a nonzero natural multiple, so it genuinely depends on `(a,b,c)`);
* `paperComparisonRegion point a b c := tripleScale a b c '' (unitRegion ∪ {point a b c})`,
  matching the paper shape `region a b c = scale(a,b,c) '' (O ∪ {pt a b c})`;
* `TripleDependentComparison` keeps the two IUT IV Thm 1.10 inequalities as explicit
  epsilon-form fields (Gap1 height comparison, Gap2 region log-volume bound);
* `abc_of_tripleComparison` derives `ABCConjecture` through the generic green
  `heightWeightBound_of_normalizedVolumeComparison`.

No object is changed; the two inequalities remain named inputs.  ABC gate NOT passed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **Triple-dependent scaling** of the S1902 carrier: a nonzero natural multiple
  depending on the ABC triple.  (The identity `scaleShift` of the actual hull cannot
  support the paper's height comparison; see A618.) -/
noncomputable def tripleScale (a b c : Nat) : S1902Carrier T → S1902Carrier T :=
  fun x v => (a + b + c + 1) • x v

/-- The paper comparison region: the triple-scaled unit region together with the
  triple-indexed point datum. -/
noncomputable def paperComparisonRegion
    (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) : Set (S1902Carrier T) :=
  tripleScale T a b c '' (s1902UnitRegion T ∪ {point a b c})

/-- The region has exactly the paper shape `scale '' (unitRegion ∪ {pt})`. -/
theorem paperComparisonRegion_shape
    (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) :
    paperComparisonRegion T point a b c =
      tripleScale T a b c '' (s1902UnitRegion T ∪ {point a b c}) := rfl

/-- The two named IUT IV Thm 1.10 inequalities on the triple-dependent region. -/
structure TripleDependentComparison
    (point : Nat → Nat → Nat → S1902Carrier T) where
  /-- Gap 1: the ε-normalized height comparison with the region log-volume. -/
  height_le_regionVolume : ∀ ε : ℝ, 0 < ε → ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + ε) * (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal
  /-- Gap 2: the ε-normalized region log-volume bound (`D` may depend on `ε`). -/
  regionVolume_le_weight : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ,
    ∀ a b c : Nat, IsABCTriple a b c →
      (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal ≤
        (1 + ε) * arithmeticWeight (abcRationalPoint a c) +
          (s1902LogVolume T (s1902Hull T)).toReal + D

/-- **Conditional ABC from the triple-dependent paper comparison region.** -/
theorem abc_of_tripleComparison
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) : ABCConjecture :=
  abcConjecture_iff_abcArithmeticWeightHeightBound.mpr
    (heightWeightBound_of_normalizedVolumeComparison
      (P := IsABCTriple)
      (height := fun a b c => Height.logHeight₁ (abcRationalPoint a c))
      (weight := fun a b c => arithmeticWeight (abcRationalPoint a c))
      (volume := fun _ _ a b c =>
        (s1902LogVolume T (paperComparisonRegion T point a b c)).toReal)
      (thetaBound := (s1902LogVolume T (s1902Hull T)).toReal)
      (hweight_nonneg := fun a b c _ => arithmeticWeight_nonneg _)
      (hcomparison := fun δ hδ =>
        ⟨fun a b c habc => C.height_le_regionVolume δ hδ a b c habc,
         by
           obtain ⟨D, hD⟩ := C.regionVolume_le_weight δ hδ
           exact ⟨D, fun a b c habc => hD a b c habc⟩⟩))

end LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

end
/-! ### Axiom gate (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.abc_of_tripleComparison