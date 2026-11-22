import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Mzk1Stage4PaperComparisonRegionScalingDesignActual (stage4 lane; design, supplemental)

A622 module (stage4 supplementary design; the canonical file
Mzk1PaperComparisonRegionScalingActual is MAINLINE-exclusive and is NOT written here):
generic interface for the paper comparison region with TRIPLE-DEPENDENT scaling,
region a b c := tripleScale a b c '' (unitRegion ∪ {pt a b c}), plus a concrete real
model whose regions are monotone in the triple.  No new mathematics.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperComparisonRegionScalingDesignActual

universe u

/-- The paper comparison region with triple-dependent scaling. -/
structure PaperComparisonRegionScaling (X : Type u) where
  /-- triple-dependent scaling map. -/
  scale : Nat → Nat → Nat → X → X
  /-- the unit region (log-shell). -/
  unitRegion : Set X
  /-- the point datum of a triple. -/
  pt : Nat → Nat → Nat → X

/-- The comparison region of a triple: scale a b c applied to unit ∪ {pt a b c}. -/
def region {X : Type u} (S : PaperComparisonRegionScaling X)
    (a b c : Nat) : Set X :=
  S.scale a b c '' (S.unitRegion ∪ {S.pt a b c})

/-- The real model's unit region [0,1]. -/
def realUnit : Set Real := Set.Icc 0 1

/-- The real model's triple scale: multiplication by a+b+c+1. -/
def realScale (a b c : Nat) (x : Real) : Real := x * (((a + b + c : Nat) : Real) + 1)

/-- The real model's point datum: the point 1. -/
def realPt (_a _b _c : Nat) : Real := 1

/-- The real model of the paper comparison region scaling. -/
noncomputable def realScaling : PaperComparisonRegionScaling Real where
  scale := realScale
  unitRegion := realUnit
  pt := realPt

/-- The model scale is monotone in the triple sum. -/
theorem realScale_mono_sum {n n' : Real} (hn : n ≤ n') {x : Real} (hx0 : 0 ≤ x) :
    x * (n + 1) ≤ x * (n' + 1) :=
  mul_le_mul_of_nonneg_left (by linarith) hx0

/-- The model comparison regions are monotone in the triple. -/
theorem realScaling_region_mono {a b c a' b' c' : Nat}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    region realScaling a b c ⊆ region realScaling a' b' c' := by
  have hnat : a + b + c ≤ a' + b' + c' := by omega
  have hsum : ((a + b + c : Nat) : Real) ≤ ((a' + b' + c' : Nat) : Real) := by
    exact_mod_cast hnat
  rintro y ⟨x, hx, rfl⟩
  simp only [realScaling, realPt] at hx ⊢
  have hx0 : 0 ≤ x := by
    rcases hx with h | h
    · exact h.1
    · rw [Set.mem_singleton_iff] at h
      subst h
      norm_num
  have hx1 : x ≤ 1 := by
    rcases hx with h | h
    · exact h.2
    · rw [Set.mem_singleton_iff] at h
      subst h
      norm_num
  have hNpos : (0 : Real) < ((a' + b' + c' : Nat) : Real) + 1 := by positivity
  refine ⟨x * (((a + b + c : Nat) : Real) + 1) / (((a' + b' + c' : Nat) : Real) + 1), ?_, ?_⟩
  · left
    constructor
    · positivity
    · rw [div_le_one hNpos]
      nlinarith
  · show (x * (((a + b + c : Nat) : Real) + 1) / (((a' + b' + c' : Nat) : Real) + 1)) *
        (((a' + b' + c' : Nat) : Real) + 1) =
      x * (((a + b + c : Nat) : Real) + 1)
    field_simp
#check PaperComparisonRegionScaling
#check region
#check realScaling
#check realScaling_region_mono
#check realScale_mono_sum

end LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperComparisonRegionScalingDesignActual
end
