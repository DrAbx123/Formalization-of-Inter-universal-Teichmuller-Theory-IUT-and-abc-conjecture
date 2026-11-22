import tmp.sheaf.xif.paper.S1225SourceChoiceCoreActual

/-! # S1282: an actual source level on `Choice = I.family.index`

The S1225 source-choice data gives `Choice := I.family.index` together with
`index_equiv : index ≃ ℤ × ℤ` and the actual shifts
`sourceInd1/2/3`.  S1231 built a `Core` with `level := fun _ => 0`; this
file constructs a *genuine* (nonconstant, unbounded) level from the actual
source data and determines exactly what it can and cannot satisfy.

## What is constructed

`sourceLevel i := (I.index_equiv i).1.toNat` is the actual first lattice
coordinate, truncated at zero.  It is not an artificial constant:

* `sourceLevel_unbounded`: every `N` is attained;
* `sourceLevel_stageSource`: on the actual F-stage procession
  (`I.fStageCapsule n`, whose `k`-th theater is `I.indexOf k n`) the level
  of the `k`-th theater is exactly `k`;
* `sourceLevel_ind3_le`: the actual `ind3 = translate (n,0)` is monotone
  for this level, i.e. the `Core.ind3_level` direction holds;
* `sourceLevel_ind3_eq_add_of_nonneg`: on the nonnegative part it is exactly
  `level c + n`.

## What is impossible

* `no_additive_sourceLevel`: no total level satisfies
  `level (ind3 n c) = level c + n` for the actual `ind3`, hence the
  `Carrier.ind3_level_eq` form cannot be met on
  `Choice = I.family.index`;
* `level_constant_of_core_level_laws`: any level invariant under the actual
  `ind1` and `ind2` is constant.  Since `sourceLevel` is not
  `ind1`-invariant, it cannot be inserted into the actual S1231 Core: the
  Core level laws force the zero level.  Changing `level` alone cannot repair
  this; `ind1`/`ind2` (or `Choice`) must change.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1282SourceLevelActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1225SourceChoiceCoreActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. The actual level -/

/-- The lattice coordinate underlying the level. -/
def levelCoord (i : I.family.index) : Int := (I.index_equiv i).1

/-- Actual source level: the nonnegative part of the first lattice coordinate.
Built from `I.index_equiv`; it is unbounded, hence not a constant replacement. -/
def sourceLevel (i : I.family.index) : Nat := (levelCoord I i).toNat

@[simp] theorem levelCoord_indexOf (a m : Int) :
    levelCoord I (I.indexOf a m) = a := by
  unfold levelCoord
  rw [I.indexOf_apply]

@[simp] theorem sourceLevel_indexOf (a m : Int) :
    sourceLevel I (I.indexOf a m) = a.toNat := by
  unfold sourceLevel
  rw [levelCoord_indexOf]

/-! ## 2. The actual `ind3` direction -/

theorem sourceInd3_eq_translate (n : Nat) (c : I.family.index) :
    sourceInd3 I n c = I.translate (n : Int) 0 c := rfl

theorem sourceInd3_indexOf (n : Nat) (a m : Int) :
    sourceInd3 I n (I.indexOf a m) = I.indexOf (a + (n : Int)) m := by
  rw [sourceInd3_eq_translate, I.translate_theater]
  simp

/-- Monotonicity in the actual `ind3` direction (the `Core.ind3_level` law). -/
theorem sourceLevel_ind3_le (n : Nat) (c : I.family.index) :
    sourceLevel I c ≤ sourceLevel I (sourceInd3 I n c) := by
  unfold sourceLevel levelCoord
  rw [sourceInd3_eq_translate, I.translate_index]
  simp only [translateIndex]
  exact Int.toNat_le_toNat (by omega)

/-- On the nonnegative part the shift is exactly `n`. -/
theorem sourceLevel_ind3_eq_add_of_nonneg (n : Nat) (c : I.family.index)
    (hc : 0 ≤ levelCoord I c) :
    sourceLevel I (sourceInd3 I n c) = sourceLevel I c + n := by
  unfold sourceLevel levelCoord at *
  rw [sourceInd3_eq_translate, I.translate_index]
  simp only [translateIndex]
  rw [Int.toNat_add hc (by omega), Int.toNat_natCast]

/-! ## 3. Non-degeneracy: not a constant level -/

theorem sourceLevel_unbounded (N : Nat) : ∃ c, sourceLevel I c = N :=
  ⟨I.indexOf (N : Int) 0, by simp⟩

theorem sourceLevel_not_constant :
    sourceLevel I (I.indexOf 2 0) ≠ sourceLevel I (I.indexOf 0 0) := by
  simp

/-- The two-point witness that the level is genuinely nonconstant. -/
theorem sourceLevel_two_ne_zero :
    sourceLevel I (I.indexOf 2 0) = 2 ∧ sourceLevel I (I.indexOf 0 0) = 0 := by
  simp

/-! ## 4. The exact obstruction to the equality form -/

/-- No total level on `I.family.index` shifts by exactly `n` under the
actual `ind3`.  Iterating from a negative first coordinate forces
`level (indexOf 0 0) ≥ m` for every `m`. -/
theorem no_additive_sourceLevel :
    ¬ ∃ level : I.family.index → Nat,
        ∀ (n : Nat) (c : I.family.index),
          level (sourceInd3 I n c) = level c + n := by
  rintro ⟨level, h⟩
  have key : ∀ m : Nat, m ≤ level (I.indexOf 0 0) := by
    intro m
    have hm := h m (I.indexOf (-(m : Int)) 0)
    rw [sourceInd3_indexOf] at hm
    have h0 : (-(m : Int) + (m : Int)) = 0 := by ring
    rw [h0] at hm
    omega
  have := key (level (I.indexOf 0 0) + 1)
  omega

/-! ## 5. Relation to the actual F-stage procession -/

/-- On the actual F-stage, the `k`-th theater has level `k`. -/
theorem sourceLevel_stageSource (n : Nat) (k : Fin (n + 1)) :
    sourceLevel I ((I.fStageCapsule n).source k) = k.1 := by
  rw [fStageCapsule_source]
  unfold stageSource sourceLevel levelCoord
  rw [I.indexOf_apply]
  simp

/-- Every level value is realized by a theater of the actual procession. -/
theorem sourceLevel_attained_in_stage (N : Nat) :
    ∃ (n : Nat) (k : Fin (n + 1)),
      sourceLevel I ((I.fStageCapsule n).source k) = N :=
  ⟨N, ⟨N, Nat.lt_succ_self N⟩, by rw [sourceLevel_stageSource]⟩

/-- Consequence for any procession stage: its theaters have level at most the
stage number. -/
theorem sourceLevel_le_of_stage (n : Nat) (k : Fin (n + 1)) :
    sourceLevel I ((I.fStageCapsule n).source k) ≤ n := by
  rw [sourceLevel_stageSource]
  omega

/-- The canonical H2F procession's stages are exactly the F-stage capsules, so
the same bound holds for `H2FProcession.canonical`. -/
theorem sourceLevel_le_of_canonical_stage (n : Nat) (k : Fin (n + 1)) :
    sourceLevel I (((H2FProcession.canonical (I := I)).stage n).source k) ≤ n := by
  rw [H2FProcession.canonical_stage]
  exact sourceLevel_le_of_stage I n k

/-- The procession does not cover the whole index lattice: `indexOf 0 (-1)`
occurs in no stage, so the level cannot be read off from stage membership
alone. -/
theorem not_every_index_in_a_stage :
    ¬ ∃ (n : Nat) (k : Fin (n + 1)),
        (I.fStageCapsule n).source k = I.indexOf 0 (-1) := by
  rintro ⟨n, k, hk⟩
  have h := congrArg (fun i => (I.index_equiv i).2) hk
  rw [fStageCapsule_source] at h
  unfold stageSource at h
  rw [I.indexOf_apply, I.indexOf_apply] at h
  simp at h

/-! ## 6. The Core level laws force the zero level -/

theorem sourceInd1_neg_one_indexOf (a m : Int) :
    sourceInd1 I (-1) (I.indexOf a m) = I.indexOf (a + 1) m := by
  simp [sourceInd1, horizontalPerm, I.horizontal_shift_theater]

theorem sourceInd1_one_indexOf (a m : Int) :
    sourceInd1 I 1 (I.indexOf a m) = I.indexOf (a - 1) m := by
  simp [sourceInd1, horizontalPerm, I.horizontal_shift_inverse_theater]

theorem sourceInd2_neg_one_indexOf (n m : Int) :
    sourceInd2 I (-1) (I.indexOf n m) = I.indexOf n (m + 1) := by
  simp [sourceInd2, verticalPerm, I.vertical_shift_theater]

theorem sourceInd2_one_indexOf (n m : Int) :
    sourceInd2 I 1 (I.indexOf n m) = I.indexOf n (m - 1) := by
  simp [sourceInd2, verticalPerm, I.vertical_shift_inverse_theater]

theorem level_horizontal_const (level : I.family.index → Nat)
    (h1 : ∀ (g : Int) (c : I.family.index),
      level (sourceInd1 I g c) = level c)
    (m : Int) : ∀ a : Int, level (I.indexOf a m) = level (I.indexOf 0 m) := by
  intro a
  refine Int.induction_on a ?zero ?succ ?pred
  · rfl
  · intro i ih
    calc level (I.indexOf ((i : Int) + 1) m)
        = level (sourceInd1 I (-1) (I.indexOf (i : Int) m)) := by
          rw [sourceInd1_neg_one_indexOf]
      _ = level (I.indexOf (i : Int) m) := h1 (-1) _
      _ = level (I.indexOf 0 m) := ih
  · intro i ih
    calc level (I.indexOf (-(i : Int) - 1) m)
        = level (sourceInd1 I 1 (I.indexOf (-(i : Int)) m)) := by
          rw [sourceInd1_one_indexOf]
      _ = level (I.indexOf (-(i : Int)) m) := h1 1 _
      _ = level (I.indexOf 0 m) := ih

theorem level_vertical_const (level : I.family.index → Nat)
    (h2 : ∀ (g : Int) (c : I.family.index),
      level (sourceInd2 I g c) = level c)
    (n : Int) : ∀ m : Int, level (I.indexOf n m) = level (I.indexOf n 0) := by
  intro m
  refine Int.induction_on m ?zero ?succ ?pred
  · rfl
  · intro i ih
    calc level (I.indexOf n ((i : Int) + 1))
        = level (sourceInd2 I (-1) (I.indexOf n (i : Int))) := by
          rw [sourceInd2_neg_one_indexOf]
      _ = level (I.indexOf n (i : Int)) := h2 (-1) _
      _ = level (I.indexOf n 0) := ih
  · intro i ih
    calc level (I.indexOf n (-(i : Int) - 1))
        = level (sourceInd2 I 1 (I.indexOf n (-(i : Int)))) := by
          rw [sourceInd2_one_indexOf]
      _ = level (I.indexOf n (-(i : Int))) := h2 1 _
      _ = level (I.indexOf n 0) := ih

/-- Any level invariant under the actual `ind1` and `ind2` is constant. -/
theorem level_constant_of_core_level_laws (level : I.family.index → Nat)
    (h1 : ∀ (g : Int) (c : I.family.index),
      level (sourceInd1 I g c) = level c)
    (h2 : ∀ (g : Int) (c : I.family.index),
      level (sourceInd2 I g c) = level c) :
    ∀ c : I.family.index, level c = level (I.indexOf 0 0) := by
  intro c
  have hc : I.indexOf (I.index_equiv c).1 (I.index_equiv c).2 = c := by
    apply I.index_equiv.injective
    rw [I.indexOf_apply]
  calc level c
      = level (I.indexOf (I.index_equiv c).1 (I.index_equiv c).2) := by rw [hc]
    _ = level (I.indexOf 0 (I.index_equiv c).2) :=
        level_horizontal_const I level h1 (I.index_equiv c).2
          (I.index_equiv c).1
    _ = level (I.indexOf 0 0) :=
        level_vertical_const I level h2 0 (I.index_equiv c).2

/-- The constructed level violates the `Core.ind1_level` law, so it cannot be
inserted into the actual S1231 Core (whose `ind1` is the same horizontal
shift). -/
theorem sourceLevel_not_ind1_invariant :
    ¬ ∀ (g : Int) (c : I.family.index),
        sourceLevel I (sourceInd1 I g c) = sourceLevel I c := by
  intro h
  have hc := h (-1) (I.indexOf 1 0)
  rw [sourceInd1_neg_one_indexOf] at hc
  simp at hc

/-- The constructed level does satisfy the `Core.ind3_level` direction; it
fails only the `ind1`/`ind3` coherence, which is the exact obstruction. -/
theorem sourceLevel_ind3_direction :
    (∀ (n : Nat) (c : I.family.index),
      sourceLevel I c ≤ sourceLevel I (sourceInd3 I n c)) ∧
    (∃ c, sourceLevel I c ≠ sourceLevel I (I.indexOf 0 0)) :=
  ⟨sourceLevel_ind3_le I, ⟨I.indexOf 2 0, by simp⟩⟩

end LeanFormal.IUT.XiFPaper.S1282SourceLevelActual

end