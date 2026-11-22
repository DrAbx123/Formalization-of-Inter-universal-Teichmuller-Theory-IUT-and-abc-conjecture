import tmp.sheaf.xif.PaperSignedHull

noncomputable section

namespace LeanFormal.IUT.OrigXiFProbeHullAdapted

open LeanFormal.IUT
open scoped ENNReal

/-- A synthetic paper signed hull with a prescribed nonnegative procession
average.  This is a consistency/model object for the scalar audit only; it is
not a paper hull and is not used as a paper object. -/
def testHull (v : Real) (hv : 0 <= v) : PaperSignedHull Real PUnit where
  ambient :=
    { imageSet := {0}
      hull := {0}
      imageSet_subset_hull := by intro x hx; exact hx
      logVolume := fun S => if S.Nonempty then ENNReal.ofReal v else 0
      logVolume_mono := by
        intro S T hST
        by_cases hS : S.Nonempty
        . have hT : T.Nonempty := by
            rcases hS with ⟨x, hx⟩
            exact ⟨x, hST hx⟩
          simp [hS, hT]
        . simp [hS]
      unitRegion := {0}
      scaleShift := fun x => x
      hull_subset_scaleShift := by
        intro x hx
        exact ⟨x, hx, rfl⟩
      unitRegion_logVolume_lt_top := by
        have h : ({0} : Set Real).Nonempty := ⟨0, rfl⟩
        change (if ({0} : Set Real).Nonempty then ENNReal.ofReal v else 0) < ⊤
        rw [if_pos h]
        exact ENNReal.ofReal_lt_top
      scaleShift_unitRegion_logVolume_le := by simp }
  procession :=
    { value := fun _ => v
      weight := fun _ => 1
      weightTotal := 1
      weightTotal_pos := by norm_num
      weightTotal_eq_sum := by simp }
  hull :=
    { volume := fun _ => v
      hullVolume := v
      contains := fun _ => le_rfl }
  weighted_matches_hull := fun _ => rfl
  weights_nonnegative := fun _ => by norm_num
  average_nonneg := hv
  hull_logVolume_eq_average := by
    have h : ({0} : Set Real).Nonempty := ⟨0, rfl⟩
    simp [h, WeightedValues.average]

theorem testHull_signed (v : Real) (hv : 0 <= v) :
    (testHull v hv).signedHullLogVolume = -v := by
  have h : ({0} : Set Real).Nonempty := ⟨0, rfl⟩
  simp [PaperSignedHull.signedHullLogVolume, testHull, h, ENNReal.toReal_ofReal hv]

end LeanFormal.IUT.OrigXiFProbeHullAdapted
