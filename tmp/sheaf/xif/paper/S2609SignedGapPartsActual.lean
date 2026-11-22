import tmp.sheaf.xif.paper.S2605SignedSourceVolumeActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierHaarData

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2605SignedSourceVolumeActual
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2609SignedGapPartsActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem sourceSetVolumeSigned_union_le (v : V)
    (S T : Set (I.ThetaPilotPoint v)) :
    sourceSetVolumeSigned I v (S ∪ T) <=
      sourceSetVolumeSigned I v S + sourceSetVolumeSigned I v T := by
  unfold sourceSetVolumeSigned
  refine iSup_le_iff.mpr ?_
  intro x
  refine iSup_le_iff.mpr ?_
  intro hx
  rw [Set.mem_union] at hx
  rcases hx with hxS | hxT
  · exact le_trans (le_iSup_of_le x (le_iSup_of_le (f := fun _ : x ∈ S => sourcePointVolumeSigned I v x) hxS le_rfl)) (le_add_right le_rfl)
  · exact le_trans (le_iSup_of_le x (le_iSup_of_le (f := fun _ : x ∈ T => sourcePointVolumeSigned I v x) hxT le_rfl)) (le_add_left le_rfl)

theorem S2609_signed_hsplit (v : V)
    (W : IQHullLogVolumeInterface (I.ThetaPilotPoint v))
    (p : Nat -> Nat -> Nat -> I.ThetaPilotPoint v)
    (a b c : Nat) :
    sourceSetVolumeSigned I v (normalizedComparisonRegion W p a b c) <=
      sourceSetVolumeSigned I v (W.scaleShift '' W.unitRegion) +
        sourceSetVolumeSigned I v {W.scaleShift (p a b c)} := by
  rw [cor312Gap2_normalizedComparisonRegion_eq_scaleShift_union]
  exact sourceSetVolumeSigned_union_le I v _ _

theorem S2609_signed_hptfin (v : V) (x : I.ThetaPilotPoint v) :
    sourceSetVolumeSigned I v {x} < ⊤ := by
  have hEq : sourceSetVolumeSigned I v {x} = sourcePointVolumeSigned I v x := by
    apply le_antisymm
    · unfold sourceSetVolumeSigned
      refine iSup_le_iff.mpr ?_
      intro y
      refine iSup_le_iff.mpr ?_
      intro hy
      have hyx : y = x := Set.mem_singleton_iff.mp hy
      rw [hyx]
    · unfold sourceSetVolumeSigned
      exact le_iSup_of_le x (le_iSup_of_le (f := fun _ : x ∈ {x} => sourcePointVolumeSigned I v x) (by simp) le_rfl)
  rw [hEq]
  exact ENNReal.ofReal_lt_top

#check sourceSetVolumeSigned_union_le
#check S2609_signed_hsplit
#check S2609_signed_hptfin
#print axioms S2609_signed_hsplit

end LeanFormal.IUT.XiFPaper.S2609SignedGapPartsActual
end