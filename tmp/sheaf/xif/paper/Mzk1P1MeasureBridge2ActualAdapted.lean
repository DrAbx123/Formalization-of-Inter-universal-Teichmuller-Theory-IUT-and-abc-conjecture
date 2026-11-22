import tmp.sheaf.xif.paper.Mzk1P1MeasureBridgeActualAdapted

/-! # Mzk1P1MeasureBridge2ActualAdapted — numMax P1 bridge for the f0 step (real lemma)

Real Lean (no sorry/axiom): for finite S with maxDeg S >= 2, adding infinity to the finite
image does not change the P1 maximal count, because infinity has degree 1 and is not
maximal.  This is the second concrete ingredient of the P1 measure transfer.  Registry 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge2ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridgeActualAdapted

attribute [local instance] Classical.decEq

universe u

/-- For finite S with maxDeg S >= 2, the P1 maximal count of the finite image equals the
finite numMax, and adding infinity does not change it. -/
theorem numMaxP_insert_infty_image (S : Finset Qbar) (h2 : 2 <= maxDeg S) :
    numMaxP (insert P1Point.infty (S.image (fun z => P1Point.ofFinite z))) = numMax S := by
  have hmax : max 1 (maxDeg S) = maxDeg S := by omega
  have hnot : P1Point.infty ∉ S.image (fun z => P1Point.ofFinite z) := by
    intro hmem
    obtain ⟨z, _hz, hz⟩ := Finset.mem_image.mp hmem
    exact absurd hz (by simp [P1Point.infty, P1Point.ofFinite])
  unfold numMaxP numMax
  rw [maxDegP_insert_infty_image, hmax]
  have hinf : degP P1Point.infty ≠ maxDeg S := by
    have h1 : degP P1Point.infty = 1 := rfl
    omega
  have hfilter : (insert P1Point.infty (S.image (fun z => P1Point.ofFinite z))).filter
      (fun p => degP p = maxDeg S) =
      (S.filter (fun z => degQ z = maxDeg S)).image (fun z => P1Point.ofFinite z) := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter, Finset.mem_insert] at hp
      rcases hp with ⟨hpin | hpim, hpdeg⟩
      · rw [hpin] at hpdeg
        exact absurd hpdeg hinf
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hpim
        exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hz, hpdeg⟩, rfl⟩
    · intro hp
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
      rw [Finset.mem_filter] at hz
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z, hz.1, rfl⟩), hz.2⟩
  rw [hfilter, Finset.card_image_of_injective _ (fun x y h => Option.some.inj h)]

/-- Row record. -/
def p1MeasureBridge2Rows : List (String × String) :=
  [ ("numMaxP_insert_infty_image", "PROVED (new)") ]

theorem p1MeasureBridge2Rows_length : p1MeasureBridge2Rows.length = 1 := rfl

#check numMaxP_insert_infty_image

end LeanFormal.IUT.XiFPaper.Mzk1P1MeasureBridge2ActualAdapted
end
