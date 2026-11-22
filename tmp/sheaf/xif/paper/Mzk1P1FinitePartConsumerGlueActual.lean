import tmp.sheaf.xif.paper.Mzk1P1FinitePartActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1FinitePartConsumerGlueActual — consumer lemmas for the finite part

Small glue module (no new mathematics): monotonicity, infinity-erasure invariance and
image-subset facts derived from `mem_finitePart_iff` / `finitePart_image`.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartConsumerGlueActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartActual

local instance instDecEqQbar : DecidableEq Qbar := Classical.decEq Qbar
local instance instDecEqP1 : DecidableEq (P1Point Qbar) := Classical.decEq (P1Point Qbar)

universe u

/-- Monotonicity of the finite part. -/
theorem finitePart_mono {S T : Finset (P1Point Qbar)} (h : S ⊆ T) :
    finitePart S ⊆ finitePart T := by
  intro x hx
  exact mem_finitePart_iff.mpr (h (mem_finitePart_iff.mp hx))

/-- Erasing the point at infinity does not change the finite part. -/
theorem finitePart_erase_infty (S : Finset (P1Point Qbar)) :
    finitePart (S.erase P1Point.infty) = finitePart S := by
  ext x
  rw [mem_finitePart_iff, mem_finitePart_iff, Finset.mem_erase]
  constructor
  · exact fun h => h.2
  · intro hx
    exact ⟨P1Point.ofFinite_ne_infty x, hx⟩

/-- The image of the finite part under the finite embedding lies in the original set. -/
theorem image_finitePart_subset (S : Finset (P1Point Qbar)) :
    (finitePart S).image (fun x => P1Point.ofFinite x) ⊆ S := by
  rw [finitePart_image]
  exact Finset.erase_subset _ _

/-- Nonempty finite part iff the set contains some finite point. -/
theorem finitePart_nonempty_iff (S : Finset (P1Point Qbar)) :
    (finitePart S).Nonempty ↔ ∃ q ∈ S, q ≠ P1Point.infty := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨P1Point.ofFinite x, mem_finitePart_iff.mp hx, P1Point.ofFinite_ne_infty x⟩
  · rintro ⟨q, hq, hqinf⟩
    obtain ⟨x, rfl⟩ : ∃ x, q = P1Point.ofFinite x := by
      cases q with
      | none => exact absurd rfl hqinf
      | some x => exact ⟨x, rfl⟩
    exact ⟨x, mem_finitePart_iff.mpr hq⟩

#check finitePart_mono
#check finitePart_erase_infty
#check image_finitePart_subset
#check finitePart_nonempty_iff

end LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartConsumerGlueActual
end
