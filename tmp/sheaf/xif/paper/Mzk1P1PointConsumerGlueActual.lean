import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1PointConsumerGlueActual — consumer lemmas for P1(Qbar) finite points

Small glue module (no new mathematics): injectivity/characterisation lemmas for the
finite-point embedding `P1Point.ofFinite`, derived from the proved
`P1Point.ofFinite_ne_infty` / `P1Point.eq_infty_or_finite`.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P1PointConsumerGlueActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

universe u

variable {K : Type u} [Field K]

/-- The finite embedding is injective. -/
theorem ofFinite_injective : Function.Injective (P1Point.ofFinite : K → P1Point K) := by
  intro a b h
  injection h

/-- A point is finite iff it is not the point at infinity. -/
theorem ne_infty_iff_exists_ofFinite (p : P1Point K) :
    p ≠ P1Point.infty ↔ ∃ x : K, p = P1Point.ofFinite x := by
  constructor
  · intro hp
    rcases P1Point.eq_infty_or_finite p with h | ⟨x, hx⟩
    · exact absurd h hp
    · exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    exact P1Point.ofFinite_ne_infty x

/-- The finite points have no point at infinity in their image. -/
theorem infty_not_mem_image (S : Finset K) :
    P1Point.infty ∉ S.image (fun x => P1Point.ofFinite x) := by
  intro h
  obtain ⟨x, _hx, hx⟩ := Finset.mem_image.mp h
  exact P1Point.ofFinite_ne_infty x hx.symm

/-- Erasing infinity from an image of finite points is a no-op. -/
theorem erase_infty_image (S : Finset K) :
    (S.image (fun x => P1Point.ofFinite x)).erase P1Point.infty =
      S.image (fun x => P1Point.ofFinite x) :=
  Finset.erase_eq_of_not_mem (infty_not_mem_image S)

/-- The image of a finite set of finite points has the same cardinality. -/
theorem card_image_ofFinite (S : Finset K) :
    (S.image (fun x => P1Point.ofFinite x)).card = S.card :=
  Finset.card_image_of_injective S ofFinite_injective

#check ofFinite_injective
#check ne_infty_iff_exists_ofFinite
#check erase_infty_image
#check card_image_ofFinite

end LeanFormal.IUT.XiFPaper.Mzk1P1PointConsumerGlueActual
end
