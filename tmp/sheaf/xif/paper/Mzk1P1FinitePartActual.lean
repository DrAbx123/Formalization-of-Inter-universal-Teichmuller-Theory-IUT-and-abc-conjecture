import tmp.sheaf.xif.paper.Mzk1StepProviderPrimeActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1FinitePartActual — finite part of a P1(Qbar) point set (real)

Real Lean (no sorry/axiom): the finite part of a finite P1(Qbar) set together with its
membership characterisation and image identity.  This is the bookkeeping needed for the f4b
transfer from the PROVED finite strict-count lemma numMax_stepSet_lt to the P1 measure.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual

local instance instDecEqQbar : DecidableEq Qbar := Classical.decEq Qbar
local instance instDecEqP1 : DecidableEq (P1Point Qbar) := Classical.decEq (P1Point Qbar)

universe u

/-- Finite part of a finite P1(Qbar) set: the finite points, as elements of Qbar. -/
noncomputable def finitePart (S : Finset (P1Point Qbar)) : Finset Qbar :=
  (S.erase P1Point.infty).attach.image (fun p =>
    Classical.choose (Option.ne_none_iff_exists'.mp (Finset.mem_erase.mp p.2).1))

/-- Membership characterisation: x is in the finite part iff the finite point is in S. -/
theorem mem_finitePart_iff {S : Finset (P1Point Qbar)} {x : Qbar} :
    x ∈ finitePart S ↔ P1Point.ofFinite x ∈ S := by
  constructor
  · intro hx
    obtain ⟨p, _hp, hpx⟩ := Finset.mem_image.mp hx
    have hspec := Classical.choose_spec (Option.ne_none_iff_exists'.mp (Finset.mem_erase.mp p.2).1)
    have hval : p.1 = P1Point.ofFinite x := by
      rw [hspec, hpx]
      rfl
    have hmem : p.1 ∈ S := (Finset.mem_erase.mp p.2).2
    rwa [hval] at hmem
  · intro hx
    let p : {q // q ∈ S.erase P1Point.infty} :=
      ⟨P1Point.ofFinite x, Finset.mem_erase.mpr ⟨P1Point.ofFinite_ne_infty x, hx⟩⟩
    refine Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, ?_⟩
    show Classical.choose (Option.ne_none_iff_exists'.mp (Finset.mem_erase.mp p.2).1) = x
    have hspec := Classical.choose_spec (Option.ne_none_iff_exists'.mp (Finset.mem_erase.mp p.2).1)
    exact (Option.some.inj hspec).symm

/-- The finite part reconstructs exactly the finite points of S. -/
theorem finitePart_image (S : Finset (P1Point Qbar)) :
    (finitePart S).image (fun x => P1Point.ofFinite x) = S.erase P1Point.infty := by
  ext q
  constructor
  · intro hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_erase.mpr ⟨P1Point.ofFinite_ne_infty x, mem_finitePart_iff.mp hx⟩
  · intro hq
    have hq' : q ≠ P1Point.infty := (Finset.mem_erase.mp hq).1
    obtain ⟨x, hx⟩ : ∃ x, q = P1Point.ofFinite x := by
      cases q with
      | none => exact absurd rfl hq'
      | some x => exact ⟨x, rfl⟩
    exact Finset.mem_image.mpr ⟨x, mem_finitePart_iff.mpr (hx ▸ (Finset.mem_erase.mp hq).2), hx.symm⟩

#check finitePart
#check mem_finitePart_iff
#check finitePart_image

end LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartActual
end
