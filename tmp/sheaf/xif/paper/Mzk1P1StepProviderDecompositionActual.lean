import tmp.sheaf.xif.paper.Mzk1P1FinitePartActual
import tmp.sheaf.xif.paper.Mzk1F0StepGeometryActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1StepProviderDecompositionActual — P1 step target vs finite step target (real)

Real Lean (no sorry/axiom): the P1 step target stepSetP1 S alpha0 decomposes as the finite
step target of the finite part, mapped by ofFinite, together with the point at infinity when
it lies in S.  This discharges the set-decomposition hypothesis of the f4b transfer.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderDecompositionActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1StepProviderPrimeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartActual
open LeanFormal.IUT.XiFPaper.Mzk1F0StepGeometryActual
open Polynomial

attribute [local instance] Classical.decEq

universe u

theorem stepSetP1_eq_finite (S : Finset (P1Point Qbar)) (alpha0 : Qbar) :
    stepSetP1 S alpha0 =
      (stepSet (finitePart S) alpha0).image (fun x => P1Point.ofFinite x) ∪
        (if P1Point.infty ∈ S then {P1Point.infty} else ∅) := by
  ext q
  constructor
  · intro hq
    unfold stepSetP1 at hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
      subst hpq
      rcases Finset.mem_union.mp hp with hpS | hpC
      · by_cases hpi : p = P1Point.infty
        · subst hpi
          rw [f0Map_infty, Finset.mem_union, if_pos hpS]
          exact Or.inr (Finset.mem_singleton_self _)
        · obtain ⟨x, rfl⟩ : ∃ x : Qbar, p = P1Point.ofFinite x := by
            cases p with
            | none => exact absurd rfl hpi
            | some x => exact ⟨x, rfl⟩
          rw [f0Map_finite]
          apply Finset.mem_union_left
          apply Finset.mem_image.mpr
          refine ⟨aeval x (minpoly ℚ alpha0), ?_, rfl⟩
          unfold stepSet
          apply Finset.mem_union_left
          apply Finset.mem_image.mpr
          exact ⟨x, Finset.mem_union_left _ (mem_finitePart_iff.mpr hpS), rfl⟩
      · obtain ⟨x, hxconj, hpx⟩ := Finset.mem_image.mp hpC
        subst hpx
        rw [f0Map_finite]
        apply Finset.mem_union_left
        apply Finset.mem_image.mpr
        refine ⟨aeval x (minpoly ℚ alpha0), ?_, rfl⟩
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨x, Finset.mem_union_right _ hxconj, rfl⟩)
    · obtain ⟨xi, hxi, hq⟩ := Finset.mem_image.mp hq
      subst hq
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨aeval xi (minpoly ℚ alpha0), ?_, rfl⟩
      unfold stepSet
      exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨xi, hxi, rfl⟩)
  · intro hq
    rw [Finset.mem_union] at hq
    rcases hq with hq | hq
    · obtain ⟨y, hy, hqy⟩ := Finset.mem_image.mp hq
      subst hqy
      unfold stepSet at hy
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨x, hx, hyx⟩ := Finset.mem_image.mp hy
        subst hyx
        rcases Finset.mem_union.mp hx with hxF | hxC
        · unfold stepSetP1
          apply Finset.mem_union_left
          exact Finset.mem_image.mpr
            ⟨P1Point.ofFinite x, Finset.mem_union_left _ (mem_finitePart_iff.mp hxF), f0Map_finite _ _⟩
        · unfold stepSetP1
          apply Finset.mem_union_left
          exact Finset.mem_image.mpr
            ⟨P1Point.ofFinite x, Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨x, hxC, rfl⟩), f0Map_finite _ _⟩
      · obtain ⟨xi, hxi, hyx⟩ := Finset.mem_image.mp hy
        subst hyx
        unfold stepSetP1
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨xi, hxi, rfl⟩
    · have hinf : P1Point.infty ∈ S := by
        by_contra h
        rw [if_neg h] at hq
        exact absurd hq (by simp)
      rw [if_pos hinf] at hq
      rw [Finset.mem_singleton] at hq
      subst hq
      unfold stepSetP1
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr
        ⟨P1Point.infty, Finset.mem_union_left _ hinf, f0Map_infty alpha0⟩

#check stepSetP1_eq_finite

end LeanFormal.IUT.XiFPaper.Mzk1P1StepProviderDecompositionActual
end
