import tmp.sheaf.xif.paper.Mzk1P1FinitePartActual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # Mzk1P1FinitePartMeasureActual — P1 measure vs finite part (real)

Real Lean (no sorry/axiom): for a finite P1(Qbar) set with maxDegP >= 2 the infinity point
(degree 1) never attains the maximal degree, so the P1 measure coincides with the finite-part
measure: maxDegP S = maxDeg (finitePart S) and numMaxP S = numMax (finitePart S).
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartMeasureActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartActual

universe u

/-- With maxDegP S >= 2, the P1 maximal degree is the finite-part maximal degree. -/
theorem maxDegP_eq_maxDeg_finitePart (S : Finset (P1Point Qbar)) (h2 : 2 <= maxDegP S) :
    maxDegP S = maxDeg (finitePart S) := by
  classical
  have hne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with rfl | h
    · simp [maxDegP] at h2
    · exact h
  obtain ⟨p, hpS, hpdeg⟩ := Finset.exists_mem_eq_sup (s := S) hne (f := degP)
  have hpmax : degP p = maxDegP S := hpdeg.symm
  have hle1 : maxDegP S <= maxDeg (finitePart S) := by
    rw [← hpmax]
    cases p with
    | none =>
        exfalso
        rw [← hpmax] at h2
        rw [show degP (none : P1Point Qbar) = 1 from rfl] at h2
        omega
    | some x =>
        change degQ x <= maxDeg (finitePart S)
        unfold maxDeg
        exact Finset.le_sup (f := degQ) (mem_finitePart_iff.mpr hpS)
  have hle2 : maxDeg (finitePart S) <= maxDegP S := by
    change (finitePart S).sup degQ <= S.sup degP
    apply Finset.sup_le
    intro y hy
    have hyS : P1Point.ofFinite y ∈ S := mem_finitePart_iff.mp hy
    have hle : degP (P1Point.ofFinite y) <= S.sup degP :=
      Finset.le_sup (f := degP) hyS
    simpa [P1Point.ofFinite, degP] using hle
  exact le_antisymm hle1 hle2

/-- With maxDegP S >= 2, the P1 maximal count is the finite-part maximal count. -/
theorem numMaxP_eq_numMax_finitePart (S : Finset (P1Point Qbar)) (h2 : 2 <= maxDegP S) :
    numMaxP S = numMax (finitePart S) := by
  classical
  have hmax : maxDegP S = maxDeg (finitePart S) := maxDegP_eq_maxDeg_finitePart S h2
  have hge : 2 <= maxDeg (finitePart S) := by
    rw [← hmax]
    exact h2
  unfold numMaxP numMax
  rw [hmax]
  have hfilter : S.filter (fun p => degP p = maxDeg (finitePart S)) =
      Finset.image (fun x => P1Point.ofFinite x)
        ((finitePart S).filter (fun x => degQ x = maxDeg (finitePart S))) := by
    ext q
    constructor
    · intro hq
      rw [Finset.mem_filter] at hq
      obtain ⟨hqS, hqd⟩ := hq
      cases q with
      | none =>
          exfalso
          have h1 : degP (none : P1Point Qbar) = 1 := rfl
          rw [h1] at hqd
          omega
      | some x =>
          refine Finset.mem_image.mpr ⟨x, ?_, rfl⟩
          rw [Finset.mem_filter]
          refine ⟨mem_finitePart_iff.mpr hqS, ?_⟩
          change degQ x = maxDeg (finitePart S) at hqd
          exact hqd
    · intro hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
      rw [Finset.mem_filter] at hx ⊢
      obtain ⟨hxmem, hxd⟩ := hx
      refine ⟨mem_finitePart_iff.mp hxmem, ?_⟩
      change degQ x = maxDeg (finitePart S)
      exact hxd
  rw [hfilter]
  exact Finset.card_image_of_injective _ (fun a b h => Option.some.inj h)

#check maxDegP_eq_maxDeg_finitePart
#check numMaxP_eq_numMax_finitePart

end LeanFormal.IUT.XiFPaper.Mzk1P1FinitePartMeasureActual
end
