import tmp.sheaf.xif.paper.Mzk1G1B2Fixed4Actual
import tmp.sheaf.xif.paper.Mzk1G1PsiFixedTChartActual
import tmp.sheaf.xif.paper.Mzk1G1PsiCoverActual
import Mathlib.Tactic
/-!
# B2: global zero fibre `psiFixed⁻¹(p1Zero) = D_T`

`Mzk1G1PsiFixedTChartActual` (emmy, DONE 23:34:23) supplies
`psiFixed_qPiece_notMem_p1Zero`, so the `qPiece`/t-chart piece contributes nothing.
Together with the chart-0 characterization of `Mzk1G1B2Fixed4Actual` this gives the
unconditional global equality.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedTChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
variable (n : Nat) (T : Finset ℚ)

/-- **B2 global**: `psiFixed⁻¹(p1Zero) = DTFixed`. -/
theorem psiFixed_preimage_p1Zero_eq_DT :
    psiFixed n T ⁻¹' p1Zero = DTFixed n T := by
  ext y
  constructor
  · intro hy
    rcases (Set.mem_union _ _ _).mp (cover_point n T y) with h0 | h1
    · obtain ⟨p, rfl⟩ := h0
      exact Set.mem_image_of_mem _ ((psiFixed_chart0_mem_p1Zero_iff n T p).mp hy)
    · obtain ⟨P, rfl⟩ := h1
      exact absurd hy (by simpa using psiFixed_qPiece_notMem_p1Zero n T P)
  · rintro ⟨p, hp, rfl⟩
    exact psiFixed_protected_mem_p1Zero n T p hp

#print axioms psiFixed_preimage_p1Zero_eq_DT
end LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
end