import tmp.sheaf.xif.paper.Mzk1G1PsiFixedActual
import tmp.sheaf.xif.paper.Mzk1G1PsiCoverActual
import tmp.sheaf.xif.paper.Mzk1G1PsiP1ZeroJudgeActual
import Mathlib.Tactic

/-!
# t-chart form of `psiFixed` on the D(q) piece, and its avoidance of `p1Zero`

`psiFixed` (Mzk1G1PsiFixedActual) is the glued map with first piece
`chartMorphism0 (psiChart0Coord)` and second piece
`chartMorphismInf (psiChartInfCoord)` — this is exactly its definition on the D(q) piece,
recorded in `psiFixed_ι_true`.  Note that the *unswapped* chart morphism
`Mzk1G1PsiGlobalActual.psiChart1` is the lambda-chart map `chartMorphism0` on the same
piece, so the correct point formula for `psiFixed` is the t-chart one below (a
`chartMorphism0`/lambda-chart statement would be false).

andrew's `Mzk1G1B2Fixed5Actual` compares `psiFixed⁻¹ (p1Zero)` with `D_T`; its
second-chart contribution needs

* the point formula for `psiFixed` on the D(q) piece, and
* the resulting fact that no point of the D(q) piece maps to `p1Zero`
  (the qPiece piece lands in the t-chart, and `chartMorphismInf_not_mem_p1Zero` says
  the t-chart never meets the lambda = 0 point of the glued P^1).

Both reduce to `psiFixed_ι_true` via `Scheme.Hom.comp_apply` and the definitional
identification `(psiOpenCover n T).f (ULift.up true) = qPiece n T`
(`psiOpenCover_f_true`).
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedTChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1ZeroJudgeActual

/-- **Point formula of `psiFixed` on the D(q) piece (t-chart form)**:
on the second piece `qPiece` of the two-piece cover, `psiFixed` is the t-chart point
`t = psiChartInfCoord`. -/
theorem psiFixed_qPiece_apply (n : Nat) (T : Finset ℚ)
    (P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T))) :
    (psiFixed n T).base ((qPiece n T).base P) =
      (chartMorphismInf (R := Localization.Away (psiChartInfDenom n T))
        (psiChartInfCoord n T)).base P := by
  have hι : qPiece n T ≫ psiFixed n T =
      chartMorphismInf (R := Localization.Away (psiChartInfDenom n T))
        (psiChartInfCoord n T) :=
    psiFixed_ι_true n T
  calc (psiFixed n T).base ((qPiece n T).base P)
      = ((qPiece n T) ≫ psiFixed n T).base P :=
        (Scheme.Hom.comp_apply (qPiece n T) (psiFixed n T) P).symm
    _ = (chartMorphismInf (R := Localization.Away (psiChartInfDenom n T))
          (psiChartInfCoord n T)).base P := by rw [hι]

/-- **`psiFixed` on the D(q) piece avoids the point lambda = 0**:
the t-chart piece of `psiFixed` lands in the t-chart of P^1, which is disjoint from
`p1Zero` (`chartMorphismInf_not_mem_p1Zero`). -/
theorem psiFixed_qPiece_notMem_p1Zero (n : Nat) (T : Finset ℚ)
    (P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T))) :
    (psiFixed n T).base ((qPiece n T).base P) ∉ p1Zero := by
  rw [psiFixed_qPiece_apply n T P]
  exact chartMorphismInf_not_mem_p1Zero (R := Localization.Away (psiChartInfDenom n T))
    (psiChartInfCoord n T) P

/-- Variant stated with a point `P` of the second Fermat chart lying in the D(q) piece
(`q = psiChartInfDenom` not in `P`): its image in `Y_n` does not map to lambda = 0.
The lift `Q` of `P` to the localization exists by `mem_range_localization_iff`. -/
theorem psiFixed_chartInf_notMem_p1Zero (n : Nat) (T : Finset ℚ)
    (P : PrimeSpectrum (R2 n)) (hq : psiChartInfDenom n T ∉ P.asIdeal) :
    (psiFixed n T).base ((fermatChartInfToCurve n).base P) ∉ p1Zero := by
  obtain ⟨Q, hQ⟩ := (mem_range_localization_iff n (psiChartInfDenom n T) P).mpr hq
  have hspec : (Spec.map (CommRingCat.ofHom
      (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T))))).base Q = P := hQ
  have hpt : (qPiece n T).base Q = (fermatChartInfToCurve n).base P := by
    rw [qPiece, Scheme.Hom.comp_apply, hspec]
  rw [← hpt]
  exact psiFixed_qPiece_notMem_p1Zero n T Q

#print axioms psiFixed_qPiece_apply
#print axioms psiFixed_qPiece_notMem_p1Zero
#print axioms psiFixed_chartInf_notMem_p1Zero
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedTChartActual
end
