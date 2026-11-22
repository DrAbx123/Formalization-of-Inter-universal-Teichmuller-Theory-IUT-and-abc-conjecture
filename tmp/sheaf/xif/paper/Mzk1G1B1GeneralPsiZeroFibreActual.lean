/- B1/G-C: zero-fibre dictionary for the GENERAL two-section map psiGeneral (route §4.1).

  `Mzk1G1PsiGeneralActual.psiGeneral (u0) (u1) (compat)` is the general psi. This file records
  the chart-0 zero-fibre dictionary: a chart-0 point goes to `p1Zero` iff `u0` vanishes there
  (the same judge lemma as for `psiFixed`, but for arbitrary chart function `u0`). This is the
  scheme-level input for the general `psi^{-1}(0) = D_T` statement; it does NOT use any fixed
  choice of u0/u1, so it serves the general-T RR construction once RR provides the chart
  functions. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiGeneralActual
import tmp.sheaf.xif.paper.Mzk1G1PsiP1ZeroJudgeActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1GeneralPsiZeroFibreActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGeneralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1ZeroJudgeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual

variable (n : Nat) (T : Finset ℚ)

/-- **一般 ψ 的 chart-0 零纤维字典**：chart-0 点打到 `p1Zero` 当且仅当 `u0` 在该点消失。 -/
theorem psiGeneral_chart0_mem_p1Zero_iff (u0 : R n)
    (u1 : Localization.Away (psiChartInfDenom n T))
    (haffine : chart0ToOverlap n T ≫ chartMorphism0 u0 =
      chartInfPieceToOverlap n T ≫
        chartMorphismInf u1)
    (p : PrimeSpectrum (R n)) :
    psiGeneral n T u0 u1 haffine ((fermatChart0ToCurve n).base p) ∈ p1Zero ↔
      u0 ∈ p.asIdeal := by
  rw [← psiOpenCover_f_false n T]
  have h := congrArg (fun g => g p) (psiGeneral_ι_false n T u0 u1 haffine)
  have h' : psiGeneral n T u0 u1 haffine (((psiOpenCover n T).f ⟨false⟩) p) =
      (chartMorphism0 u0) p := h
  erw [h']
  exact chartMorphism0_mem_p1Zero_iff u0 p

/-- **一般 ψ 的 chart-0 零纤维（包含形式）**：`u0` 的零点集打到 `p1Zero`。 -/
theorem psiGeneral_chart0_image_subset_p1Zero (u0 : R n)
    (u1 : Localization.Away (psiChartInfDenom n T))
    (haffine : chart0ToOverlap n T ≫ chartMorphism0 u0 =
      chartInfPieceToOverlap n T ≫
        chartMorphismInf u1) :
    (fermatChart0ToCurve n) '' {p : PrimeSpectrum (R n) | u0 ∈ p.asIdeal} ⊆
      psiGeneral n T u0 u1 haffine ⁻¹' p1Zero := by
  rintro _ ⟨p, hp, rfl⟩
  exact (psiGeneral_chart0_mem_p1Zero_iff n T u0 u1 haffine p).mpr hp

#print axioms psiGeneral_chart0_mem_p1Zero_iff
#print axioms psiGeneral_chart0_image_subset_p1Zero
/-- **一般 ψ 的全局零纤维**：`ψ^{-1}(p1Zero) = chart-0 上 u0 的零点集`。
    t-chart 片永远打不到 `p1Zero`（`chartMorphismInf_not_mem_p1Zero`），故无需任何额外假设。 -/
theorem psiGeneral_preimage_p1Zero_eq (u0 : R n)
    (u1 : Localization.Away (psiChartInfDenom n T))
    (haffine : chart0ToOverlap n T ≫ chartMorphism0 u0 =
      chartInfPieceToOverlap n T ≫ chartMorphismInf u1) :
    (psiGeneral n T u0 u1 haffine) ⁻¹' p1Zero =
      (fermatChart0ToCurve n) '' {p : PrimeSpectrum (R n) | u0 ∈ p.asIdeal} := by
  ext y
  constructor
  · intro hy
    rcases (Set.mem_union _ _ _).mp (cover_point n T y) with h0 | h1
    · obtain ⟨p, rfl⟩ := h0
      exact Set.mem_image_of_mem _
        ((psiGeneral_chart0_mem_p1Zero_iff n T u0 u1 haffine p).mp hy)
    · obtain ⟨P, rfl⟩ := h1
      rw [show (qPiece n T) = (psiOpenCover n T).f (ULift.up true) from rfl] at hy
      rw [Set.mem_preimage] at hy
      have hι := congrArg (fun g => g P) (psiGeneral_ι_true n T u0 u1 haffine)
      have hpt : psiGeneral n T u0 u1 haffine (((psiOpenCover n T).f ⟨true⟩) P) =
          (chartMorphismInf u1) P := hι
      erw [hpt] at hy
      exact absurd hy (chartMorphismInf_not_mem_p1Zero u1 P)
  · rintro ⟨p, hp, rfl⟩
    exact (psiGeneral_chart0_mem_p1Zero_iff n T u0 u1 haffine p).mpr hp

#print axioms psiGeneral_preimage_p1Zero_eq


end LeanFormal.IUT.XiFPaper.Mzk1G1B1GeneralPsiZeroFibreActual