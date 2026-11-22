import tmp.sheaf.xif.paper.Mzk1G1PsiP1ZeroJudgeActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFixedActual
import tmp.sheaf.xif.paper.Mzk1G1NoncriticalPsiActual
import Mathlib.Tactic
/-!
# B2: `psiFixed` zero fibre on the first cover piece

Instead of projecting `psiOpenCover`'s by-block `f`/`X` fields explicitly, we state the
chart-0 zero-fibre characterization directly for points `x : (psiOpenCover n T).X false`.
`psiFixed_ι_false` then gives `psiFixed (f x) = chartMorphism0 u x` by `Scheme.Hom.comp_apply`,
and the judgment lemma of `Mzk1G1PsiP1ZeroJudgeActual` converts this to `u ∈ x.asIdeal`.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFixedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1ZeroJudgeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
variable (n : Nat) (T : Finset ℚ)

/-- On the first chart, `psiFixed` is `chartMorphism0 (psiChart0Coord)`. -/
theorem psiFixed_chart0_apply (p : PrimeSpectrum (R n)) :
    psiFixed n T ((fermatChart0ToCurve n).base p)
      = chartMorphism0 (R := R n) (psiChart0Coord n T) p := by
  have hm : fermatChart0ToCurve n ≫ psiFixed n T
      = chartMorphism0 (R := R n) (psiChart0Coord n T) := by
    rw [← psiOpenCover_f_false n T]
    exact psiFixed_ι_false n T
  have h := congrArg
    (fun g : fermatChart0Scheme n ⟶ projectiveLineGlued => g p) hm
  rw [Scheme.Hom.comp_apply] at h
  simpa using h

#print axioms psiFixed_chart0_apply

/-- The protected set `D_T` on the curve (first chart), as a point set. -/
noncomputable def DTFixed : Set (fermatCurveScheme n) :=
  (fermatChart0ToCurve n).base ''
    {p : PrimeSpectrum (R n) | ∃ t ∈ T, chartX n - algebraMap ℚ (R n) t ∈ p.asIdeal}

/-- Chart-0 zero-fibre characterization for `psiFixed` (B2 direction). -/
theorem psiFixed_chart0_mem_p1Zero_iff (p : PrimeSpectrum (R n)) :
    psiFixed n T ((fermatChart0ToCurve n).base p) ∈ p1Zero ↔
      ∃ t ∈ T, chartX n - algebraMap ℚ (R n) t ∈ p.asIdeal := by
  rw [psiFixed_chart0_apply n T p]
  exact (chartMorphism0_mem_p1Zero_iff (psiChart0Coord n T) p).trans
    (psiChart0Coord_mem_iff n T p.asIdeal)

/-- `psiFixed` maps every protected point of `D_T` to the zero point. -/
theorem psiFixed_protected_mem_p1Zero (p : PrimeSpectrum (R n))
    (hp : ∃ t ∈ T, chartX n - algebraMap ℚ (R n) t ∈ p.asIdeal) :
    psiFixed n T ((fermatChart0ToCurve n).base p) ∈ p1Zero :=
  (psiFixed_chart0_mem_p1Zero_iff n T p).mpr hp

#print axioms psiFixed_chart0_mem_p1Zero_iff
#print axioms psiFixed_protected_mem_p1Zero

/-- The map `psiFixed` sends the whole protected set `D_T` into the zero point. -/
theorem psiFixed_image_DTFixed_subset_p1Zero :
    psiFixed n T '' DTFixed n T ⊆ p1Zero := by
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨p, hp, rfl⟩ := hx
  exact psiFixed_protected_mem_p1Zero n T p hp

#print axioms psiFixed_image_DTFixed_subset_p1Zero
end LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual
end