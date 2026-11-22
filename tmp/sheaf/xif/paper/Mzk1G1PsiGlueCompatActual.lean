/- B1④ (4)(5): compatibility of the psi chart morphisms on the pullback, and psi itself.
henry's ADAPTER file; emmy imports the names.  Uses emmy's
`wToPullback` (+ fst/snd) and `affine_compat`; `IsIso (wToPullback n T)` is the
remaining obligation of (3), kept as a typeclass argument here. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiGlobalActual
import tmp.sheaf.xif.paper.Mzk1G1PsiIsoActual
import Mathlib.Tactic
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiGlueCompatActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineCompatActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open scoped AlgebraicGeometry
variable (n : Nat) (T : Finset ℚ)
/-- The chart morphisms of psi, indexed by the two cover pieces. -/
noncomputable def psiFun :
    ∀ i : (psiOpenCover n T).I₀, (psiOpenCover n T).X i ⟶ projectiveLineGlued :=
  fun i => match i with
    | ULift.up false => psiChart0 n T
    | ULift.up true => psiChart1 n T
set_option maxHeartbeats 2000000 in
/-- Compatibility of psiFun on the pullback of the two cover pieces. -/
theorem glueMorphisms_compat :
    ∀ x y : (psiOpenCover n T).I₀,
      pullback.fst ((psiOpenCover n T).f x) ((psiOpenCover n T).f y) ≫ psiFun n T x =
        pullback.snd ((psiOpenCover n T).f x) ((psiOpenCover n T).f y) ≫ psiFun n T y := by
  -- the mixed (false,true) compatibility
  have hmixed : pullback.fst ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
      ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) ≫ psiChart0 n T =
      pullback.snd ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
        ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) ≫ psiChart1 n T := by
    have hw : wToPullback n T ≫
        (pullback.fst ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
            ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) ≫ psiChart0 n T)
      = wToPullback n T ≫
        (pullback.snd ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
            ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) ≫ psiChart1 n T) := by
      rw [← Category.assoc, ← Category.assoc, wToPullback_fst, wToPullback_snd]
      exact Mzk1G1PsiAffineCompatActual.affine_compat n T
    haveI : Epi (wToPullback n T) := inferInstance
    exact (cancel_epi (wToPullback n T)).mp hw
  intro x y
  obtain ⟨bx⟩ := x
  obtain ⟨by'⟩ := y
  cases bx <;> cases by'
  · -- both pieces are the first chart
    dsimp only [psiFun]
    have hfs : pullback.fst ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
        ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀)) = pullback.snd _ _ := by
      rw [← cancel_mono ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))]
      rw [pullback.condition]
    rw [hfs]
  · -- first chart against the D(q) piece
    dsimp only [psiFun]
    exact hmixed
  · -- D(q) piece against the first chart: transpose of hmixed along pullbackSymmetry
    dsimp only [psiFun]
    haveI : Epi (pullbackSymmetry ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
        ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀))).hom := inferInstance
    rw [← cancel_epi (pullbackSymmetry ((psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀))
      ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀))).hom]
    rw [← Category.assoc, ← Category.assoc]
    rw [pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst]
    exact hmixed.symm
  · -- both pieces are the D(q) piece
    dsimp only [psiFun]
    have hfs : pullback.fst ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀))
        ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀)) = pullback.snd _ _ := by
      rw [← cancel_mono ((psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀))]
      rw [pullback.condition]
    rw [hfs]
/-- The glued morphism psi : Y_n ⟶ P^1 (assembly (5)). -/
noncomputable def psi :
    fermatCurveScheme n ⟶ projectiveLineGlued :=
  (psiOpenCover n T).glueMorphisms (psiFun n T) (glueMorphisms_compat n T)
theorem psi_ι_false :
    (psiOpenCover n T).f (ULift.up false : (psiOpenCover n T).I₀) ≫ psi n T = psiChart0 n T :=
  Scheme.Cover.ι_glueMorphisms (𝒰 := psiOpenCover n T) (f := psiFun n T)
    (hf := glueMorphisms_compat n T) (ULift.up false : (psiOpenCover n T).I₀)
theorem psi_ι_true :
    (psiOpenCover n T).f (ULift.up true : (psiOpenCover n T).I₀) ≫ psi n T = psiChart1 n T :=
  Scheme.Cover.ι_glueMorphisms (𝒰 := psiOpenCover n T) (f := psiFun n T)
    (hf := glueMorphisms_compat n T) (ULift.up true : (psiOpenCover n T).I₀)
#print axioms glueMorphisms_compat
#print axioms psi
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiGlueCompatActual