import tmp.sheaf.xif.paper.Mzk1G1PsiCoverActual
import tmp.sheaf.xif.paper.Mzk1GlueCocycleActual
import tmp.sheaf.xif.paper.Mzk1G1PsiAffineCompatActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import tmp.sheaf.xif.paper.Mzk1GlueMorphismActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHcompRightActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartInfCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineCompatActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1HullFermatGluingActual

variable (n : Nat) (T : Finset ℚ)

/-- The chart morphism of psi on the first piece U0: t = psiChart0Coord (the protected
product), into the t-chart of P^1. -/
noncomputable def psiChart0 : (psiOpenCover n T).X (ULift.up false) ⟶
    Mzk1G1ProjectiveLineGluedActual.projectiveLineGlued :=
  chartMorphismInf (R := R n) (psiChart0Coord n T)

/-- The chart morphism of psi on the second piece D(q): lambda = psiChartInfCoord, into the
lambda-chart of P^1. -/
noncomputable def psiChart1 : (psiOpenCover n T).X (ULift.up true) ⟶
    Mzk1G1ProjectiveLineGluedActual.projectiveLineGlued :=
  chartMorphism0 (R := Localization.Away (psiChartInfDenom n T)) (psiChartInfCoord n T)

/-- Y_n glue condition: the two overlap inclusions into Y_n agree.  Derived from the
generic eqToHom cocycle lemma (Mzk1GlueCocycleActual), which sidesteps the non-definitional
identification of 𝟙 (V (i,j)) with a morphism out of V (j,i). -/
theorem overlapToCurve_condition :
    Mzk1G1FermatOverlapActual.overlapToChart0 n ≫ fermatChart0ToCurve n =
      Mzk1G1FermatOverlapActual.overlapToChartInf n ≫ fermatChartInfToCurve n := by
  have hV : (fermatTwoChartGlueData n).V (ULift.up false, ULift.up true) =
      (fermatTwoChartGlueData n).V (ULift.up true, ULift.up false) := rfl
  have ht : (fermatTwoChartGlueData n).t (ULift.up false) (ULift.up true) = eqToHom hV := by
    simp [fermatTwoChartGlueData, twoChartGlueData, twoChartT]
  have h := Mzk1GlueCocycleActual.glue_condition_eqToHom (D := fermatTwoChartGlueData n)
    (ULift.up false) (ULift.up true) hV ht
  exact h.symm

-- NOTE (reuse check done): the user-facing cocycle equation
--   overlapToChart0 n ≫ fermatChart0ToCurve n = overlapToChartInf n ≫ fermatChartInfToCurve n
-- is NOT yet available anywhere; it is a known hard restatement documented in
-- Mzk1G1FermatTwoChartGluingActual.lean (technical note after fermatOverlapToCurve):
-- deriving it from Scheme.GlueData.glue_condition fails because the defeq check
-- V (i,j) = V (j,i) does not fire (opaque twoChartV match on the ULift pair).
-- Candidate fixes (three, from that note): (a) generic two-index cocycle lemma stated with
-- a V-equality hypothesis + eqToHom; (b) redefine twoChartV so V (false,true) and
-- V (true,false) are the same term syntactically; (c) transport chart maps through the
-- pullback iso instead of rewriting inside the glue_condition equation.
-- Tracked as the only remaining prerequisite of hcomp (B1 step 4).
/-- LEFT LEG of hcomp: the first-chart leg factors through the overlap. -/
theorem hcomp_left_eq (n : Nat) (T : Finset ℚ) :
    chart0ToOverlap n T ≫ fermatChart0ToCurve n =
      Spec.map (CommRingCat.ofHom (infToOverlap n T)) ≫
        Spec.map (CommRingCat.ofHom (Mzk1G1FermatOverlapActual.alpha n)) ≫
          Mzk1G1FermatOverlapActual.overlapToChart0 n ≫ fermatChart0ToCurve n := by
  have hr : rToOverlap n T =
      (infToOverlap n T).comp ((Mzk1G1FermatOverlapActual.alpha n).comp
        (algebraMap (R n) (Overlap0 n))) := by
    rw [rToOverlap, ← Mzk1G1FermatOverlapActual.alpha_comp_algebraMap n]
  rw [chart0ToOverlap, hr]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    show Spec.map (CommRingCat.ofHom (algebraMap (R n) (Overlap0 n))) =
      Mzk1G1FermatOverlapActual.overlapToChart0 n from rfl]

/-- HCOMP: the two chart legs agree over Y_n (the compatibility input of
glueMorphisms for psi).  Uses henry hcomp_right_eq (17:30:23) + our HY. -/
theorem hcomp (n : Nat) (T : Finset ℚ) :
    chart0ToOverlap n T ≫ fermatChart0ToCurve n =
      chartInfPieceToOverlap n T ≫ qPiece n T := by
  rw [hcomp_left_eq n T, Mzk1G1PsiHcompRightActual.hcomp_right_eq n T,
    ← overlapToCurve_condition n]

/-- The comparison map from the overlap affine chart to the pullback of the two cover
pieces of psi. -/
noncomputable def wToPullback (n : Nat) (T : Finset ℚ) :
    Spec (CommRingCat.of (overlapRing n T)) ⟶
      pullback ((psiOpenCover n T).f (ULift.up false)) ((psiOpenCover n T).f (ULift.up true)) :=
  pullback.lift (chart0ToOverlap n T) (chartInfPieceToOverlap n T) (hcomp n T)

theorem wToPullback_fst (n : Nat) (T : Finset ℚ) :
    wToPullback n T ≫
        pullback.fst ((psiOpenCover n T).f (ULift.up false)) ((psiOpenCover n T).f (ULift.up true))
      = chart0ToOverlap n T :=
  pullback.lift_fst _ _ _

theorem wToPullback_snd (n : Nat) (T : Finset ℚ) :
    wToPullback n T ≫
        pullback.snd ((psiOpenCover n T).f (ULift.up false)) ((psiOpenCover n T).f (ULift.up true))
      = chartInfPieceToOverlap n T :=
  pullback.lift_snd _ _ _

#print axioms wToPullback
#print axioms wToPullback_fst
#print axioms wToPullback_snd
#print axioms hcomp
#print axioms hcomp_left_eq
#print axioms psiChart0
#print axioms psiChart1
#print axioms overlapToCurve_condition
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiGlobalActual
