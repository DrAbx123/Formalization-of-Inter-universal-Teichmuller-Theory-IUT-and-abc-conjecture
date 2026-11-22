import tmp.sheaf.xif.paper.Mzk1G1PsiXiActual
import tmp.sheaf.xif.paper.Mzk1G1PsiChartMapsActual
import tmp.sheaf.xif.paper.Mzk1G1PsiChartInfCoverActual
import tmp.sheaf.xif.paper.Mzk1G1FermatSecondChartActual
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual

variable (n : Nat) (T : Finset ℚ)

/-- The common affine overlap of the first Fermat chart and the open D(q) of the second
chart: it is the localization of the second chart ring at q * r. -/
noncomputable abbrev overlapRing : Type :=
  Localization.Away (psiChartInfDenom n T * chartR n)

/-- The overlap localization map from the second chart ring. -/
noncomputable def r2ToOverlap : R2 n →+* overlapRing n T :=
  algebraMap (R2 n) (overlapRing n T)

/-- The image of q in the overlap is a unit. -/
theorem isUnit_q : IsUnit (r2ToOverlap n T (psiChartInfDenom n T)) := by
  have h : IsUnit (r2ToOverlap n T (psiChartInfDenom n T * chartR n)) :=
    IsLocalization.Away.algebraMap_isUnit (S := overlapRing n T)
      (x := psiChartInfDenom n T * chartR n)
  rw [map_mul] at h
  exact isUnit_of_dvd_unit (dvd_mul_right _ _) h

/-- The image of r in the overlap is a unit. -/
theorem isUnit_r : IsUnit (r2ToOverlap n T (chartR n)) := by
  have h : IsUnit (r2ToOverlap n T (psiChartInfDenom n T * chartR n)) :=
    IsLocalization.Away.algebraMap_isUnit (S := overlapRing n T)
      (x := psiChartInfDenom n T * chartR n)
  rw [map_mul] at h
  exact isUnit_of_dvd_unit (dvd_mul_left _ _) h

/-- The localization map from the chart at infinity overlap ring to the common overlap. -/
noncomputable def infToOverlap : OverlapInf n →+* overlapRing n T :=
  IsLocalization.Away.lift (S := OverlapInf n) (x := r1 n) (g := r2ToOverlap n T) (by
    have h : r2ToOverlap n T (r1 n) = r2ToOverlap n T (chartR n) := rfl
    rw [h]; exact isUnit_r n T)

/-- The map from the first chart ring to the common overlap (through the overlap
isomorphism of the two Fermat charts). -/
noncomputable def rToOverlap : R n →+* overlapRing n T :=
  (infToOverlap n T).comp (psi n)

/-- The q-chart map from the common overlap to the localization of the second chart. -/
noncomputable def qToOverlap : Localization.Away (psiChartInfDenom n T) →+* overlapRing n T :=
  IsLocalization.Away.lift (x := psiChartInfDenom n T) (g := r2ToOverlap n T) (isUnit_q n T)

/-- The first chart map from the common overlap. -/
noncomputable def chart0ToOverlap : Spec (CommRingCat.of (overlapRing n T)) ⟶
    Spec (CommRingCat.of (R n)) :=
  Spec.map (CommRingCat.ofHom (rToOverlap n T))

/-- The q-chart map from the common overlap. -/
noncomputable def chartInfPieceToOverlap : Spec (CommRingCat.of (overlapRing n T)) ⟶
    Spec (CommRingCat.of (Localization.Away (psiChartInfDenom n T))) :=
  Spec.map (CommRingCat.ofHom (qToOverlap n T))

/-! ## Chart morphisms along a change of coordinate ring

For a ring hom f : A -> B, composing the affine chart map Spec.map f with a chart morphism
of P^1 is the chart morphism of the transported coordinate. -/

section ChartComp
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
  (f : A →+* B)

theorem chartMorphismInf_comp (hf : f.comp (algebraMap ℚ A) = algebraMap ℚ B) (a : A) :
    Spec.map (CommRingCat.ofHom f) ≫
        chartMorphismInf (R := A) a =
      chartMorphismInf (R := B) (f a) := by
  rw [chartMorphismInf, chartMorphismInf, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  have hring : f.comp (evalAt (R := A) a) = evalAt (R := B) (f a) := by
    apply Polynomial.ringHom_ext
    · intro r
      show f ((evalAt (R := A) a) (Polynomial.C r)) =
        (evalAt (R := B) (f a)) (Polynomial.C r)
      rw [evalAt_C, evalAt_C]
      have := RingHom.congr_fun hf r
      simpa using this
    · show f ((evalAt (R := A) a) Polynomial.X) =
        (evalAt (R := B) (f a)) Polynomial.X
      rw [evalAt_X, evalAt_X]
  rw [hring]

theorem chartMorphism0_comp (hf : f.comp (algebraMap ℚ A) = algebraMap ℚ B) (a : A) :
    Spec.map (CommRingCat.ofHom f) ≫
        chartMorphism0 (R := A) a =
      chartMorphism0 (R := B) (f a) := by
  rw [chartMorphism0, chartMorphism0, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  have hring : f.comp (evalAt (R := A) a) = evalAt (R := B) (f a) := by
    apply Polynomial.ringHom_ext
    · intro r
      show f ((evalAt (R := A) a) (Polynomial.C r)) =
        (evalAt (R := B) (f a)) (Polynomial.C r)
      rw [evalAt_C, evalAt_C]
      have := RingHom.congr_fun hf r
      simpa using this
    · show f ((evalAt (R := A) a) Polynomial.X) =
        (evalAt (R := B) (f a)) Polynomial.X
      rw [evalAt_X, evalAt_X]
  rw [hring]

end ChartComp

#print axioms isUnit_q
#print axioms isUnit_r
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
