/- B1④ (3) final: the intersection identity U0 ⊓ qPiece.opensRange = cY.opensRange. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiRangeSupportActual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiPreimageChartActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartPreimageActual
import Mathlib.Tactic
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiInterActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineCompatActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiRangeSupportActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual
open LeanFormal.IUT.XiFPaper.Mzk1SchemeOpensRangeInterfaceActual
open scoped AlgebraicGeometry
variable (n : Nat) (T : Finset ℚ)
/-- (iii) U0 ⊓ (t-chart range) = t-chart image of D(r). -/
theorem inter_range :
    (fermatChart0ToCurve n).opensRange ⊓ (fermatChartInfToCurve n).opensRange =
      fermatChartInfToCurve n ''ᵁ
        ((Spec (CommRingCat.of (ChartInfRing n))).basicOpen (Mzk1G1PsiRangeSupportActual.secOf (r1 n))) := by
  haveI h0 : IsOpenImmersion ((fermatTwoChartGlueData n).ι (ULift.up false)) :=
    inferInstanceAs (IsOpenImmersion (fermatChart0ToCurve n))
  haveI h1 : IsOpenImmersion ((fermatTwoChartGlueData n).ι (ULift.up true)) :=
    inferInstanceAs (IsOpenImmersion (fermatChartInfToCurve n))
  rw [inf_comm]
  rw [← Scheme.Hom.image_preimage_eq_opensRange_inf
    (f := fermatChartInfToCurve n) (U := (fermatChart0ToCurve n).opensRange)]
  congr 1
  have hpre := Mzk1G1ProjectiveLineChartPreimageActual.preimage_opensRange_ι
    (D := fermatTwoChartGlueData n) (ULift.up true) (ULift.up false)
  show ((fermatTwoChartGlueData n).ι (ULift.up true)) ⁻¹ᵁ
      ((fermatTwoChartGlueData n).ι (ULift.up false)).opensRange =
    ((Spec (CommRingCat.of (ChartInfRing n))).basicOpen (Mzk1G1PsiRangeSupportActual.secOf (r1 n)))
  rw [hpre]
  exact Mzk1G1FermatPiPreimageChartActual.overlapToChartInf_opensRange n
/-- (v) an open immersion preserves the infimum of opens. -/
theorem image_inf {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] (U V : X.Opens) :
    f ''ᵁ (U ⊓ V) = f ''ᵁ U ⊓ f ''ᵁ V := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  · rintro ⟨⟨x, hxU, rfl⟩, ⟨x', hxV, hx'⟩⟩
    have hxx : x = x' := f.isOpenEmbedding.injective hx'.symm
    subst hxx
    exact ⟨x, ⟨hxU, hxV⟩, rfl⟩
/-- (iv) basicOpen of a product is the infimum of the basic opens. -/
theorem basicOpen_mul (n : Nat) (T : Finset ℚ) :
    (Spec (CommRingCat.of (R2 n))).basicOpen
        (Mzk1G1PsiRangeSupportActual.secOf (psiChartInfDenom n T * chartR n)) =
      (Spec (CommRingCat.of (R2 n))).basicOpen
          (Mzk1G1PsiRangeSupportActual.secOf (psiChartInfDenom n T)) ⊓
        (Spec (CommRingCat.of (R2 n))).basicOpen (Mzk1G1PsiRangeSupportActual.secOf (chartR n)) := by
  simpa only [Mzk1G1PsiRangeSupportActual.secOf, map_mul] using
    (Scheme.basicOpen_mul (X := Spec (CommRingCat.of (R2 n)))
      (Mzk1G1PsiRangeSupportActual.secOf (psiChartInfDenom n T))
      (Mzk1G1PsiRangeSupportActual.secOf (chartR n)))
#print axioms inter_range
#print axioms image_inf
#print axioms basicOpen_mul
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiInterActual