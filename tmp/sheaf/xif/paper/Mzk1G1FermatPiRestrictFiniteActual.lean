/-
G1-A (route §2.3) ADAPTER: the chart restriction of pi is finite (chart0 side). -/
import tmp.sheaf.xif.paper.Mzk1G1FermatPiPreimageClose2Actual
import tmp.sheaf.xif.paper.Mzk1G1FermatChartFinite2Actual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiFiniteAssemblyActual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiPreimageCloseActual
import tmp.sheaf.xif.paper.Mzk1G1FermatChartFiniteActual
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Restrict
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiRestrictFiniteActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageCloseActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageClose2Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiFiniteAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open scoped AlgebraicGeometry
theorem restrict_eq_chart0 (n : Nat) (hn : 0 < n) :
    morphismRestrict (pi n) localChart0.opensRange =
      (IsOpenImmersion.isoOfRangeEq (fermatChart0ToCurve n)
        ((pi n) ⁻¹ᵁ localChart0.opensRange).ι (by
          rw [← Scheme.Hom.coe_opensRange (f := fermatChart0ToCurve n),
            ← Scheme.Hom.coe_opensRange (f := ((pi n) ⁻¹ᵁ localChart0.opensRange).ι)]
          rw [pi_preimage_localChart0 n hn, Scheme.Opens.opensRange_ι])).symm.hom ≫
      Spec.map (CommRingCat.ofHom
        (LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFiniteActual.lamHom n)) ≫
      (IsOpenImmersion.isoOfRangeEq localChart0 localChart0.opensRange.ι (by
          rw [← Scheme.Hom.coe_opensRange (f := localChart0),
            ← Scheme.Hom.coe_opensRange (f := localChart0.opensRange.ι)]
          rw [Scheme.Opens.opensRange_ι])).hom := by
  rw [← cancel_mono localChart0.opensRange.ι]
  have h1 : (IsOpenImmersion.isoOfRangeEq (fermatChart0ToCurve n)
        ((pi n) ⁻¹ᵁ localChart0.opensRange).ι (by
          rw [← Scheme.Hom.coe_opensRange (f := fermatChart0ToCurve n),
            ← Scheme.Hom.coe_opensRange (f := ((pi n) ⁻¹ᵁ localChart0.opensRange).ι)]
          rw [pi_preimage_localChart0 n hn, Scheme.Opens.opensRange_ι])).symm.hom ≫
      fermatChart0ToCurve n = ((pi n) ⁻¹ᵁ localChart0.opensRange).ι :=
    IsOpenImmersion.isoOfRangeEq_inv_fac (f := fermatChart0ToCurve n)
      (g := ((pi n) ⁻¹ᵁ localChart0.opensRange).ι) (e := by
        rw [← Scheme.Hom.coe_opensRange (f := fermatChart0ToCurve n),
          ← Scheme.Hom.coe_opensRange (f := ((pi n) ⁻¹ᵁ localChart0.opensRange).ι)]
        rw [pi_preimage_localChart0 n hn, Scheme.Opens.opensRange_ι])
  have h2 : (IsOpenImmersion.isoOfRangeEq localChart0 localChart0.opensRange.ι (by
          rw [← Scheme.Hom.coe_opensRange (f := localChart0),
            ← Scheme.Hom.coe_opensRange (f := localChart0.opensRange.ι)]
          rw [Scheme.Opens.opensRange_ι])).hom ≫ localChart0.opensRange.ι =
      localChart0 :=
    IsOpenImmersion.isoOfRangeEq_hom_fac (f := localChart0)
      (g := localChart0.opensRange.ι) (e := by
        rw [← Scheme.Hom.coe_opensRange (f := localChart0),
          ← Scheme.Hom.coe_opensRange (f := localChart0.opensRange.ι)]
        rw [Scheme.Opens.opensRange_ι])
  simp only [Category.assoc]
  rw [h2]
  rw [show Spec.map (CommRingCat.ofHom
      (LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFiniteActual.lamHom n)) ≫
      localChart0 = piChart0 n from rfl]
  rw [← pi_ι0 n]
  rw [← Category.assoc, h1]
  rw [morphismRestrict_ι]
theorem isFinite_pi_restrict_chart0 (n : Nat) (hn : 0 < n) :
    IsFinite (morphismRestrict (pi n) localChart0.opensRange) := by
  rw [restrict_eq_chart0 n hn]
  have hg : IsFinite (Spec.map (CommRingCat.ofHom
      (LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFiniteActual.lamHom n))) :=
    LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFiniteActual.lamHomSpec_isFinite n hn
  haveI := hg
  infer_instance
/-- The restriction of pi to the t chart is the chart map, up to the chart isos. -/
theorem restrict_eq_chartInf (n : Nat) (hn : 0 < n) :
    morphismRestrict (pi n) localChartInf.opensRange =
      (IsOpenImmersion.isoOfRangeEq (fermatChartInfToCurve n)
        ((pi n) ⁻¹ᵁ localChartInf.opensRange).ι (by
          rw [← Scheme.Hom.coe_opensRange (f := fermatChartInfToCurve n),
            ← Scheme.Hom.coe_opensRange (f := ((pi n) ⁻¹ᵁ localChartInf.opensRange).ι)]
          rw [Mzk1G1FermatPiPreimageClose2Actual.pi_preimage_localChartInf n hn,
            Scheme.Opens.opensRange_ι])).symm.hom ≫
      Spec.map (CommRingCat.ofHom
        (LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFinite2Actual.lamHom2 n)) ≫
      (IsOpenImmersion.isoOfRangeEq localChartInf localChartInf.opensRange.ι (by
          rw [← Scheme.Hom.coe_opensRange (f := localChartInf),
            ← Scheme.Hom.coe_opensRange (f := localChartInf.opensRange.ι)]
          rw [Scheme.Opens.opensRange_ι])).hom := by
  rw [← cancel_mono localChartInf.opensRange.ι]
  have h1 : (IsOpenImmersion.isoOfRangeEq (fermatChartInfToCurve n)
        ((pi n) ⁻¹ᵁ localChartInf.opensRange).ι (by
          rw [← Scheme.Hom.coe_opensRange (f := fermatChartInfToCurve n),
            ← Scheme.Hom.coe_opensRange (f := ((pi n) ⁻¹ᵁ localChartInf.opensRange).ι)]
          rw [Mzk1G1FermatPiPreimageClose2Actual.pi_preimage_localChartInf n hn,
            Scheme.Opens.opensRange_ι])).symm.hom ≫
      fermatChartInfToCurve n = ((pi n) ⁻¹ᵁ localChartInf.opensRange).ι :=
    IsOpenImmersion.isoOfRangeEq_inv_fac (f := fermatChartInfToCurve n)
      (g := ((pi n) ⁻¹ᵁ localChartInf.opensRange).ι) (e := by
        rw [← Scheme.Hom.coe_opensRange (f := fermatChartInfToCurve n),
          ← Scheme.Hom.coe_opensRange (f := ((pi n) ⁻¹ᵁ localChartInf.opensRange).ι)]
        rw [Mzk1G1FermatPiPreimageClose2Actual.pi_preimage_localChartInf n hn,
          Scheme.Opens.opensRange_ι])
  have h2 : (IsOpenImmersion.isoOfRangeEq localChartInf localChartInf.opensRange.ι (by
          rw [← Scheme.Hom.coe_opensRange (f := localChartInf),
            ← Scheme.Hom.coe_opensRange (f := localChartInf.opensRange.ι)]
          rw [Scheme.Opens.opensRange_ι])).hom ≫ localChartInf.opensRange.ι =
      localChartInf :=
    IsOpenImmersion.isoOfRangeEq_hom_fac (f := localChartInf)
      (g := localChartInf.opensRange.ι) (e := by
        rw [← Scheme.Hom.coe_opensRange (f := localChartInf),
          ← Scheme.Hom.coe_opensRange (f := localChartInf.opensRange.ι)]
        rw [Scheme.Opens.opensRange_ι])
  simp only [Category.assoc]
  rw [h2]
  rw [show Spec.map (CommRingCat.ofHom
      (LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFinite2Actual.lamHom2 n)) ≫
      localChartInf = piChartInf n from rfl]
  rw [← pi_ι1 n]
  rw [← Category.assoc, h1]
  rw [morphismRestrict_ι]
/-- pi restricted to the t chart is finite. -/
theorem isFinite_pi_restrict_chartInf (n : Nat) (hn : 0 < n) :
    IsFinite (morphismRestrict (pi n) localChartInf.opensRange) := by
  rw [restrict_eq_chartInf n hn]
  have hg : IsFinite (Spec.map (CommRingCat.ofHom
      (LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFinite2Actual.lamHom2 n))) :=
    LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFinite2Actual.lamHom2Spec_isFinite n hn
  haveI := hg
  infer_instance
/-- IsFinite (pi n) for n > 0. -/
theorem isFinite_pi (n : Nat) (hn : 0 < n) : IsFinite (pi n) :=
  LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiFiniteAssemblyActual.isFinite_pi_of_chart_restrict n
    (isFinite_pi_restrict_chart0 n hn) (isFinite_pi_restrict_chartInf n hn)
#print axioms isFinite_pi
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiRestrictFiniteActual
