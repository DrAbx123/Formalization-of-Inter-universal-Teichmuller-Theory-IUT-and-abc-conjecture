/- G1-A (route 2.3): the lambda-chart restriction of pi is finite.
   Reuse check: old corpus has only the API pattern (S2555ExtractionTransportActual:30 arrow_mk_iso_iff (P := @IsFinite));
   no existing IsFinite(pi|_U) lemma; accepted layer has no AG finite donor; Mathlib gives isoOfRangeEq/arrow_mk_iso_iff.
   Conclusion: ADAPTER -- pure assembly from our new h0 (pi_preimage_localChart0) + lamHomSpec_isFinite.
   No sorry/admit/axiom/PUnit/True/toy. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatPiPreimageCloseActual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiPreimageClose2Actual
import tmp.sheaf.xif.paper.Mzk1G1FermatChartFiniteActual
import tmp.sheaf.xif.paper.Mzk1G1FermatChartFinite2Actual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiFiniteAssemblyActual
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiFiniteChartActual
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFiniteActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageCloseActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiPreimageClose2Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFinite2Actual

/-- piChart0 = Spec.map(lamHom) >> localChart0（定义展开）。 -/
theorem piChart0_eq_lamSpec (n : Nat) :
    piChart0 n = Spec.map (CommRingCat.ofHom (lamHom n)) ≫ localChart0 := rfl

/-- piChartInf = Spec.map(lamHom2) >> localChartInf（定义展开）。 -/
theorem piChartInf_eq_lamSpec2 (n : Nat) :
    piChartInf n = Spec.map (CommRingCat.ofHom (lamHom2 n)) ≫ localChartInf := rfl

/-- piChart0 = Spec.map(lamHom) >> localChart0（定义展开）。 -/
theorem chart0_toCurve_range_eq (n : Nat) :
    Set.range (fermatChart0ToCurve n) =
      Set.range ((fermatChart0ToCurve n).opensRange).ι := by
  rw [← Scheme.Hom.coe_opensRange (f := fermatChart0ToCurve n),
    ← Scheme.Hom.coe_opensRange (f := ((fermatChart0ToCurve n).opensRange).ι),
    Scheme.Opens.opensRange_ι]

theorem localChart0_range_eq :
    Set.range localChart0 = Set.range (localChart0.opensRange).ι := by
  rw [← Scheme.Hom.coe_opensRange (f := localChart0),
    ← Scheme.Hom.coe_opensRange (f := (localChart0.opensRange).ι),
    Scheme.Opens.opensRange_ι]

#print axioms piChartInf_eq_lamSpec2
#print axioms piChart0_eq_lamSpec
#print axioms chart0_toCurve_range_eq
#print axioms localChart0_range_eq
/-- **λ-chart 上 π 的限制有限**：把 `pi ∣_ U0` 经 `homOfLE`（同 opens）+ `isoOfRangeEq` 化成
    `Spec.map(lamHom)` 的 arrow，再 `MorphismProperty.arrow_mk_iso_iff` 运输。 -/
theorem isFinite_pi_of_chart0_restrict (n : Nat) (hn : 0 < n) :
    IsFinite (pi n ∣_ localChart0.opensRange) := by
  let U0 : Mzk1G1ProjectiveLineGluedActual.projectiveLineGlued.Opens := localChart0.opensRange
  let W : (fermatCurveScheme n).Opens := (fermatChart0ToCurve n).opensRange
  let q : fermatChart0Scheme n ⟶ Mzk1G1ProjectiveLineGluedActual.chart0Scheme :=
    Spec.map (CommRingCat.ofHom (lamHom n))
  have hqfin : IsFinite q := lamHomSpec_isFinite n hn
  have h0 : (pi n) ⁻¹ᵁ U0 = W := pi_preimage_localChart0 n hn
  let eW : fermatChart0Scheme n ≅ W := IsOpenImmersion.isoOfRangeEq (fermatChart0ToCurve n) W.ι
    (chart0_toCurve_range_eq n)
  let eU : Mzk1G1ProjectiveLineGluedActual.chart0Scheme ≅ U0 :=
    IsOpenImmersion.isoOfRangeEq localChart0 U0.ι localChart0_range_eq
  have hWι : W.ι = eW.inv ≫ fermatChart0ToCurve n :=
    (IsOpenImmersion.isoOfRangeEq_inv_fac (fermatChart0ToCurve n) W.ι
      (chart0_toCurve_range_eq n)).symm
  have hUι : localChart0 = eU.hom ≫ U0.ι :=
    (IsOpenImmersion.isoOfRangeEq_hom_fac localChart0 U0.ι localChart0_range_eq).symm
  have hpi : fermatChart0ToCurve n ≫ pi n = q ≫ localChart0 := by
    rw [pi_ι0, piChart0_eq_lamSpec]
  have hrange : Set.range ((pi n) ⁻¹ᵁ U0).ι = Set.range (fermatChart0ToCurve n) := by
    rw [← Scheme.Hom.coe_opensRange (f := ((pi n) ⁻¹ᵁ U0).ι),
      ← Scheme.Hom.coe_opensRange (f := fermatChart0ToCurve n),
      Scheme.Opens.opensRange_ι, h0, Scheme.Hom.coe_opensRange]
  let eLeft : ((pi n) ⁻¹ᵁ U0 : Scheme) ≅ fermatChart0Scheme n :=
    IsOpenImmersion.isoOfRangeEq ((pi n) ⁻¹ᵁ U0).ι (fermatChart0ToCurve n) hrange
  have hL : eLeft.inv ≫ ((pi n) ⁻¹ᵁ U0).ι = fermatChart0ToCurve n :=
    IsOpenImmersion.isoOfRangeEq_inv_fac ((pi n) ⁻¹ᵁ U0).ι (fermatChart0ToCurve n) hrange
  have hL2 : eLeft.hom ≫ fermatChart0ToCurve n = ((pi n) ⁻¹ᵁ U0).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac ((pi n) ⁻¹ᵁ U0).ι (fermatChart0ToCurve n) hrange
  have hcomm : (pi n ∣_ U0) ≫ eU.inv = eLeft.hom ≫ q := by
    rw [← cancel_mono localChart0]
    rw [Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac localChart0 U0.ι
      localChart0_range_eq]
    rw [morphismRestrict_ι]
    simp only [Category.assoc]
    rw [← hpi]
    rw [← Category.assoc, hL2]
  have hcomm' : eLeft.hom ≫ q = (pi n ∣_ U0) ≫ eU.symm.hom := hcomm.symm
  let e : Arrow.mk (pi n ∣_ U0) ≅ Arrow.mk q := Arrow.isoMk eLeft eU.symm hcomm'
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) e).mpr hqfin

/-- **t-chart 上 π 的限制有限**（镜像 chart0 证明）。 -/
theorem isFinite_pi_of_chartInf_restrict (n : Nat) (hn : 0 < n) :
    IsFinite (pi n ∣_ localChartInf.opensRange) := by
  let U1 : Mzk1G1ProjectiveLineGluedActual.projectiveLineGlued.Opens := localChartInf.opensRange
  let W : (fermatCurveScheme n).Opens := (fermatChartInfToCurve n).opensRange
  let q : fermatChartInfScheme n ⟶ Mzk1G1ProjectiveLineGluedActual.chartInfScheme :=
    Spec.map (CommRingCat.ofHom (lamHom2 n))
  have hqfin : IsFinite q := lamHom2Spec_isFinite n hn
  have h0 : (pi n) ⁻¹ᵁ U1 = W := pi_preimage_localChartInf n hn
  have hpi : fermatChartInfToCurve n ≫ pi n = q ≫ localChartInf := by
    rw [pi_ι1]
    exact piChartInf_eq_lamSpec2 n
  have hrange : Set.range ((pi n) ⁻¹ᵁ U1).ι = Set.range (fermatChartInfToCurve n) := by
    rw [← Scheme.Hom.coe_opensRange (f := ((pi n) ⁻¹ᵁ U1).ι),
      ← Scheme.Hom.coe_opensRange (f := fermatChartInfToCurve n),
      Scheme.Opens.opensRange_ι, h0, Scheme.Hom.coe_opensRange]
  have hrangeU : Set.range localChartInf = Set.range (localChartInf.opensRange).ι := by
    rw [← Scheme.Hom.coe_opensRange (f := localChartInf),
      ← Scheme.Hom.coe_opensRange (f := (localChartInf.opensRange).ι),
      Scheme.Opens.opensRange_ι]
  let eRight : Mzk1G1ProjectiveLineGluedActual.chartInfScheme ≅ U1 :=
    IsOpenImmersion.isoOfRangeEq localChartInf U1.ι hrangeU
  let eLeft : ((pi n) ⁻¹ᵁ U1 : Scheme) ≅ fermatChartInfScheme n :=
    IsOpenImmersion.isoOfRangeEq ((pi n) ⁻¹ᵁ U1).ι (fermatChartInfToCurve n) hrange
  have hL2 : eLeft.hom ≫ fermatChartInfToCurve n = ((pi n) ⁻¹ᵁ U1).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac ((pi n) ⁻¹ᵁ U1).ι (fermatChartInfToCurve n) hrange
  have hcomm : (pi n ∣_ U1) ≫ eRight.inv = eLeft.hom ≫ q := by
    rw [← cancel_mono localChartInf]
    rw [Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac localChartInf U1.ι hrangeU]
    rw [morphismRestrict_ι]
    simp only [Category.assoc]
    rw [← hpi]
    rw [← Category.assoc, hL2]
  have hcomm' : eLeft.hom ≫ q = (pi n ∣_ U1) ≫ eRight.symm.hom := hcomm.symm
  let e : Arrow.mk (pi n ∣_ U1) ≅ Arrow.mk q := Arrow.isoMk eLeft eRight.symm hcomm'
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsFinite) e).mpr hqfin

/-- **IsFinite π**（两侧限制有限，拼装）。 -/
theorem isFinite_pi (n : Nat) (hn : 0 < n) : IsFinite (pi n) :=
  Mzk1G1FermatPiFiniteAssemblyActual.isFinite_pi_of_chart_restrict n
    (isFinite_pi_of_chart0_restrict n hn) (isFinite_pi_of_chartInf_restrict n hn)

#print axioms isFinite_pi_of_chartInf_restrict
#print axioms isFinite_pi

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiFiniteChartActual