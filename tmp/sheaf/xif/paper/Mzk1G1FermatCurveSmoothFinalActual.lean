/- G1-A route 2.4 exit: Y_n -> Spec Q is smooth of relative dimension 1.
   Reuse check: Mathlib IsZariskiLocalAtSource.iff_of_iSup_eq_top + IsOpenImmersion.isoOfRangeEq
   (+_hom_fac/_inv_fac) + Arrow.isoMk + MorphismProperty.arrow_mk_iso_iff; no old-corpus donor
   (only usage patterns); Lead's Mzk1G1ChartCoverActual provides the Bool-indexed two-chart open
   cover lemma, which we reprove here against the canonical CurveActual API. Conclusion: ADAPTER. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveToSpecActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveSmoothActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveSmooth2Actual
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveSmoothFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveToSpecActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveSmoothActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveSmooth2Actual

/-- The two-chart Zariski cover of the glued Fermat curve (Bool-indexed, if-form). -/
def chartOpenFamily (n : Nat) : Bool → (fermatCurveScheme n).Opens :=
  fun b => if b then (fermatChartInfToCurve n).opensRange
    else (fermatChart0ToCurve n).opensRange

theorem chartOpenFamily_false (n : Nat) :
    chartOpenFamily n false = (fermatChart0ToCurve n).opensRange := rfl

theorem chartOpenFamily_true (n : Nat) :
    chartOpenFamily n true = (fermatChartInfToCurve n).opensRange := rfl

theorem chartOpenFamily_iSup_eq_top (n : Nat) :
    iSup (chartOpenFamily n) = ⊤ := by
  ext x
  change x ∈ iSup (chartOpenFamily n) ↔ x ∈ (⊤ : (fermatCurveScheme n).Opens)
  rw [TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨i, hi⟩
    trivial
  · intro _
    obtain ⟨i, y, hy⟩ := (fermatTwoChartGlueData n).ι_jointly_surjective x
    obtain ⟨b⟩ := i
    cases b
    · exact ⟨false, by rw [chartOpenFamily_false]; exact ⟨y, hy⟩⟩
    · exact ⟨true, by rw [chartOpenFamily_true]; exact ⟨y, hy⟩⟩

#print axioms chartOpenFamily_iSup_eq_top
/-- chart-0 限制：把 `(chart0 image).ι ≫ f` 与 `chart0ToCurve ≫ f` 通过 arrow iso 对齐。 -/
theorem smoothOfRelativeDimension_of_chart0_restrict (n : Nat) (hn : 0 < n) :
    SmoothOfRelativeDimension 1
      (((fermatChart0ToCurve n).opensRange).ι ≫ fermatCurveToSpec n) := by
  have hrange : Set.range (fermatChart0ToCurve n) =
      Set.range ((fermatChart0ToCurve n).opensRange).ι := by
    rw [← Scheme.Hom.coe_opensRange (f := fermatChart0ToCurve n),
      ← Scheme.Hom.coe_opensRange (f := ((fermatChart0ToCurve n).opensRange).ι),
      Scheme.Opens.opensRange_ι]
  let eW : fermatChart0Scheme n ≅ ((fermatChart0ToCurve n).opensRange : Scheme) :=
    IsOpenImmersion.isoOfRangeEq (fermatChart0ToCurve n)
      ((fermatChart0ToCurve n).opensRange).ι hrange
  have hcomm : eW.inv ≫ (fermatChart0ToCurve n ≫ fermatCurveToSpec n)
      = (((fermatChart0ToCurve n).opensRange).ι ≫ fermatCurveToSpec n)
          ≫ 𝟙 (Spec (CommRingCat.of ℚ)) := by
    rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac, Category.comp_id]
  have hchart : SmoothOfRelativeDimension 1
      (fermatChart0ToCurve n ≫ fermatCurveToSpec n) := by
    rw [fermatCurveToSpec_ι0 n, fermatChart0ToSpec]
    exact chartSpec_smoothOfRelativeDimension n hn
  exact (MorphismProperty.arrow_mk_iso_iff (P := @SmoothOfRelativeDimension 1)
    (Arrow.isoMk eW.symm (Iso.refl _) hcomm)).mpr hchart

/-- chart-∞ 限制（镜像）。 -/
theorem smoothOfRelativeDimension_of_chartInf_restrict (n : Nat) (hn : 0 < n) :
    SmoothOfRelativeDimension 1
      (((fermatChartInfToCurve n).opensRange).ι ≫ fermatCurveToSpec n) := by
  have hrange : Set.range (fermatChartInfToCurve n) =
      Set.range ((fermatChartInfToCurve n).opensRange).ι := by
    rw [← Scheme.Hom.coe_opensRange (f := fermatChartInfToCurve n),
      ← Scheme.Hom.coe_opensRange (f := ((fermatChartInfToCurve n).opensRange).ι),
      Scheme.Opens.opensRange_ι]
  let eW : fermatChartInfScheme n ≅ ((fermatChartInfToCurve n).opensRange : Scheme) :=
    IsOpenImmersion.isoOfRangeEq (fermatChartInfToCurve n)
      ((fermatChartInfToCurve n).opensRange).ι hrange
  have hcomm : eW.inv ≫ (fermatChartInfToCurve n ≫ fermatCurveToSpec n)
      = (((fermatChartInfToCurve n).opensRange).ι ≫ fermatCurveToSpec n)
          ≫ 𝟙 (Spec (CommRingCat.of ℚ)) := by
    rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac, Category.comp_id]
  have hchart : SmoothOfRelativeDimension 1
      (fermatChartInfToCurve n ≫ fermatCurveToSpec n) := by
    rw [fermatCurveToSpec_ι1 n, fermatChartInfToSpec]
    exact chartSpec2_smoothOfRelativeDimension n hn
  exact (MorphismProperty.arrow_mk_iso_iff (P := @SmoothOfRelativeDimension 1)
    (Arrow.isoMk eW.symm (Iso.refl _) hcomm)).mpr hchart

/-- **路线 §2.4 G-A smooth 出口**：`Y_n ⟶ Spec ℚ` 是 rel dim 1 smooth。 -/
theorem fermatCurveToSpec_smoothOfRelativeDimension (n : Nat) (hn : 0 < n) :
    SmoothOfRelativeDimension 1 (fermatCurveToSpec n) := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (f := fermatCurveToSpec n) (U := chartOpenFamily n) (chartOpenFamily_iSup_eq_top n)]
  intro i
  cases i
  · rw [chartOpenFamily_false]
    exact smoothOfRelativeDimension_of_chart0_restrict n hn
  · rw [chartOpenFamily_true]
    exact smoothOfRelativeDimension_of_chartInf_restrict n hn

#print axioms smoothOfRelativeDimension_of_chart0_restrict
#print axioms smoothOfRelativeDimension_of_chartInf_restrict
#print axioms fermatCurveToSpec_smoothOfRelativeDimension


end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveSmoothFinalActual