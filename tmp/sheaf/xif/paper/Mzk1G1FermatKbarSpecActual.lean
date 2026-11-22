/- G1-A (h) M-g per-piece integrality: the three kbar-base-changed charts as integral schemes.
   Four-part reuse: old corpus/GeomIntegral route-new IsDomain results; accepted layer none needed;
   Mathlib: instance [IsDomain R] : IsIntegral (Spec R) (Properties.lean:329), Nonempty (Spec R) from
   Nontrivial, PreirreducibleSpace from IrreducibleSpace; conclusion ADAPTER (instances only). -/
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapKbarActual
import tmp.sheaf.xif.paper.Mzk1G1FermatChartInfKbarActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveToSpecActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveSmoothFinalActual
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatKbarSpecActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothGeomIntegralActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ChartKbarActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartInfKbarActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapKbarActual

abbrev K : Type := FermatK

theorem isIntegral_chartKbarSpec (n : Nat) (hn : 0 < n) :
    IsIntegral (Spec (CommRingCat.of (Chart0Ring n ⊗[ℚ] K))) := by
  haveI := Mzk1G1ChartKbarActual.chartKbar_isDomain n hn
  infer_instance

theorem nonempty_chartKbarSpec (n : Nat) (hn : 0 < n) :
    Nonempty (Spec (CommRingCat.of (Chart0Ring n ⊗[ℚ] K))) := by
  haveI := Mzk1G1ChartKbarActual.chartKbar_isDomain n hn
  infer_instance

theorem preirreducible_chartKbarSpec (n : Nat) (hn : 0 < n) :
    PreirreducibleSpace (Spec (CommRingCat.of (Chart0Ring n ⊗[ℚ] K))) := by
  haveI := isIntegral_chartKbarSpec n hn
  infer_instance

theorem isIntegral_chartInfKbarSpec (n : Nat) (hn : 0 < n) :
    IsIntegral (Spec (CommRingCat.of (R2 n ⊗[ℚ] K))) := by
  haveI := Mzk1G1FermatChartInfKbarActual.chartKbarInf_isDomain n hn
  infer_instance

theorem nonempty_chartInfKbarSpec (n : Nat) (hn : 0 < n) :
    Nonempty (Spec (CommRingCat.of (R2 n ⊗[ℚ] K))) := by
  haveI := Mzk1G1FermatChartInfKbarActual.chartKbarInf_isDomain n hn
  infer_instance

theorem preirreducible_chartInfKbarSpec (n : Nat) (hn : 0 < n) :
    PreirreducibleSpace (Spec (CommRingCat.of (R2 n ⊗[ℚ] K))) := by
  haveI := isIntegral_chartInfKbarSpec n hn
  infer_instance

theorem isIntegral_overlapKbarSpec (n : Nat) (hn : 0 < n) :
    IsIntegral (Spec (CommRingCat.of (Overlap0 n ⊗[ℚ] K))) := by
  haveI := Mzk1G1FermatOverlapKbarActual.overlapKbar_isDomain n hn
  infer_instance

theorem nonempty_overlapKbarSpec (n : Nat) (hn : 0 < n) :
    Nonempty (Spec (CommRingCat.of (Overlap0 n ⊗[ℚ] K))) := by
  haveI := Mzk1G1FermatOverlapKbarActual.overlapKbar_isDomain n hn
  infer_instance

#print axioms isIntegral_chartKbarSpec
/-- `Spec k̄ ⟶ Spec ℚ`。 -/
noncomputable def gK : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ K))

/-- chart-0 结构态射沿 Spec k̄ 的 base change ≅ Spec (Chart0Ring n ⊗[ℚ] k̄)。 -/
noncomputable def chart0BaseChangeIso (n : Nat) :
    pullback (Mzk1G1FermatCurveToSpecActual.fermatChart0ToSpec n) (gK) ≅
      Spec (CommRingCat.of (Chart0Ring n ⊗[ℚ] K)) :=
  pullbackSpecIso ℚ (Chart0Ring n) K

/-- chart-∞ 结构态射沿 Spec k̄ 的 base change ≅ Spec (R2 n ⊗[ℚ] k̄)。 -/
noncomputable def chartInfBaseChangeIso (n : Nat) :
    pullback (Mzk1G1FermatCurveToSpecActual.fermatChartInfToSpec n) (gK) ≅
      Spec (CommRingCat.of (R2 n ⊗[ℚ] K)) :=
  pullbackSpecIso ℚ (R2 n) K

/-- chart-0 的 base change 是整概型。 -/
theorem isIntegral_pullback_chart0ToSpec (n : Nat) (hn : 0 < n) :
    IsIntegral (pullback (Mzk1G1FermatCurveToSpecActual.fermatChart0ToSpec n) (gK)) := by
  haveI h := isIntegral_chartKbarSpec n hn
  exact IsIntegral.of_isIso (chart0BaseChangeIso n).inv

/-- chart-∞ 的 base change 是整概型。 -/
theorem isIntegral_pullback_chartInfToSpec (n : Nat) (hn : 0 < n) :
    IsIntegral (pullback (Mzk1G1FermatCurveToSpecActual.fermatChartInfToSpec n) (gK)) := by
  haveI h := isIntegral_chartInfKbarSpec n hn
  exact IsIntegral.of_isIso (chartInfBaseChangeIso n).inv

#print axioms chart0BaseChangeIso
/-- 两个 base-change chart preimage 覆盖 Ybar := pullback (fermatCurveToSpec n) gK。 -/
theorem kbarCover_iSup_eq_top (n : Nat) :
    (⨆ b : Bool, (pullback.fst (Mzk1G1FermatCurveToSpecActual.fermatCurveToSpec n) gK) ⁻¹ᵁ
      Mzk1G1FermatCurveSmoothFinalActual.chartOpenFamily n b) = ⊤ :=
  Scheme.Hom.iSup_preimage_eq_top
    (f := pullback.fst (Mzk1G1FermatCurveToSpecActual.fermatCurveToSpec n) gK)
    (U := Mzk1G1FermatCurveSmoothFinalActual.chartOpenFamily n)
    (Mzk1G1FermatCurveSmoothFinalActual.chartOpenFamily_iSup_eq_top n)

#print axioms kbarCover_iSup_eq_top

#print axioms isIntegral_pullback_chart0ToSpec
#print axioms isIntegral_pullback_chartInfToSpec

#print axioms isIntegral_chartInfKbarSpec
#print axioms isIntegral_overlapKbarSpec

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatKbarSpecActual
