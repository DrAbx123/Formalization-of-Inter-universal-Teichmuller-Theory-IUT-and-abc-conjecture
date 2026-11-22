/- G-A §2.3：Y_n 的 canonical 结构态射 Y_n ⟶ Spec ℚ（由两 chart 的 base 态射粘合）
   以及 IsProper(Y_n) 的装配。
   关键工具（alan, Mzk1P1ProperActual）：
   * subsingleton_hom_spec_rat (X : Scheme) : Subsingleton (X ⟶ Spec ℚ)；
   * p1GluedToBase : projectiveLineGlued ⟶ Spec ℚ。
   Y_n 结构态射：两 chart 的 fermatChartToSpec/fermatChart2ToSpec 经 glueMorphisms 粘，
   相容性由 subsingleton 直接得到；proper 装配用 finite⟹proper 与 proper 复合。
   不含 sorry/admit/axiom/PUnit/True/toy。 -/
import tmp.sheaf.xif.paper.Mzk1G1FermatPiActual
import tmp.sheaf.xif.paper.Mzk1P1ProperActual
import tmp.sheaf.xif.paper.Mzk1P1ProperFinalActual
import tmp.sheaf.xif.paper.Mzk1G1FermatPiRestrictFiniteActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveToSpecActual
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiProperActual
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1P1ProperActual
open LeanFormal.IUT.XiFPaper.Mzk1P1ProperFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveToSpecActual

/-- **π 有限 ⟹ π proper**（Mathlib 的 IsFinite ⟹ IsProper 实例）。 -/
theorem fermatPi_isProper (n : Nat) (hfin : IsFinite (pi n)) : IsProper (pi n) := by
  haveI := hfin
  exact inferInstance

/-- 第一个 chart 的结构态射 Spec R n ⟶ Spec ℚ。 -/
noncomputable def fermatChartBase0 (n : Nat) :
    fermatChart0Scheme n ⟶ Spec (CommRingCat.of ℚ) :=
  fermatChartToSpec n

/-- 第二个 chart 的结构态射 Spec R2 n ⟶ Spec ℚ。 -/
noncomputable def fermatChartBaseInf (n : Nat) :
    fermatChartInfScheme n ⟶ Spec (CommRingCat.of ℚ) :=
  fermatChart2ToSpec n

/-- **Y_n 的 canonical 结构态射** Y_n ⟶ Spec ℚ：两 chart 的 base 态射粘合。 -/
noncomputable def fermatCurveToBase (n : Nat) :
    fermatCurveScheme n ⟶ Spec (CommRingCat.of ℚ) :=
  (fermatTwoChartGlueData n).openCover.glueMorphisms
    (fun i =>
      match i with
      | ULift.up false => fermatChartBase0 n
      | ULift.up true => fermatChartBaseInf n)
    (fun i j => Subsingleton.elim _ _)

/-- 在第一个 chart 上，结构态射就是该 chart 的 base 态射。 -/
theorem fermatChart0ToCurve_fermatCurveToBase (n : Nat) :
    fermatChart0ToCurve n ≫ fermatCurveToBase n = fermatChartBase0 n :=
  (fermatTwoChartGlueData n).openCover.ι_glueMorphisms _ _ (ULift.up false)

/-- 在第二个 chart 上，结构态射就是该 chart 的 base 态射。 -/
theorem fermatChartInfToCurve_fermatCurveToBase (n : Nat) :
    fermatChartInfToCurve n ≫ fermatCurveToBase n = fermatChartBaseInf n :=
  (fermatTwoChartGlueData n).openCover.ι_glueMorphisms _ _ (ULift.up true)

/-- 到 Spec ℚ 的态射唯一，故 Y_n 的结构态射 = π ≫ P¹ 的结构态射。 -/
theorem fermatCurveToBase_eq_pi_comp (n : Nat) :
    fermatCurveToBase n = pi n ≫ p1GluedToBase :=
  Subsingleton.elim _ _

/-- **IsProper(Y_n) 装配（条件式）**：π 有限 + P¹_glued proper ⟹ Y_n ⟶ Spec ℚ proper。 -/
theorem fermatCurveToBase_isProper (n : Nat)
    (hfin : IsFinite (pi n)) (hP1 : IsProper p1GluedToBase) :
    IsProper (fermatCurveToBase n) := by
  rw [fermatCurveToBase_eq_pi_comp]
  haveI := hfin
  haveI := hP1
  exact inferInstance

/-- 到 Spec ℚ 的态射唯一：本文件的结构态射 = henry 的 `fermatCurveToSpec`（避免双定义）。 -/
theorem fermatCurveToBase_eq_fermatCurveToSpec (n : Nat) :
    fermatCurveToBase n = Mzk1G1FermatCurveToSpecActual.fermatCurveToSpec n :=
  Subsingleton.elim _ _

/-- 用 henry 的 `fermatCurveToSpec` 表述的 IsProper 装配（条件同 `fermatCurveToBase_isProper`）。 -/
theorem fermatCurveToSpec_isProper (n : Nat)
    (hfin : IsFinite (pi n)) (hP1 : IsProper p1GluedToBase) :
    IsProper (Mzk1G1FermatCurveToSpecActual.fermatCurveToSpec n) := by
  rw [← fermatCurveToBase_eq_fermatCurveToSpec]
  exact fermatCurveToBase_isProper n hfin hP1

#print axioms subsingleton_hom_spec_rat
#print axioms fermatChart0ToCurve_fermatCurveToBase
#print axioms fermatChartInfToCurve_fermatCurveToBase
#print axioms fermatCurveToBase_eq_pi_comp
#print axioms fermatCurveToBase_eq_fermatCurveToSpec
#print axioms fermatCurveToSpec_isProper
/-- **IsProper(Y_n)（只差 IsFinite π）**：消费 alan 已交付的 `IsProper p1GluedToBase`，
    `fermatCurveToSpec_isProper_cond (hfin : IsFinite (pi n)) : IsProper (fermatCurveToSpec n)`。 -/
theorem fermatCurveToSpec_isProper_cond (n : Nat) (hfin : IsFinite (pi n)) :
    IsProper (Mzk1G1FermatCurveToSpecActual.fermatCurveToSpec n) := by
  exact fermatCurveToSpec_isProper n hfin (Mzk1P1ProperFinalActual.p1GluedToBase_isProper)

#print axioms fermatCurveToSpec_isProper_cond
/-- **★ IsProper(Y_n) 闭合（G-A proper 出口）**：henry 的 `isFinite_pi`（17:16:42 三公理）
    + alan 的 `p1GluedToBase_isProper`（15:53:12 三公理）⇒ Y_n → Spec ℚ 是 proper。 -/
theorem fermatCurveToSpec_isProper_final (n : Nat) (hn : 0 < n) :
    IsProper (Mzk1G1FermatCurveToSpecActual.fermatCurveToSpec n) := by
  exact fermatCurveToSpec_isProper_cond n
    (Mzk1G1FermatPiRestrictFiniteActual.isFinite_pi n hn)

#print axioms fermatCurveToSpec_isProper_final


#print axioms fermatCurveToBase_isProper

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiProperActual