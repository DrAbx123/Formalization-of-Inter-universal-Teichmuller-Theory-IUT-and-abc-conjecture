/- G-A §2.3：IsFinite π 的 scheme 层 Zariski-local 装配机械。
   IsFinite 在目标是 Zariski 局部性质：把目标 P¹_glued 用两 chart 开集覆盖，
   若 π 在每个 chart 开集上的限制有限，则 π 有限。
   本文件给出：
   * isFinite_of_two_chart_restrict：通用装配引理（任意 scheme 态射 + 两个覆盖开集）；
   * isFinite_pi_of_chart_restrict：对 π : Y_n ⟶ P¹_glued 的特化
     （cover = localChart0.opensRange ⊔ localChartInf.opensRange = ⊤，emmy 的引理）。
   剩下的 chart 限制有限性（pi ∣_ U0 / U1）等 henry 用 π⁻¹ 等式 + chart 环有限性给出。
   不含 sorry/admit/axiom/PUnit/True/toy。 -/
import tmp.sheaf.xif.paper.Mzk1G1FermatPiActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineChartPreimageActual
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiFiniteAssemblyActual
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineChartPreimageActual

/-- **通用装配**：若 f 在两个开集（其并为 ⊤）上的限制都有限，则 f 有限。 -/
theorem isFinite_of_two_chart_restrict {X Y : Scheme} (f : X ⟶ Y)
    (U0 U1 : Y.Opens) (hU : U0 ⊔ U1 = ⊤)
    (h0 : IsFinite (f ∣_ U0)) (h1 : IsFinite (f ∣_ U1)) :
    IsFinite f := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite)
    (fun b : Bool => cond b U0 U1) ?_ ?_
  · rw [iSup_bool_eq]
    simpa using hU
  · intro b
    cases b
    · simpa using h1
    · simpa using h0

/-- **π 的 IsFinite 装配**：两 chart 开集上的限制都有限 ⟹ π 有限。
    这正是 henry 需要补的两个 chart 限制（用 π⁻¹ 等式 + chart 环有限性）后的总装。 -/
theorem isFinite_pi_of_chart_restrict (n : Nat)
    (h0 : IsFinite (pi n ∣_ localChart0.opensRange))
    (h1 : IsFinite (pi n ∣_ localChartInf.opensRange)) :
    IsFinite (pi n) :=
  isFinite_of_two_chart_restrict (pi n) localChart0.opensRange localChartInf.opensRange
    localChart0_opensRange_sup_localChartInf h0 h1

#print axioms isFinite_of_two_chart_restrict
#print axioms isFinite_pi_of_chart_restrict

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatPiFiniteAssemblyActual
