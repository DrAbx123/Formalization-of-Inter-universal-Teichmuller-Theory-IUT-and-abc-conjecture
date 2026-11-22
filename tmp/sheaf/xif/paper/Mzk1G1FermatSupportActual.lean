/- G1-A 实际几何支撑（geom lane）：
   * 两张仿射图的真实环 A₀/A∞ 及其 rank n²（来自 `Mzk1G1FermatFiniteDegree2Actual`）；
   * 图态射 `Spec A₀ → Spec ℚ[λ]`、`Spec A∞ → Spec ℚ[t]` 的实际 finite/proper
     （由 Module.Finite + `IsFinite.SpecMap_iff` + finite ⇒ proper）；
   * Fermat 曲线闭子概形的 closed immersion/proper（来自 `Mzk1G1FermatCurveClosed2Actual`）。
   不含 sorry/admit/axiom/PUnit/True/toy。 -/
import tmp.sheaf.xif.paper.Mzk1G1FermatFiniteDegree2Actual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveClosed2Actual
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatSupportActual
open AlgebraicGeometry CategoryTheory
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatFiniteDegree2Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveClosed2Actual

/-! ### λ 图：Spec A₀ → Spec ℚ[λ] finite/proper -/

/-- λ 图到基图的实际结构态射 `Spec A₀ ⟶ Spec ℚ[λ]`。 -/
noncomputable def fermatChart0Map (n : Nat) :
    Spec (CommRingCat.of (fermatA0Ring n)) ⟶ Spec (CommRingCat.of (Polynomial ℚ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (fermatA0Ring n)))

/-- λ 图结构态射是有限态射（真实 Module.Finite）。 -/
theorem fermatChart0Map_isFinite (n : Nat) (hn : 0 < n) : IsFinite (fermatChart0Map n) := by
  rw [fermatChart0Map, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr (fermatA0Ring_finite n hn)

/-- λ 图结构态射是 proper（有限 ⇒ proper）。这是 π 在 λ 图上的限制。 -/
theorem fermatChart0Map_isProper (n : Nat) (hn : 0 < n) : IsProper (fermatChart0Map n) :=
  haveI := fermatChart0Map_isFinite n hn
  inferInstance

/-! ### ∞ 图：Spec A∞ → Spec ℚ[t] finite/proper -/

/-- ∞ 图到基图的实际结构态射 `Spec A∞ ⟶ Spec ℚ[t]`。 -/
noncomputable def fermatChartInfMap (n : Nat) :
    Spec (CommRingCat.of (fermatAInfRing n)) ⟶ Spec (CommRingCat.of (Polynomial ℚ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℚ) (fermatAInfRing n)))

theorem fermatChartInfMap_isFinite (n : Nat) (hn : 0 < n) : IsFinite (fermatChartInfMap n) := by
  rw [fermatChartInfMap, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr (fermatAInfRing_finite n hn)

theorem fermatChartInfMap_isProper (n : Nat) (hn : 0 < n) : IsProper (fermatChartInfMap n) :=
  haveI := fermatChartInfMap_isFinite n hn
  inferInstance

/-! ### 曲线闭子概形 -/

/-- 实际 Fermat 曲线到 P² 的闭浸入是 proper。 -/
theorem fermatCurve_proper_support (n : Nat) : IsProper (fermatCurveι n) :=
  fermatCurve_proper n

/-- 实际 Fermat 曲线到 P² 的闭浸入。 -/
theorem fermatCurve_closed_support (n : Nat) : IsClosedImmersion (fermatCurveι n) :=
  fermatCurve_closedImmersion n

#print axioms fermatChart0Map_isFinite
#print axioms fermatChart0Map_isProper
#print axioms fermatChartInfMap_isFinite
#print axioms fermatChartInfMap_isProper
#print axioms fermatCurve_proper_support

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatSupportActual
