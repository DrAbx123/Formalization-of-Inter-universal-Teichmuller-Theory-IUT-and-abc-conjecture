/- H-T route §8.3: F4 的实际多项式数据接口 + 算术桥（NO INHABITANT inputs）。

Route §8.3 (coord route lines 771-800): F4: h_{E_i}(y) <= r_i h_{O_Y(1)}(y) + C_i
= kappa_i h_{omega_Y}(y) + C_i, 其中 kappa_i = r_i/(n-3), r_i = deg P_i
(P_i 的实际构造 = 直线 x Galois orbit 乘积, route §8.3 NEW 项, 另立项)。

本文件:
* RouteF4PolyData: P_i : Polynomial ℚ + r_i = natDegree + route 字母
  hO1/hOmega/hE/C + route 高度界 + 归一化 r_i hO1 = r_i/(n-3) hOmega (NO INHABITANT);
* RouteF4Statement: route §8.3 的高度形式 (kappa_i 形式);
* routeF4_of_polyData: 由上述数据证 RouteF4Statement（算术桥）;
* natDegree/kappa 代数引理（可证部分）。 -/
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HT83F4PolyActual

/-- Route §8.3 的 per-index 实际多项式数据（NO INHABITANT）:
P_i : Polynomial ℚ（直线 x Galois orbit 乘积的实际构造，route NEW 项）,
r_i := natDegree P_i, 以及 route 字母 h_{O_Y(1)}, h_{omega_Y}, h_{E_i}, C_i 与
* route 高度界 h_{E_i} <= r_i h_{O_Y(1)} + C_i,
* route 归一化 r_i h_{O_Y(1)} = (r_i/(n-3)) h_{omega_Y}。 -/
structure RouteF4PolyData where
  P : ℕ → Polynomial ℚ
  n : ℝ
  n_gt_three : 3 < n
  hO1 : ℕ → ℝ
  hOmega : ℕ → ℝ
  hE : ℕ → ℝ
  C : ℕ → ℝ
  C_nonneg : ∀ i, 0 ≤ C i
  hE_le : ∀ i, hE i ≤ ((P i).natDegree : ℝ) * hO1 i + C i
  hnorm : ∀ i, ((P i).natDegree : ℝ) * hO1 i =
    ((P i).natDegree : ℝ) / (n - 3) * hOmega i

/-- Route §8.3 的 kappa_i := r_i/(n-3)。 -/
def RouteF4PolyData.kappa (D : RouteF4PolyData) (i : ℕ) : ℝ :=
  ((D.P i).natDegree : ℝ) / (D.n - 3)

/-- Route F4 (§8.3): h_{E_i} <= kappa_i h_{omega_Y} + C_i。 -/
def RouteF4Statement (D : RouteF4PolyData) : Prop :=
  ∀ i, D.hE i ≤ D.kappa i * D.hOmega i + D.C i

/-- natDegree 转实数的非负性（可证代数引理）。 -/
theorem natDegree_coe_nonneg (p : Polynomial ℚ) : 0 ≤ ((p.natDegree : ℝ)) :=
  Nat.cast_nonneg _

/-- kappa_i 非负（r_i >= 0, n > 3）。 -/
theorem kappa_nonneg (D : RouteF4PolyData) (i : ℕ) : 0 ≤ D.kappa i := by
  unfold RouteF4PolyData.kappa
  exact div_nonneg (Nat.cast_nonneg _) (by linarith [D.n_gt_three])

/-- kappa 的乘法形式（代数引理）。 -/
theorem kappa_eq_mul_inv (D : RouteF4PolyData) (i : ℕ) :
    D.kappa i = ((D.P i).natDegree : ℝ) * (D.n - 3)⁻¹ := by
  unfold RouteF4PolyData.kappa
  rw [div_eq_mul_inv]

/-- **算术桥**: RouteF4PolyData 的 route 高度界 + 归一化 ⇒ RouteF4Statement
(h_{E_i} <= kappa_i h_{omega_Y} + C_i)。 -/
theorem routeF4_of_polyData (D : RouteF4PolyData) : RouteF4Statement D := by
  intro i
  have h := D.hE_le i
  have hn := D.hnorm i
  unfold RouteF4PolyData.kappa
  linarith

/-- RouteF4Statement 的 kappa 形式与 hO1 形式等价（便于与 F6 接口对接）。 -/
theorem routeF4Statement_iff_O1_form (D : RouteF4PolyData) :
    RouteF4Statement D ↔
      ∀ i, D.hE i ≤ ((D.P i).natDegree : ℝ) * D.hO1 i + D.C i := by
  constructor
  · intro h i
    have hh := h i
    have hn := D.hnorm i
    unfold RouteF4PolyData.kappa at hh
    linarith
  · intro h i
    have hh := h i
    have hn := D.hnorm i
    unfold RouteF4PolyData.kappa
    linarith

/-- F4 的常数非负性与 kappa 非负给出 route 的 O(1) 误差形式中常数可加性
(route §8.3 的常数 C_i 与 F6 的 C4 对齐)。 -/
theorem routeF4_C_nonneg (D : RouteF4PolyData) (i : ℕ) : 0 ≤ D.C i := D.C_nonneg i

#print axioms natDegree_coe_nonneg
#print axioms kappa_nonneg
#print axioms kappa_eq_mul_inv
#print axioms routeF4_of_polyData
#print axioms routeF4Statement_iff_O1_form

end LeanFormal.IUT.XiFPaper.Mzk1HT83F4PolyActual
