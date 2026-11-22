/- G1-A：Fermat 曲线作为 P² 的实际闭子概形（复用已 accepted donor），
   并证明"标准图 D(X)∪D(Z) 覆盖 Fermat 曲线"（X=Z=0 ⇒ Y=0）。
   donor：`Mzk1G1FermatProjectiveScheme4Actual`（actual Proj plane + Fermat 齐次多项式 +
   closed subset + structure map）与 `Mzk1G1FermatProjClosedSubscheme4Actual`
   （vanishingIdeal.subscheme/subschemeι 的 closed immersion + proper，standard three）。
   不含 sorry/admit/axiom/PUnit/True/toy。 -/
import tmp.sheaf.xif.paper.Mzk1G1FermatProjectiveScheme4Actual
import tmp.sheaf.xif.paper.Mzk1G1FermatProjClosedSubscheme4Actual
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveClosed2Actual
open MvPolynomial AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjectiveScheme4Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatProjClosedSubscheme4Actual

/-- 环境射影平面 P² = Proj ℚ[X₀,X₁,X₂]。 -/
abbrev P2 : Scheme := fermatProjectivePlane

/-- 实际 Fermat 曲线 Y_n ⊆ P²（Fermat 齐次理想的 closed subscheme）。 -/
abbrev FermatCurve (n : Nat) : Scheme := fermatCurveScheme n

/-- 闭浸入 Y_n ⟶ P²。 -/
abbrev fermatCurveι (n : Nat) : FermatCurve n ⟶ P2 := fermatCurveImmersion n

theorem fermatCurve_closedImmersion (n : Nat) : IsClosedImmersion (fermatCurveι n) :=
  fermatCurveImmersion_isClosedImmersion n

theorem fermatCurve_proper (n : Nat) : IsProper (fermatCurveι n) :=
  fermatCurveImmersion_isProper n

/-! ### X=Z=0 ⇒ Y=0：两张标准图覆盖 Fermat 曲线 -/

/-- 在 ℚ[X₀,X₁,X₂] 中的恒等式：`X₁^n = X₂^n - X₀^n + F`。 -/
theorem fermatPolynomial_relation (n : Nat) :
    (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ) ^ n
      = (MvPolynomial.X 2) ^ n - (MvPolynomial.X 0) ^ n + fermatPolynomial n := by
  unfold fermatPolynomial
  ring

/-- 关键覆盖事实：`X₀=0, X₂=0, F=0` 迫使 `X₁^n=0`；
    即 `X₁^n ∈ (F, X₀, X₂)`，故曲线点不能同时避开 `D(X₀)` 与 `D(X₂)`：
    `D(X₀) ∪ D(X₂)` 覆盖 Fermat 曲线。 -/
theorem fermat_X1_pow_mem_span (n : Nat) (hn : 0 < n) :
    (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ) ^ n ∈
      Ideal.span ({fermatPolynomial n, MvPolynomial.X 0, MvPolynomial.X 2} :
        Set (MvPolynomial (Fin 3) ℚ)) := by
  have hX0 : (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) ∈
      Ideal.span ({fermatPolynomial n, MvPolynomial.X 0, MvPolynomial.X 2} :
        Set (MvPolynomial (Fin 3) ℚ)) :=
    Ideal.subset_span (by simp)
  have hX2 : (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℚ) ∈
      Ideal.span ({fermatPolynomial n, MvPolynomial.X 0, MvPolynomial.X 2} :
        Set (MvPolynomial (Fin 3) ℚ)) :=
    Ideal.subset_span (by simp)
  have hF : fermatPolynomial n ∈
      Ideal.span ({fermatPolynomial n, MvPolynomial.X 0, MvPolynomial.X 2} :
        Set (MvPolynomial (Fin 3) ℚ)) :=
    Ideal.subset_span (by simp)
  rw [fermatPolynomial_relation]
  exact Ideal.add_mem (I := Ideal.span {fermatPolynomial n, MvPolynomial.X 0, MvPolynomial.X 2})
    (Ideal.sub_mem (I := Ideal.span {fermatPolynomial n, MvPolynomial.X 0, MvPolynomial.X 2})
      (Ideal.pow_mem_of_mem (I := Ideal.span {fermatPolynomial n, MvPolynomial.X 0,
        MvPolynomial.X 2}) hX2 n hn)
      (Ideal.pow_mem_of_mem (I := Ideal.span {fermatPolynomial n, MvPolynomial.X 0,
        MvPolynomial.X 2}) hX0 n hn))
    hF

/-- 素理想版本：若齐次素理想包含 `F` 与 `X₀, X₂`，则必含 `X₁`。
    因此在 `D(X₀) ∪ D(X₂)` 之外没有 Fermat 曲线的点（曲线的点理想是素理想）。 -/
theorem fermat_X1_mem_of_prime (n : Nat) (hn : 0 < n) (p : Ideal (MvPolynomial (Fin 3) ℚ))
    (hp : p.IsPrime) (hF : fermatPolynomial n ∈ p)
    (h0 : (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) ∈ p)
    (h2 : (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℚ) ∈ p) :
    (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ) ∈ p := by
  have hpow : (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ) ^ n ∈ p := by
    rw [fermatPolynomial_relation]
    exact p.add_mem (p.sub_mem (Ideal.pow_mem_of_mem p h2 n hn)
      (Ideal.pow_mem_of_mem p h0 n hn)) hF
  exact hp.mem_of_pow_mem n hpow

#print axioms fermatCurve_closedImmersion
#print axioms fermatCurve_proper
#print axioms fermatPolynomial_relation
#print axioms fermat_X1_pow_mem_span
#print axioms fermat_X1_mem_of_prime

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveClosed2Actual