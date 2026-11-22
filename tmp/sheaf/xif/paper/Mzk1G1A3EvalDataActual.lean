/- A3 / F2.1: interface for the evaluation data used by the route §4.1 B2 construction.

  ROUTE-CONFORMING CONTENT: for a finite set of closed points `D` (the effective reduced divisor
  `D_T`) of degree at least `deg K_Y + 3`, Riemann-Roch + Serre duality give, for every closed
  point `x ∈ D`, a nonzero evaluation map `H0(O(D)) → residue(x)`; consequently `H0(O(D))` is
  not covered by the finitely many hyperplanes `{s : s(x) = 0}`, so there is a section `s1`
  which is nonzero at every `x ∈ D` (this is exactly `Mzk1G1A3EvaluationActual.
  exists_forall_apply_ne_zero`).

  THIS FILE packages the data side: the structure `A3EvalData` holds the finite set of points,
  the section space, the residue fields and the (hypothesised, NONZERO) evaluation maps, and
  proves the existence of the avoiding section `s1`. The cohomological hypotheses which are
  supposed to PRODUCE the nonzero evaluations (`H^1(O(D - x)) = 0` via Serre duality,
  `ConstantsAreBase`, `ResidueTheorem`) are listed explicitly in the docstring and in
  `coord/A3-EVALDATA-MAP.md`; they are registered obligations, NOT asserted here.

  Header RECON: `Mzk1G1A3EvaluationActual.exists_forall_apply_ne_zero` (DONE 11:04:34) is the
  linear-algebra core and is reused directly; no duplicate. The tree's `serrePairing`
  (`Def_AlgebraicCurve_SerrePairing`) is only for divisor 0; the general-D duality needs
  `AdelicIndex.residuePairing (W D)` + `WeilDuality` + `ResidueTheorem`, see the map doc.
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1A3EvaluationActual
import tmp.sheaf.xif.paper.Mzk1G1FermatAffineChartActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3EvalDataActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3EvaluationActual

variable (n : Nat)

/-- **F2.1 的 evaluation 数据接口**（route §4.1：`H0(O(D_T)) → residue(x)` 非零）。

    字段全部显式；其中 `evalAt` 的**非零性** `hne` 是 route L257 的结论，其生产所需的
    上同调假设见文件头/`coord/A3-EVALDATA-MAP.md`（登记义务，不在本结构中断言其可证性）。 -/
structure A3EvalData where
  /-- 有限闭点集（chart-0 上的素点，代表 reduced `D_T` 的支撑）。 -/
  D : Finset (PrimeSpectrum (R n))
  /-- 除子 `D_T` 的次数与 canonical 除子次数（抽象记账，单位 ℤ）。 -/
  degDT : ℤ
  degK : ℤ
  /-- route §4.1 的次数条件。 -/
  hdeg : degK + 3 ≤ degDT
  /-- 截面空间 `H⁰(O(D_T))`。 -/
  H0 : Type
  [H0_add : AddCommGroup H0]
  [H0_mod : Module ℚ H0]
  /-- 每个闭点的 residue field（可为高次数域扩张）。 -/
  κ : PrimeSpectrum (R n) → Type
  [κ_field : ∀ x, Field (κ x)]
  [κ_alg : ∀ x, Algebra ℚ (κ x)]
  /-- 闭点处的 evaluation（线性）。 -/
  evalAt : ∀ x, H0 →ₗ[ℚ] κ x
  /-- **route L257 的结论**：每个 `x ∈ D` 处 evaluation 非零。 -/
  hne : ∀ x ∈ D, evalAt x ≠ 0

attribute [instance] A3EvalData.H0_add A3EvalData.H0_mod A3EvalData.κ_field A3EvalData.κ_alg

/-- **由 evaluation 数据得到避开 `D` 的截面 `s1`**：`∃ s1 : H0, ∀ x ∈ D, evalAt x s1 ≠ 0`。
    （route L261 的「有限多个真子空间不能覆盖」，复用 `exists_forall_apply_ne_zero`。） -/
theorem A3EvalData.exists_avoiding (E : A3EvalData n) :
    ∃ s1 : E.H0, ∀ x ∈ E.D, E.evalAt x s1 ≠ 0 :=
  exists_forall_apply_ne_zero E.D E.κ E.evalAt E.hne

#print axioms A3EvalData.exists_avoiding

end LeanFormal.IUT.XiFPaper.Mzk1G1A3EvalDataActual
