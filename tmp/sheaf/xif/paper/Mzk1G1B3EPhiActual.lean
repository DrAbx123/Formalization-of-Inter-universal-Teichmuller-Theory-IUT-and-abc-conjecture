/- B3 S4 prerequisite (route L319-334): the reduced preimage E_phi = (phi^{-1}{0,1,infty})_red.
   This file (owner=grace) provides the scheme-layer point set and its decomposition into
   the three fibres; the divisor-layer Cech unit and the bridge to the scheme layer are
   documented in the docstring below and will be added once the refined cover
   (Mzk1G1B3RefinedCoverActual, S7) lands. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiB1Actual
import tmp.sheaf.xif.paper.Mzk1G1PhiFiberFiniteActual
import tmp.sheaf.xif.paper.Mzk1G1B3CoverActual
import tmp.sheaf.xif.paper.Mzk1G1A5LineBundleIsoActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineBoundaryActual
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
open AlgebraicGeometry CategoryTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B3EPhiActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual

/-- **E_φ 的 scheme 层**（route L330）：φ = ψ ≫ h 下 `{0,1,∞}` 的拉回点集
    （1 维曲线上有限个闭点，reduced 结构唯一）。 -/
noncomputable def ePhiSet (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    Set (fermatCurveScheme n) :=
  (phi n T h hh).base ⁻¹' boundarySetGlued

/-- E_φ 分解成 `φ^{-1}{0}`、`φ^{-1}{1}`、`φ^{-1}{∞}` 三个纤维的并。 -/
theorem ePhiSet_eq_union (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    ePhiSet n T h hh =
      ((phi n T h hh).base ⁻¹' p1Zero ∪ (phi n T h hh).base ⁻¹' p1One) ∪
        (phi n T h hh).base ⁻¹' p1Infinity := by
  unfold ePhiSet
  rw [LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual.boundarySetGlued_eq, Set.preimage_union,
    Set.preimage_union]

/-- E_φ 是 `φ` 下 `{0,1,∞}` 的拉回（divisor 层支撑集与 scheme 层点集一致）。 -/
theorem ePhiSet_support_eq (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    ePhiSet n T h hh = {x | (phi n T h hh).base x ∈ boundarySetGlued} := rfl

#print axioms ePhiSet_eq_union
/-! ## ω_Y 侧的 Čech 单元

    A5 (`Mzk1G1A5LineBundleIsoActual.omegaYEUnit`) 的过渡单元落在 `O0 n = Overlap0 n`，
    而我们的对称 cover `fermatCover n` 的共同 overlap 也取 `Overlap0 n`，所以直接可用。
    （route B3 的 ω_Y 侧：A5 是 π = fermatCurveToSpec 版本，这里只借用 ω_Y 的过渡单元。） -/

/-- ω_Y 在对称两图 cover 上的 Čech 线丛（用 A5 的 `omegaYEUnit`）。 -/
noncomputable def omegaLineBundle (n : Nat) :
    TwoChartCech.Sections (Mzk1G1B3CoverActual.fermatCover n) :=
  (Mzk1G1B3CoverActual.fermatCover n).lineBundle
    (LeanFormal.IUT.XiFPaper.Mzk1G1A5LineBundleIsoActual.omegaYEUnit n)

/-- ω_Y 线丛的 r0 就是 chart0 的局部化。 -/
theorem omegaLineBundle_r0_apply (n : Nat) (p : R n) :
    (omegaLineBundle n).r0 p =
      (Mzk1G1B3CoverActual.fermatCover n).ρ0 p := rfl

#print axioms omegaLineBundle
/-! ## E_φ 的有限性（reduced 结构层的前提）

    route L330: `E_φ = (φ^{-1}{0,1,∞})_red`。其支撑集 `ePhiSet` 的有限性由 ⑥ 的
    `phi_boundaryPreimage_finite`（22:42:11，三公理）直接给出；1 维曲线上有限闭点集的
    reduced 闭子概型结构唯一（下一步与 divisor 层对接）。 -/

/-- **E_φ 有限**：三条纤维的并有限（route L330 的 reduced 结构层前提）。 -/
theorem ePhiSet_finite (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0)
    (hn : 0 < n) (hT : T.Nonempty) (h0 : (0 : ℚ) ∉ T) (hdeg : 0 < h.natDegree) :
    (ePhiSet n T h hh).Finite :=
  LeanFormal.IUT.XiFPaper.Mzk1G1PhiFiberFiniteActual.phi_boundaryPreimage_finite
    n T h hh hn hT h0 hdeg

#print axioms ePhiSet_finite

#print axioms omegaLineBundle_r0_apply

#print axioms ePhiSet_support_eq

end LeanFormal.IUT.XiFPaper.Mzk1G1B3EPhiActual