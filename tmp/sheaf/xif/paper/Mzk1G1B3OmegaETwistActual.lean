/- B3 E_phi twist layer, object part (grace): the local equations of E_phi = (phi^{-1}{0,1,infty})_red
   on the two charts, route L334 (explicit Cech units, per-point dt/du).
   chart 0: coordinate u = h(a), a := psiChart0Coord; 0/1 fibres are u = 0, u = 1; the infinity
   fibre does not meet the chart-0 image of a polynomial h.
   chart infinity: coordinate b := psiChartInfCoord; the infinity fibre is b = 0 and the 0/1 fibres
   are hRev(b) = 0, hRev(b) - b^d = 0 (h(1/b) = hRev(b)/b^d), d = natDegree h.
   No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1B3EPhiActual
import tmp.sheaf.xif.paper.Mzk1G1B3RefinedCoverActual
import tmp.sheaf.xif.paper.Mzk1G1B3PullbackO1YActual
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B3OmegaETwistActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B3RefinedCoverActual

/-- chart-0 的 φ 坐标 `h(a)`（a := psiChart0Coord）。 -/
noncomputable def phiCoord0 (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) : R n :=
  Polynomial.eval₂ (algebraMap ℚ (R n)) (psiChart0Coord n T) h

/-- chart-0 上 `E_φ` 的局部方程：0 与 1 两根纤维（∞ 纤维不与 chart-0 相交）。 -/
noncomputable def ePhiTwistEq0 (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) : R n :=
  phiCoord0 n T h * (phiCoord0 n T h - 1)

/-- chart-∞ 的 φ 坐标 `h(1/b)` 的清分母形式 `hRev(b)`（b := psiChartInfCoord，ψ 的 t-坐标）。 -/
noncomputable def phiCoordInfNumer (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) :
    refinedChart1 n T :=
  Polynomial.eval₂ (algebraMap ℚ (refinedChart1 n T)) (psiChartInfCoord n T)
    (Polynomial.reverse h)

/-- chart-∞ 上 `E_φ` 的局部方程：∞ 纤维 `b = 0` 与 0/1 纤维。 -/
noncomputable def ePhiTwistEq1 (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) :
    refinedChart1 n T :=
  (psiChartInfCoord n T : refinedChart1 n T) * phiCoordInfNumer n T h *
    (phiCoordInfNumer n T h - (psiChartInfCoord n T : refinedChart1 n T) ^ h.natDegree)

#print axioms phiCoord0
#print axioms ePhiTwistEq0
#print axioms phiCoordInfNumer
#print axioms ePhiTwistEq1


/-! ## ω_Y(E_φ) 侧的 Čech 单元（B3 第二式的 ω 侧；E_φ twist 的 unit 比较用）

    S9 (`Mzk1G1B3PullbackO1YActual`) 的 h-overlap cover 以 `Away(a·hA)` 为单元层，A5 的 ω_Y 单元
    （`O0 n = Overlap0 n` 上的 `omegaYEUnit`）可直接沿 `algebraMap (Overlap0 n) (hOverlap n T h)` 推过去。
    E_φ 的 twist 方程见本文件上半部分（`ePhiTwistEq0`/`ePhiTwistEq1`）；twist unit 由两者的乘性比较给出。 -/

open LeanFormal.IUT.XiFPaper.Mzk1G1B3PullbackO1YActual in
/-- ω_Y 的单元推到 S9 的 h-overlap cover（B3 第二式的 ω 侧单元）。 -/
noncomputable def omegaUnitH (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) :
    (LeanFormal.IUT.XiFPaper.Mzk1G1B3PullbackO1YActual.hOverlap n T h)ˣ :=
  Units.map (algebraMap (LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual.Overlap0 n)
    (LeanFormal.IUT.XiFPaper.Mzk1G1B3PullbackO1YActual.hOverlap n T h)).toMonoidHom
    (LeanFormal.IUT.XiFPaper.Mzk1G1A5LineBundleIsoActual.omegaYEUnit n)

open LeanFormal.IUT.XiFPaper.Mzk1G1B3PullbackO1YActual in
/-- `omegaUnitH` 的值就是 `omegaYEUnit` 的像。 -/
theorem omegaUnitH_val (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) :
    (omegaUnitH n T h : LeanFormal.IUT.XiFPaper.Mzk1G1B3PullbackO1YActual.hOverlap n T h) =
      algebraMap (LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual.Overlap0 n)
        (LeanFormal.IUT.XiFPaper.Mzk1G1B3PullbackO1YActual.hOverlap n T h)
        (LeanFormal.IUT.XiFPaper.Mzk1G1A5LineBundleIsoActual.omegaYEUnit n :
          LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual.Overlap0 n) := rfl

#print axioms omegaUnitH
#print axioms omegaUnitH_val

end LeanFormal.IUT.XiFPaper.Mzk1G1B3OmegaETwistActual