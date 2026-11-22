/- A3 route-conforming (3): differential of the psi chart-0 coordinate (algebraic heart).

  RECON (repo check before writing, per Lead):
  * `Mzk1G1OmegaFreeActual` (DONE): `Psi : Omega n →ₗ[B n] B n`, `Psi_dX`, `Psi_omegaForm`,
    `Phi_injective/surjective`, `phiEquiv`/`omegaEquivO : Omega n ≃ₗ[B n] B n`
    ==> Omega_{R n/Q} is FREE OF RANK 1 with basis `omegaForm`;
  * `Mzk1G1OmegaBasisActual` (DONE): `omegaForm`, `y_pow_smul_omegaForm`, `natCast_isUnit`;
  * `Mzk1G1OmegaActual` (DONE): `dX/dY`, `derivation_relation`;
  * Mathlib `Derivation.map_aeval` (RingTheory/Derivation/Basic.lean:150): the chain rule
    `D (aeval x P) = aeval x (derivative P) • D x` is ALREADY PROVED (no need to build it).
  No duplicate work: the file only assembles the above.

  Content: `D (psiChart0Coord) = g'(x) • dX` and `Psi (D psiChart0Coord) = g'(x) * n * y^{n-1}`,
  where `g = protectedToZeroPolynomial T`. The remaining F2.2/B2 step (scheme-level
  `Ram (chartMorphism0 u) @ p <-> D u not in p Omega`) stays a registered obligation.
  No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1OmegaFreeActual
import tmp.sheaf.xif.paper.Mzk1G1A3PsiChartPolyActual
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaFreeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A3PsiChartPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedToZeroMapActual

variable (n : Nat)

/-- `D x = dX`（两个定义是同一元素）。 -/
theorem D_chartX_eq : KaehlerDifferential.D ℚ (R n) (chartX n) = dX n := by
  simp [chartX, dX, coordX]

/-- **链式法则实例**：`D (psiChart0Coord) = g′(x) • dX`。 -/
theorem D_psiChart0Coord (T : Finset ℚ) :
    KaehlerDifferential.D ℚ (R n) (psiChart0Coord n T) =
      (Polynomial.aeval (chartX n)
          (Polynomial.derivative (protectedToZeroPolynomial (K := ℚ) T))) •
        KaehlerDifferential.D ℚ (R n) (chartX n) := by
  rw [psiChart0Coord_eq_aeval_protectedToZero]
  exact Derivation.map_aeval (D := KaehlerDifferential.D ℚ (R n)) _ _

/-- **`P` 对偶下的显式公式**：`Psi (D psiChart0Coord) = g′(x) * n * y^{n-1}`。 -/
theorem Psi_D_psiChart0Coord (hn : 1 ≤ n) (T : Finset ℚ) :
    Psi n (KaehlerDifferential.D ℚ (R n) (psiChart0Coord n T)) =
      Polynomial.aeval (chartX n)
          (Polynomial.derivative (protectedToZeroPolynomial (K := ℚ) T)) *
        (n : R n) * coordY n ^ (n - 1) := by
  rw [D_psiChart0Coord, D_chartX_eq, map_smul, Psi_dX, smul_eq_mul, mul_assoc]

#print axioms D_chartX_eq
#print axioms D_psiChart0Coord
#print axioms Psi_D_psiChart0Coord

end LeanFormal.IUT.XiFPaper.Mzk1G1A3ChartDiffActual