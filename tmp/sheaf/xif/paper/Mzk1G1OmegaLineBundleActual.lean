/- G1-B (iii): the canonical line bundle data and the explicit ramification differentials.
Route 3.1 (A3)/(A4): two-chart trivializations (omega_0 on U0, omega_inf on U1) with
transition unit u0^(n-3); route 3.2: d(lambda) = n x^(n-1) dx on the lambda-chart
(the ramification exponent n-1 at lambda = 0). -/
import tmp.sheaf.xif.paper.Mzk1G1OmegaFreeActual
import tmp.sheaf.xif.paper.Mzk1G1OmegaInfFreeActual
import tmp.sheaf.xif.paper.Mzk1G1OmegaTransitionGlobalActual
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual
import tmp.sheaf.xif.paper.Mzk1G1FermatTransitionActual
import tmp.sheaf.xif.paper.Mzk1G1FermatSecondChartActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaFreeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaInfFreeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaInfinityActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaTransitionGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleActual

/-- The unit of the overlap ring given by u0^(n-3). -/
noncomputable def transitionUnit (n : Nat) : (O0 n)ˣ :=
  ((u0_isUnit n).pow (n - 3)).unit

theorem transitionUnit_spec (n : Nat) :
    ((transitionUnit n : O0 n)) = u0 n ^ (n - 3) :=
  ((u0_isUnit n).pow (n - 3)).unit_spec

/-- A3 as a transition-unit identity: the infinity generator is the transition unit
times the affine generator on the overlap. -/
theorem omegaInfRaw_eq_transitionUnit_smul (n : Nat) (hn : 3 ≤ n) :
    omegaInfRaw n = ((transitionUnit n : O0 n)) • omega0O n := by
  rw [transitionUnit_spec]
  exact omegaInfRaw_eq_pow_smul_omega0O n hn

/-- The affine generator is the localization of the actual U0 generator omegaForm. -/
theorem localize_omegaForm (n : Nat) :
    KaehlerDifferential.map ℚ ℚ (B n) (O0 n) (omegaForm n) = omega0O n := by
  have hx : algebraMap (B n) (O0 n) (coordX n) = u0 n := rfl
  have hy : algebraMap (B n) (O0 n) (coordY n) = w0 n := rfl
  have hX : KaehlerDifferential.map ℚ ℚ (B n) (O0 n) (dX n) = du n := by
    rw [dX, du, KaehlerDifferential.map_D, hx]
  have hY : KaehlerDifferential.map ℚ ℚ (B n) (O0 n) (dY n) = dw n := by
    rw [dY, dw, KaehlerDifferential.map_D, hy]
  rw [omegaForm, omega0O, map_sub, map_smul, map_smul, hX, hY]
  rw [← IsScalarTower.algebraMap_smul (R := B n) (A := O0 n) (coordY n),
    ← IsScalarTower.algebraMap_smul (R := B n) (A := O0 n) (coordX n)]
  rw [hy, hx]

/-- Local trivializations of Omega on the two charts: e0(omega0) = 1, e1(omega_inf) = 1. -/
noncomputable def omegaTrivial0 (n : Nat) (hn : 1 ≤ n) : Omega n ≃ₗ[B n] B n :=
  omegaEquivO n hn

noncomputable def omegaTrivial1 (n : Nat) (hn : 1 ≤ n) : OmegaInf n ≃ₗ[R2 n] R2 n :=
  omegaInfEquivO n hn

theorem omegaTrivial0_omegaForm (n : Nat) (hn : 1 ≤ n) :
    omegaTrivial0 n hn (omegaForm n) = 1 :=
  omegaEquivO_omegaForm n hn

theorem omegaTrivial1_omegaInfForm (n : Nat) (hn : 1 ≤ n) :
    omegaTrivial1 n hn (omegaInfForm n) = 1 :=
  omegaInfEquivO_omegaInfForm n hn

/-- The canonical line bundle data: two-chart trivializations together with the
transition unit u0^(n-3) (this is O(n-3) in the two-chart presentation). -/
theorem canonicalLineBundle_data (n : Nat) (hn : 3 ≤ n) :
    omegaTrivial0 n (by omega) (omegaForm n) = 1 ∧
    omegaTrivial1 n (by omega) (omegaInfForm n) = 1 ∧
    omegaInfRaw n = ((transitionUnit n : O0 n)) • omega0O n :=
  ⟨omegaTrivial0_omegaForm n (by omega),
    omegaTrivial1_omegaInfForm n (by omega),
    omegaInfRaw_eq_transitionUnit_smul n hn⟩

/-- Ramification on the lambda-chart: d(lambda) = n x^(n-1) dx since lambda = x^n. -/
theorem pi_pullback_lambda (n : Nat) :
    KaehlerDifferential.D ℚ (B n) (coordX n ^ n) =
      ((n : B n) * coordX n ^ (n - 1)) • dX n := by
  rw [Derivation.leibniz_pow, nsmul_smul_eq]
  rfl

/-- Ramification on the second boundary: d(1-lambda) = -n y^(n-1) dy since 1-lambda = y^n. -/
theorem pi_pullback_one_sub_lambda (n : Nat) :
    KaehlerDifferential.D ℚ (B n) (1 - coordY n ^ n) =
      -(((n : B n) * coordY n ^ (n - 1)) • dY n) := by
  rw [map_sub, Derivation.map_one_eq_zero, zero_sub]
  rw [Derivation.leibniz_pow, nsmul_smul_eq]
  rfl

/-- Ramification at infinity: d t = n r^(n-1) dr since t = r^n. -/
theorem pi_pullback_infinity (n : Nat) :
    KaehlerDifferential.D ℚ (R2 n) (infinityR n ^ n) =
      ((n : R2 n) * infinityR n ^ (n - 1)) • dR n := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (R2 n) n, smul_smul]
  rfl

#print axioms omegaInfRaw_eq_transitionUnit_smul
#print axioms localize_omegaForm
#print axioms canonicalLineBundle_data
#print axioms pi_pullback_lambda
#print axioms pi_pullback_one_sub_lambda
#print axioms pi_pullback_infinity

/-! ## A5 at the transition level and the boundary coordinate powers -/

/-- pi^* O(1) transition unit on the overlap: the pullback of the P^1 coordinate is x^n. -/
noncomputable def pullbackO1Unit (n : Nat) : (O0 n)ˣ :=
  ((u0_isUnit n).pow n).unit

theorem pullbackO1Unit_spec (n : Nat) :
    ((pullbackO1Unit n : O0 n)) = u0 n ^ n :=
  ((u0_isUnit n).pow n).unit_spec

/-- The O(E) = O(3) part of the E-fiber divisor, as a transition unit u0^3. -/
noncomputable def lineBundleEUnit (n : Nat) : (O0 n)ˣ :=
  ((u0_isUnit n).pow 3).unit

theorem lineBundleEUnit_spec (n : Nat) :
    ((lineBundleEUnit n : O0 n)) = u0 n ^ 3 :=
  ((u0_isUnit n).pow 3).unit_spec

/-- A5 at the transition-function level: omega_Y(E) = omega_Y tensor O(E) has transition
u0^(n-3) * u0^3 = u0^n, which is exactly the transition of pi^* omega_{P^1}(0+1+infty). -/
theorem a5_transition_unit (n : Nat) (hn : 3 ≤ n) :
    ((transitionUnit n : O0 n)) * ((lineBundleEUnit n : O0 n)) =
      ((pullbackO1Unit n : O0 n)) := by
  rw [transitionUnit_spec, lineBundleEUnit_spec, pullbackO1Unit_spec, ← pow_add]
  rw [show n - 3 + 3 = n by omega]

/-- Boundary fiber at lambda = 0: the coordinate satisfies lambda = x^n. -/
theorem lambda_eq_x_pow (n : Nat) : coordX n ^ n = 1 - coordY n ^ n := by
  have h : coordX n ^ n + coordY n ^ n = 1 := sub_eq_zero.mp (relation n)
  rw [← h]
  ring

/-- Boundary fiber at lambda = 1: the coordinate satisfies 1 - lambda = y^n. -/
theorem one_sub_lambda_eq_y_pow (n : Nat) : 1 - coordX n ^ n = coordY n ^ n := by
  have h : coordX n ^ n + coordY n ^ n = 1 := sub_eq_zero.mp (relation n)
  rw [← h]
  ring

/-- Boundary fiber at infinity: the coordinate satisfies t = r^n. -/
theorem infinity_t_eq_r_pow (n : Nat) : infinityR n ^ n = 1 + infinityS n ^ n := by
  have h : 1 + infinityS n ^ n = infinityR n ^ n :=
    sub_eq_zero.mp (infinityS_pow_add_one_sub_infinityR_pow n)
  rw [← h]

#print axioms a5_transition_unit
#print axioms lambda_eq_x_pow
#print axioms one_sub_lambda_eq_y_pow
#print axioms infinity_t_eq_r_pow

end LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleActual
