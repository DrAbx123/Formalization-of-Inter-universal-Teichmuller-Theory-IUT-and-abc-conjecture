/- G1-B (iii): named two-chart line-bundle data for A4/A5 (for G-C B3 and H-T consumers),
plus the route 3.3 separation of the three different notions. -/
import tmp.sheaf.xif.paper.Mzk1G1OmegaLineBundleActual
import tmp.sheaf.xif.paper.Mzk1G1OmegaFreeActual
import tmp.sheaf.xif.paper.Mzk1G1OmegaInfFreeActual
import tmp.sheaf.xif.paper.Mzk1G1OmegaTransitionGlobalActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaFreeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaInfFreeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaInfinityActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaTransitionGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleDataActual

/-- **Two-chart line-bundle data for the canonical bundle**: trivializations on the two
charts together with the A4 transition unit and the A5 transition units. -/
structure CanonicalLineBundleData (n : Nat) where
  /-- the local trivialization on the affine chart U0 -/
  trivial0 : Omega n ≃ₗ[B n] B n
  /-- the local trivialization on the affine chart U1 -/
  trivial1 : OmegaInf n ≃ₗ[R2 n] R2 n
  /-- the A4 transition unit: omega_inf = unit * omega_0 on the overlap -/
  omegaTransition : (O0 n)ˣ
  /-- the O(E) = O(3) part of the A5 transition -/
  eUnit : (O0 n)ˣ
  /-- the pi^* O(1) transition unit (the pullback of the P^1 coordinate) -/
  pullbackUnit : (O0 n)ˣ

/-- The canonical line bundle data, instantiated with the actual objects. -/
noncomputable def canonicalLineBundleData (n : Nat) (hn : 3 ≤ n) : CanonicalLineBundleData n where
  trivial0 := omegaTrivial0 n (by omega)
  trivial1 := omegaTrivial1 n (by omega)
  omegaTransition := transitionUnit n
  eUnit := lineBundleEUnit n
  pullbackUnit := pullbackO1Unit n

theorem canonicalLineBundleData_trivial0_omegaForm (n : Nat) (hn : 3 ≤ n) :
    (canonicalLineBundleData n hn).trivial0 (omegaForm n) = 1 :=
  omegaTrivial0_omegaForm n (by omega)

theorem canonicalLineBundleData_trivial1_omegaInfForm (n : Nat) (hn : 3 ≤ n) :
    (canonicalLineBundleData n hn).trivial1 (omegaInfForm n) = 1 :=
  omegaTrivial1_omegaInfForm n (by omega)

theorem canonicalLineBundleData_omegaTransition_spec (n : Nat) (hn : 3 ≤ n) :
    (((canonicalLineBundleData n hn).omegaTransition : O0 n)) = u0 n ^ (n - 3) :=
  transitionUnit_spec n

theorem canonicalLineBundleData_transition_smul (n : Nat) (hn : 3 ≤ n) :
    omegaInfRaw n = (((canonicalLineBundleData n hn).omegaTransition : O0 n)) • omega0O n :=
  omegaInfRaw_eq_transitionUnit_smul n hn

theorem canonicalLineBundleData_eUnit_spec (n : Nat) (hn : 3 ≤ n) :
    (((canonicalLineBundleData n hn).eUnit : O0 n)) = u0 n ^ 3 :=
  lineBundleEUnit_spec n

theorem canonicalLineBundleData_pullbackUnit_spec (n : Nat) (hn : 3 ≤ n) :
    (((canonicalLineBundleData n hn).pullbackUnit : O0 n)) = u0 n ^ n :=
  pullbackO1Unit_spec n

/-- **A5 in the named data**: omega_Y(E) transition = omega_Y transition * O(E) transition
equals the pi^* O(1) transition. -/
theorem canonicalLineBundleData_a5 (n : Nat) (hn : 3 ≤ n) :
    (((canonicalLineBundleData n hn).omegaTransition : O0 n)) *
        (((canonicalLineBundleData n hn).eUnit : O0 n)) =
      (((canonicalLineBundleData n hn).pullbackUnit : O0 n)) :=
  a5_transition_unit n hn

/-- Route 3.2 algebraic boundary data: lambda = x^n, 1 - lambda = y^n, t = r^n, and the
three differential formulas d(lambda) = n x^(n-1) dx etc. -/
structure BoundaryRamificationAlgebraData (n : Nat) : Prop where
  lambda_eq_x_pow : coordX n ^ n = 1 - coordY n ^ n
  one_sub_lambda_eq_y_pow : 1 - coordX n ^ n = coordY n ^ n
  infinity_eq_r_pow : infinityR n ^ n = 1 + infinityS n ^ n
  d_lambda : KaehlerDifferential.D ℚ (B n) (coordX n ^ n) =
    ((n : B n) * coordX n ^ (n - 1)) • dX n
  d_one_sub_lambda : KaehlerDifferential.D ℚ (B n) (1 - coordY n ^ n) =
    -(((n : B n) * coordY n ^ (n - 1)) • dY n)
  d_infinity : KaehlerDifferential.D ℚ (R2 n) (infinityR n ^ n) =
    ((n : R2 n) * infinityR n ^ (n - 1)) • dR n

theorem boundaryRamificationAlgebraData (n : Nat) : BoundaryRamificationAlgebraData n where
  lambda_eq_x_pow := lambda_eq_x_pow n
  one_sub_lambda_eq_y_pow := one_sub_lambda_eq_y_pow n
  infinity_eq_r_pow := infinity_t_eq_r_pow n
  d_lambda := pi_pullback_lambda n
  d_one_sub_lambda := pi_pullback_one_sub_lambda n
  d_infinity := pi_pullback_infinity n

/-- Route 3.2 boundary ramification record: at lambda = 0 on the lambda-chart the
coordinates satisfy lambda = x^n (and 1 - lambda = y^n on the second boundary).  The e = n
local-ring cores are proved elsewhere: boundary_zero_uniformizer_power and
boundary_one_uniformizer_power in
Mzk1G1OmegaRamificationLocalActual, and boundary_infinity_uniformizer_power (general field K
with zeta^n = -1) in Mzk1G1OmegaRamificationInfinityActual.  So all three boundary fibres now
have actual e = n statements; this structure just records the algebraic coordinate facts. -/
structure BoundaryRamificationIndexObligation (n : Nat) : Prop where
  lambda_eq_x_pow : coordX n ^ n = 1 - coordY n ^ n
  differential : KaehlerDifferential.D ℚ (B n) (coordX n ^ n) =
    ((n : B n) * coordX n ^ (n - 1)) • dX n

/-- Route 3.3 (2): Omega_{Y/P^1}, the relative differential, a torsion sheaf supported on
the ramification points.  Interface only: NO INHABITANT is provided at this stage. -/
structure RelativeDifferentialInterface (n : Nat) where
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [module : Module (O0 n) carrier]

/-- Route 3.3 (3): the arithmetic different O_L/O_K (trace-dual at DVRs).
Interface only: NO INHABITANT is provided at this stage. -/
structure ArithmeticDifferentInterface (K L : Type*) [Field K] [Field L] [Algebra K L] where
  different : Ideal L

#print axioms canonicalLineBundleData_a5
#print axioms canonicalLineBundleData_transition_smul
#print axioms boundaryRamificationAlgebraData
end LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleDataActual
