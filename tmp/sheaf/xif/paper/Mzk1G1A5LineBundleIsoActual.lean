/- Route 3.1 A5 (divisor-layer line-bundle iso) using the ported AG_FLT two-chart Cech donor:
the canonical cover with both charts the affine U0 and overlap the localized ring, and the
line-bundle isomorphism omega_Y(E) = omega_Y tensor O(E) from the transition-unit equality
u0^(n-3) * u0^3 = u0^n. -/
import tmp.sheaf.xif.paper.AG_FLT_TwoChartCechActual
import tmp.sheaf.xif.paper.Mzk1G1OmegaLineBundleActual
import tmp.sheaf.xif.paper.Mzk1G1OmegaTransitionGlobalActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A5LineBundleIsoActual

open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaTransitionGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual

/-- The canonical two-chart cover: both charts are the affine chart U0 and the overlap is the
localized ring O0; the two restriction maps are the localization maps. -/
def canonicalCover (n : Nat) : TwoChartCech.Cover ℚ where
  A0 := B n
  A1 := B n
  A01 := O0 n
  ρ0 := IsScalarTower.toAlgHom ℚ (B n) (O0 n)
  ρ1 := IsScalarTower.toAlgHom ℚ (B n) (O0 n)

/-- The transition unit of omega_Y(E) is the product of the omega_Y unit and the O(E) unit. -/
def omegaYEUnit (n : Nat) : (O0 n)ˣ := transitionUnit n * lineBundleEUnit n

/-- The transition unit of pi^* omega_{P^1}(0+1+infty). -/
def pullbackOmegaP1Unit (n : Nat) : (O0 n)ˣ := pullbackO1Unit n

/-- A5 unit identity: omega_Y(E) and pi^* omega_{P^1}(0+1+infty) have the same transition unit. -/
theorem omegaYEUnit_eq_pullbackUnit (n : Nat) (hn : 3 ≤ n) :
    omegaYEUnit n = pullbackOmegaP1Unit n :=
  Units.ext (a5_transition_unit n hn)

/-- **A5 complete line-bundle iso** (in the two-chart Cech model): the line bundle
omega_Y(E) = omega_Y tensor O(E) is isomorphic to pi^* omega_{P^1}(0+1+infty). -/
theorem a5_lineBundle_iso (n : Nat) (hn : 3 ≤ n) :
    TwoChartCech.Cover.lineBundle (canonicalCover n) (omegaYEUnit n) =
      TwoChartCech.Cover.lineBundle (canonicalCover n) (pullbackOmegaP1Unit n) := by
  rw [omegaYEUnit_eq_pullbackUnit n hn]

#print axioms a5_lineBundle_iso
end LeanFormal.IUT.XiFPaper.Mzk1G1A5LineBundleIsoActual
