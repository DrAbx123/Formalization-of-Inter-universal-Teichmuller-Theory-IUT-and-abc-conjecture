import tmp.sheaf.xif.paper.Mzk1G1F8O1Actual
import Mathlib.Tactic
/-!
# F8: merged first/second equality chain

Combines the chart-0 first equality (with its explicit `n * finrank * log 2` error) and
the `omega_Y(E)` frame second equality, in the form consumed by the P8 assembly.
-/
noncomputable section
open AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F8MergedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F8SecondActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F8O1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaTransitionGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A5LineBundleIsoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleActual
variable {k : Type*} [Field k] [NumberField k]

/-- Frame form of the F8 chain: the `pi^*O(1)` frame height equals `n *` the `O_Y(1)`
height, hence `n/(n-3)` times the `omega_Y(E)` frame height. -/
theorem f8_frame_chain (n : Nat) (hn : 4 ≤ n) (Φ : O0 n →+* k) :
    frameHeight n Φ (omegaYEUnit n)
      = ((n : ℝ) / ((n : ℝ) - 3)) * frameHeight n Φ (transitionUnit n) :=
  f8_second_equality_omegaE_frame n hn Φ

/-- Pointwise chart-0 chain: the F8 first equality error and the second equality are
compatible (the second equality is exact at the chart level). -/
theorem f8_chart0_second_eq (n : Nat) (hn : 4 ≤ n) (φ : Chart0Ring n →+* k) :
    Height.logHeight₁ ((φ (x0 n)) ^ n)
      = ((n : ℝ) / ((n : ℝ) - 3)) * Height.logHeight₁ ((φ (x0 n)) ^ (n - 3)) :=
  f8_second_equality_chart0 n hn φ

#print axioms f8_frame_chain
#print axioms f8_chart0_second_eq
end LeanFormal.IUT.XiFPaper.Mzk1G1F8MergedActual
end