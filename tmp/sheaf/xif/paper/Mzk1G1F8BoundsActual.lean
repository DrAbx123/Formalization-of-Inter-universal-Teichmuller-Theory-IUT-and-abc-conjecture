import tmp.sheaf.xif.paper.Mzk1G1F8ChainActual
import tmp.sheaf.xif.paper.Mzk1G1F8O1Actual
import tmp.sheaf.xif.paper.Mzk1G1F8SecondActual
import Mathlib.Tactic
/-!
# F8: packaged O(log 2) bounds

* `f8_h_pi_bound`: `f8_chain_chart0` (21:34:21) with its explicit `n * finrank * log 2` error;
* `f8_h_omega_bound`: exact second equality on the actual H0 frames (`f8_second_equality_H0frame`);
* `f8_first_second_combined` / `f8_Olog2_bound`: packaged forms.
-/
noncomputable section
open AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.F8BoundsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.F8ChainActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F8SecondActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F8O1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleActual
variable {k : Type} [Field k] [NumberField k]

theorem f8_h_pi_bound (n : Nat) (hn : 4 ≤ n) (φ : Chart0Ring n →+* k)
    (hrel : (φ (x0 n)) ^ n + (φ (x1 n)) ^ n = 1) :
    |((n : ℝ) / ((n : ℝ) - 3)) * Height.logHeight₁ ((φ (x0 n)) ^ (n - 3))
        - (n : ℝ) * Height.logHeight ![(φ (x0 n)), (φ (x1 n)), 1]|
      ≤ (n : ℝ) * ((Module.finrank ℚ k : ℝ) * Real.log 2) :=
  f8_chain_chart0 n hn φ hrel

theorem f8_h_omega_bound (n : Nat) (hn : 4 ≤ n) (φ : Chart0Ring n →+* k) :
    |Height.logHeight₁ (φ ((pullbackO1F1Data n).frame0))
        - ((n : ℝ) / ((n : ℝ) - 3)) * Height.logHeight₁ (φ ((omegaYF1Data n).frame0))|
      ≤ 0 :=
  abs_sub_le_iff.mpr ⟨by rw [f8_second_equality_H0frame n hn φ]; linarith,
    by rw [f8_second_equality_H0frame n hn φ]; linarith⟩

theorem f8_first_second_combined (n : Nat) (hn : 4 ≤ n) (φ : Chart0Ring n →+* k)
    (hrel : (φ (x0 n)) ^ n + (φ (x1 n)) ^ n = 1) :
    (|((n : ℝ) / ((n : ℝ) - 3)) * Height.logHeight₁ ((φ (x0 n)) ^ (n - 3))
        - (n : ℝ) * Height.logHeight ![(φ (x0 n)), (φ (x1 n)), 1]|
      ≤ (n : ℝ) * ((Module.finrank ℚ k : ℝ) * Real.log 2)) ∧
    (|Height.logHeight₁ (φ ((pullbackO1F1Data n).frame0))
        - ((n : ℝ) / ((n : ℝ) - 3)) * Height.logHeight₁ (φ ((omegaYF1Data n).frame0))|
      ≤ 0) :=
  ⟨f8_h_pi_bound n hn φ hrel, f8_h_omega_bound n hn φ⟩

theorem f8_Olog2_bound (n : Nat) (hn : 4 ≤ n) (φ : Chart0Ring n →+* k)
    (hrel : (φ (x0 n)) ^ n + (φ (x1 n)) ^ n = 1) :
    |((n : ℝ) / ((n : ℝ) - 3)) * Height.logHeight₁ ((φ (x0 n)) ^ (n - 3))
        - (n : ℝ) * Height.logHeight ![(φ (x0 n)), (φ (x1 n)), 1]|
      ≤ (n : ℝ) * ((Module.finrank ℚ k : ℝ) * Real.log 2) :=
  f8_h_pi_bound n hn φ hrel

#print axioms f8_h_pi_bound
#print axioms f8_h_omega_bound
#print axioms f8_first_second_combined
#print axioms f8_Olog2_bound
end LeanFormal.IUT.XiFPaper.F8BoundsActual
end