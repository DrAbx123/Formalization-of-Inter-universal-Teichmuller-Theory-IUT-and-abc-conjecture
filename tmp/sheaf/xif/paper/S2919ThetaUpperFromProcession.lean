import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage
import tmp.sheaf.xif.paper.S2838HeightComparisonReductionActual
import tmp.sheaf.xif.paper.S2792NormalizedLineBundleBridge

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2838HeightComparisonReductionActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open Finset
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2919ThetaUpperFromProcession

/-- Theta upper certificate: the procession data D/Q/S/T, their nonnegativity,
the height-to-procession estimate for ABC triples, and the region identification
of the procession upper bound. -/
structure ThetaUpperCertificate where
  n : ℕ
  hn : 2 ≤ n
  D : ℝ
  Q : ℝ
  S : ℝ
  T : ℝ
  hD : 0 ≤ D
  hS : 0 ≤ S
  hT : 0 ≤ T
  eps : ℝ
  AJ : ℝ
  height_le_procession :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcJInvariant a b c) ≤
        (1 / (n : ℝ)) *
          ∑ j ∈ Icc 1 n,
            collectionBound (2 * (n : ℝ) + 1) D Q S T j
  theta_le_region :
    ∀ a b c : Nat, IsABCTriple a b c →
      ((2 * (n : ℝ) + 1) + 1) / 4 *
          ((1 + 4 / (2 * (n : ℝ) + 1)) * D - Q / 6 +
            4 / (2 * (n : ℝ) + 1) * S + 20 / 3 * T) ≤
        6 * (1 + eps) * S2792RegionVolume a b c + AJ

/-- The explicit procession upper bound (IV L1757–L1783). -/
noncomputable def ThetaUpperCertificate.thetaUpper
    (C : ThetaUpperCertificate) : ℝ :=
  ((2 * (C.n : ℝ) + 1) + 1) / 4 *
    ((1 + 4 / (2 * (C.n : ℝ) + 1)) * C.D - C.Q / 6 +
      4 / (2 * (C.n : ℝ) + 1) * C.S + 20 / 3 * C.T)

/-- Actual procession-average comparison: the average of the label bounds is at
most the theta upper bound. -/
theorem S2919_procession_le_thetaUpper (C : ThetaUpperCertificate) :
    (1 / (C.n : ℝ)) *
        ∑ j ∈ Icc 1 C.n,
          collectionBound (2 * (C.n : ℝ) + 1) C.D C.Q C.S C.T j ≤
      C.thetaUpper :=
  processionAverage_le C.n C.hn C.D C.Q C.S C.T C.hD C.hS C.hT

/-- Theta upper bound for ABC triples from the certificate. -/
theorem S2919_thetaUpper_bound (C : ThetaUpperCertificate)
    (a b c : Nat) (habc : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) ≤
      6 * (1 + C.eps) * S2792RegionVolume a b c + C.AJ := by
  have h1 := C.height_le_procession a b c habc
  have h2 := S2919_procession_le_thetaUpper C
  have h3 := C.theta_le_region a b c habc
  exact le_trans h1 (le_trans h2 h3)

/-- Conditional reduction: the certificate gives S2838ThetaUpperGap. -/
theorem S2919_to_S2838ThetaUpperGap (C : ThetaUpperCertificate) :
    S2838ThetaUpperGap C.eps C.AJ := by
  intro a b c habc
  exact S2919_thetaUpper_bound C a b c habc

#check ThetaUpperCertificate
#check ThetaUpperCertificate.thetaUpper
#check S2919_procession_le_thetaUpper
#check S2919_thetaUpper_bound
#check S2919_to_S2838ThetaUpperGap
#print axioms S2919_procession_le_thetaUpper
#print axioms S2919_thetaUpper_bound
#print axioms S2919_to_S2838ThetaUpperGap

end LeanFormal.IUT.XiFPaper.S2919ThetaUpperFromProcession
end
