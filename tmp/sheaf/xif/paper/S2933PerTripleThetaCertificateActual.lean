import tmp.sheaf.xif.paper.S2921HeightBridgeActual
import tmp.sheaf.xif.paper.S2919ThetaUpperFromProcession
import tmp.sheaf.xif.paper.S2792NormalizedLineBundleBridge

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2919ThetaUpperFromProcession
open LeanFormal.IUT.XiFPaper.S2838HeightComparisonReductionActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open Finset
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2933PerTripleThetaCertificateActual

/-- Per-triple theta upper expression using the actual S2921 candidates. -/
noncomputable def S2933ThetaUpper
    (n : Nat) (a b c : Nat) : Real :=
  ((2 * (n : Real) + 1) + 1) / 4 *
    ((1 + 4 / (2 * (n : Real) + 1)) * S2921D - S2921Q a b c / 6 +
      4 / (2 * (n : Real) + 1) * S2921S a b c + 20 / 3 * S2921T a b c)

/-- Per-triple theta certificate.  D/Q/S/T are the actual S2921 candidates;
height_le_procession and theta_le_region are explicit inputs. -/
structure S2933Certificate where
  n : Nat
  hn : 2 ≤ n
  eps : Real
  AJ : Real
  hD : ∀ a b c : Nat, 0 ≤ S2921D
  hS : ∀ a b c : Nat, 0 ≤ S2921S a b c
  hT : ∀ a b c : Nat, 0 ≤ S2921T a b c
  height_le_procession :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcJInvariant a b c) ≤
        (1 / (n : Real)) *
          ∑ j ∈ Icc 1 n,
            collectionBound (2 * (n : Real) + 1) S2921D
              (S2921Q a b c) (S2921S a b c) (S2921T a b c) j
  theta_le_region :
    ∀ a b c : Nat, IsABCTriple a b c →
      S2933ThetaUpper n a b c ≤
        6 * (1 + eps) * S2792RegionVolume a b c + AJ

/-- Procession bound for each triple, from the actual processionAverage_le. -/
theorem S2933_procession_le_thetaUpper
    (C : S2933Certificate) (a b c : Nat) :
    (1 / (C.n : Real)) *
        ∑ j ∈ Icc 1 C.n,
          collectionBound (2 * (C.n : Real) + 1) S2921D
            (S2921Q a b c) (S2921S a b c) (S2921T a b c) j ≤
      S2933ThetaUpper C.n a b c :=
  processionAverage_le C.n C.hn S2921D (S2921Q a b c)
    (S2921S a b c) (S2921T a b c)
    (C.hD a b c) (C.hS a b c) (C.hT a b c)

/-- Per-triple theta upper bound. -/
theorem S2933_thetaUpper_bound
    (C : S2933Certificate) (a b c : Nat) (habc : IsABCTriple a b c) :
    Height.logHeight₁ (abcJInvariant a b c) ≤
      6 * (1 + C.eps) * S2792RegionVolume a b c + C.AJ := by
  have h1 := C.height_le_procession a b c habc
  have h2 := S2933_procession_le_thetaUpper C a b c
  have h3 := C.theta_le_region a b c habc
  exact le_trans h1 (le_trans h2 h3)

/-- Certificate gives S2838ThetaUpperGap. -/
theorem S2933_to_S2838ThetaUpperGap (C : S2933Certificate) :
    S2838ThetaUpperGap C.eps C.AJ := by
  intro a b c habc
  exact S2933_thetaUpper_bound C a b c habc

#check S2933ThetaUpper
#check S2933Certificate
#check S2933_procession_le_thetaUpper
#check S2933_thetaUpper_bound
#check S2933_to_S2838ThetaUpperGap
#print axioms S2933_procession_le_thetaUpper
#print axioms S2933_thetaUpper_bound
#print axioms S2933_to_S2838ThetaUpperGap

end LeanFormal.IUT.XiFPaper.S2933PerTripleThetaCertificateActual
end
