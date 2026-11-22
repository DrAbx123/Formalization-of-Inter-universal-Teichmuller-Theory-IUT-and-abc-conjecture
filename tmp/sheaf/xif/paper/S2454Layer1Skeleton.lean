import tmp.sheaf.xif.paper.S2195Layer1InstanceActual
import tmp.sheaf.xif.paper.S2232Layer1PrimeAlignmentActual
import tmp.sheaf.xif.paper.S2040QVPlaceSplitActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction

/-! # S2454: layer (1) skeleton + S1493 point-transport skeleton

BUILD HOLD: this file is written but NOT compiled.  It records the corrected
imports/binders for S2432 and the S1493 transport proof plan.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2454Layer1Skeleton

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1712OddResidueActual
open LeanFormal.IUT.XiFPaper.S1717PlaceSevenD5Actual
open LeanFormal.IUT.XiFPaper.S1729FullBadPlaceActual
open LeanFormal.IUT.XiFPaper.S1730BadSetWithoutLActual
open LeanFormal.IUT.XiFPaper.S2040QVPlaceSplitActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.S2195Layer1InstanceActual
open LeanFormal.IUT.XiFPaper.S2232Layer1PrimeAlignmentActual

universe u

variable {l : PrimeGeFive}
  (T : LeanFormal.IUT.InitialThetaSource.SourceNativeInitialThetaData.{0} l)
  (b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad
    (LeanFormal.IUT.nativePlaceSelection T))

/-- Layer (1) split package from the named paper arithmetic conditions.
The proof uses the actual S2195 package and S2232 equivalence; no Nonempty
elimination into Type is needed (Classical.choice is used only to extract the
witness from the equivalence's Nonempty form). -/
noncomputable def S2454Layer1Split_of_paperConditions
    (h : S2232PaperArithmeticConditions T b) :
    S2040QVPlaceSplitPackage T b := by
  exact s2135_toPackage T b
    (Classical.choice (s2232_package_of_paperArithmeticConditions T b h))

/-! ## S1493 point transport skeleton

`pointTransport : SideFPoint T b ≃+ SideKPoint T b` maps F-side closure points
to K-side closure points.  S2412 produces points on
`W.map (algebraMap R (AlgebraicClosure R))`.  The missing point-level link is
a map/iso
`AlgebraicClosure R -> LF T b` (or a direct base-change identification of the
S2412 curve with `WFproj`).  Once supplied: -/

-- Planned signature (uses the real S1550/S2412 names; not compiled here):
-- theorem S2454_transport_three_points
--     (h2 : (2 : R) ≠ 0)
--     (h : ... S2412ThreePoints data on W.map (algebraMap R (AlgebraicClosure R)) ...) :
--     ∃ P1 P2 P3 : SideKPoint T b,
--       (2 : Nat) • P1 = 0 ∧ (2 : Nat) • P2 = 0 ∧ (2 : Nat) • P3 = 0 ∧
--       P1 ≠ P2 ∧ P1 ≠ P3 ∧ P2 ≠ P3 ∧ P1 ≠ 0 ∧ P2 ≠ 0 ∧ P3 ≠ 0

#print axioms S2454Layer1Split_of_paperConditions

end LeanFormal.IUT.XiFPaper.S2454Layer1Skeleton

end
