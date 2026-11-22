/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.BadPlacePaperTargetStrictActual
import tmp.sheaf.xif.paper.BadPlacePaperNormalizedComparisonActual
import tmp.sheaf.xif.paper.BadPlaceRationalDegreeFactorActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeActual
import tmp.sheaf.xif.paper.Mzk1A1DeltaExplicitActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.Mzk1P2QNativeReadingCorrectedActual
import tmp.sheaf.xif.paper.Mzk1RootBaseCompletionGapActual
import tmp.sheaf.xif.paper.Mzk1P2QHatNormCoherenceProofActual
import tmp.sheaf.xif.paper.BadPlaceRationalDegreeActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import tmp.sheaf.xif.paper.Mzk1A1SignedReadoutProductActual
import Mathlib.Tactic

/-! # P1 #1: paper sums <-> S3137 bridge (weights, log objects, explicit conditions)

**Proved here:** paper sum weight is `1/[K_w:F_v]`; `d_b` sits inside
`paperNormalizedCoefficient`; and (from QHat coherence, GREEN)
`P2QHatNormInstanceAgreement` holds *unconditionally*.

**Remaining explicit inputs:**
1. `S45SourceFields` — the paper S45 normalized-source condition (ratio=1 + root-hull
   scaling), *not* an extra assumption added for convenience;
2. `RelativeFactorTowerData` — the explicit per-b degree tower with relative factor
   `B = [K_w:F_v]` (the naive identity is FALSE when B>1, see
   `Mzk1RootBaseCompletionGapActual.rootBaseDegreeIdentity_false_of_relativeDegree`);
3. `PaperToS3137A1Data` — the a1Delta <-> paper coefficient dictionary (explicit GAP);
4. `PaperS3137ReadingDictionary` — CONSTRUCTED in `Mzk1P0FinalS3137DictionaryActual`, given the substantive `PaperS3137ObjectLock` (index/weight B_b/unitMass/sign data, all explicit).

No equality of paper sums with hull closed form is assumed; `unitMass = 1` is not used. -/

noncomputable section
open scoped BigOperators ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1PaperSumsToS3137BridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperTargetStrictActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeFactorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1A1SignedReadoutProductActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1A1DeltaExplicitActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.Mzk1RootBaseCompletionGapActual
open LeanFormal.IUT.XiFPaper.Mzk1P2QHatNormCoherenceProofActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

theorem paper_sum_weight_eq_inv (b : Bad (nativePlaceSelection T)) :
    nativeBadLocalWeight T b =
      ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Nat) : Real)⁻¹ :=
  nativeBadLocalWeight_eq_inv T b

theorem paper_coefficient_degree_factor (b : Bad (nativePlaceSelection T)) :
    paperNormalizedCoefficient T b =
      ((qVFamily T b).order : Real) * rationalDegreeFactor T b *
        (Real.log (qVFamTensorRationalBaseNorm T b) /
          Real.log (qVFamTensorP T b : Real)) :=
  paperNormalizedCoefficient_eq_degree_factor T b

/-- S45 normalized-source condition (ratio = 1 + root-hull scaling). -/
def S45SourceFields : Prop := Nonempty (PaperSourceCorrectionFreeFields T)

/-- **EXPLICIT CONDITION (divisibility, not a field tower).**
This is only the number-theoretic divisibility statement `rootBaseQpDegree b | kPlaceQpDegree b`
(equivalently, existence of a quotient `B` with `C = B * A`).  It does **not** construct a
field tower `Q_p ⊆ F_v ⊆ K_w`, and the semantic meaning `B = [K_w : F_v]` is NOT established:
`F_v` need not embed into `K_w`.  The naive degree identity `A = C` is FALSE when `B > 1`
(`Mzk1RootBaseCompletionGapActual.rootBaseDegreeIdentity_false_of_relativeDegree`).
If this divisibility fails for the actual data, the weight convention must be changed instead of
assuming it. -/
def RelativeFactorTowerData : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    exists (A B C : Nat),
      0 < A ∧ rootBaseQpDegree T b = A ∧ kPlaceQpDegree T b = C ∧ C = B * A

/-- The a1Delta <-> paper coefficient dictionary (explicit, not asserted). -/
structure PaperToS3137A1Data where
  a1_delta_paper : ∀ b : Bad (nativePlaceSelection T),
    a1Delta (T := T) (b := b) =
      -((qVFamNormalizedCoefficient T b / (2 * (l.value : Real))) *
          Real.log (qVFamTensorP T b : Real)) -
        (1 / (s1915LocalDegree T b : Real)) *
          (Real.log (rootExtensionHaar T b (c0QLattice T b)).toReal -
            Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal)

def paperS3137BridgeRows : List (String × String × String) :=
  [ ("paper_sum_weight_eq_inv", "paper sum weight = 1/[K_w:F_v] (e*f)", "PROVED (rfl)"),
    ("paper_coefficient_degree_factor", "d_b inside paperNormalizedCoefficient", "PROVED"),
    ("p2QHatNormInstanceAgreement_proved", "QHat norm coherence", "PROVED (QHat proof file)"),
    ("S45SourceFields", "S45 ratio=1 source condition (explicit)", "EXPLICIT CONDITION"),
    ("RelativeFactorTowerData", "EXPLICIT CONDITION (divisibility A|C, not a field tower); naive identity FALSE if B>1", "EXPLICIT CONDITION/GAP"),
    ("PaperToS3137A1Data", "a1Delta paper dictionary", "EXPLICIT GAP"),
    ("PaperS3137ReadingDictionary", "CONSTRUCTED in Mzk1P0FinalS3137DictionaryActual (substantive PaperS3137ObjectLock; sign/unitMass explicit; no True)", "CONSTRUCTED (given lock)") ]

theorem paperS3137BridgeRows_length : paperS3137BridgeRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1PaperSumsToS3137BridgeActual

end