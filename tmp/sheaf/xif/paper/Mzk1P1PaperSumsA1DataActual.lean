/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1PaperSumsToS3137BridgeActual
import tmp.sheaf.xif.paper.Mzk1P1WeightA1BridgeActual
import tmp.sheaf.xif.paper.Mzk1P0QHatHaarScalingActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.BadPlacePaperTargetStrictActual
import Mathlib.Tactic

/-! # P1 #1: construct `PaperToS3137A1Data` from the WeightA1 a1Delta theorem

`a1Delta_eq_neg_coefficient_logP_sub_signed` has exactly the RHS required by
`PaperToS3137A1Data.a1_delta_paper`; the only side condition is `0 < s1915LocalDegree`.
Hence A1Data is no longer an unexplained gap (it is constructed given local degree
positivity, which is an explicit small input). -/

noncomputable section
open scoped BigOperators ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1PaperSumsA1DataActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperTargetStrictActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PaperSumsToS3137BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1WeightA1BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P0QHatHaarScalingActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Construct the a1Delta dictionary from the WeightA1 identity; local degree positivity
is the green theorem `local_degree_pos` (no extra hypothesis). -/
noncomputable def paperToS3137A1Data :
    PaperToS3137A1Data (T := T) where
  a1_delta_paper := fun b =>
    a1Delta_eq_neg_coefficient_logP_sub_signed (T := T) (b := b)
      (local_degree_pos (T := T) (b := b))

/-- `PaperToS3137A1Data` is inhabited unconditionally. -/
theorem paperToS3137A1Data_nonempty :
    Nonempty (PaperToS3137A1Data (T := T)) :=
  ⟨paperToS3137A1Data (T := T)⟩

def a1DataRows : List (String × String × String) :=
  [ ("paperToS3137A1Data", "A1Data constructed from a1Delta theorem + green local_degree_pos", "CONSTRUCTED (unconditional)"),
    ("paperToS3137A1Data_nonempty", "Nonempty A1Data (unconditional)", "PROVED") ]

theorem a1DataRows_length : a1DataRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1PaperSumsA1DataActual

end