/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Paper312StatementActual
import tmp.sheaf.xif.paper.S2717Cor312FullTargetActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.S2711PaperMultiUnconditionalActual
import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.xif.paper.QPilotObjectActual
import Mathlib.Tactic
/-! # C3-I/VALUE closure: Paper312Statement at the actual donor C3 -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Paper312ActualDonorC3Actual
open LeanFormal.IUT LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
universe u
variable (R : S1280RemainingClauses (S2678PaperUnconditionalHcompActual.fiveLabel))
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))
abbrev ActualDonorC3 : SourcePilotRegionData
    (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D
variable (P : PaperQPilotObjectActual
  (I := S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))
theorem paper312Statement_actualDonorC3_iff :
    Paper312Statement (C3 := S2717C3 R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D) P ↔
      qThetaPilotLogVolumeComparison (C3 := S2717C3 R redCompat hredCompat
        torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D) P :=
  paper312Statement_iff_qThetaPilotLogVolumeComparison _ P
theorem paper312Statement_actualDonorC3_iff_neg_abs :
    Paper312Statement (C3 := S2717C3 R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D) P ↔
      -|Real.log (‖P.line.C3.q.q‖)| ≤
        thetaPilotHullLogVolumeReal (C3 := S2717C3 R redCompat hredCompat
          torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D) :=
  paper312Statement_iff_neg_abs_le _ P
def rows : List String := ["Paper312Statement at actual donor C3", "iff qThetaPilotLogVolumeComparison", "iff -|log q| form", "P inhabitant still required"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1Paper312ActualDonorC3Actual
end