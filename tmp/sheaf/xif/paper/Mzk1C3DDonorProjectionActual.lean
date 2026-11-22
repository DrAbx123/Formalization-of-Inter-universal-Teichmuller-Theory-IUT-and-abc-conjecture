/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3DKeyMapActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import Mathlib.Tactic
/-! # GAP-P7-THETA-D B4.1: actual donor D is the dictionary right end -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1C3DDonorProjectionActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.Mzk1C3DIndexDataActual
open LeanFormal.IUT.XiFPaper.Mzk1C3DKeyMapActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
universe u
variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))
theorem actualDonorC3_tensorIndex_eq (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)) :
    (actualDonorC3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D).tensorIndex = D.tensorIndex := rfl
theorem actualDonorC3_tensorPlaceIndex_eq :
    (actualDonorC3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D).tensorPlaceIndex = D.tensorPlaceIndex := rfl
theorem actualDonorC3_tensorPlaces_eq :
    (actualDonorC3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D).tensorPlaces = D.tensorPlaces := rfl
theorem actualDonorC3_tensorTuple_eq :
    (actualDonorC3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D).tensorTuple = D.tensorTuple := rfl
theorem actualC3DKeyMap_dIndex_eq_D :
    (actualC3DKeyMap R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D).dIndex = D.tensorIndex := rfl
theorem actualC3DKeyMap_dPlaces_eq_D :
    (actualC3DKeyMap R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D).dPlaces = D.tensorPlaces := rfl
theorem actualC3DKeyMap_dTuple_eq_D :
    (actualC3DKeyMap R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D).dTuple = D.tensorTuple := rfl
def rows : List String := ["C3.tensorIndex = D.tensorIndex", "C3.tensorPlaceIndex = D.tensorPlaceIndex", "C3.tensorPlaces = D.tensorPlaces", "C3.tensorTuple = D.tensorTuple", "dictionary right end = D"]
theorem rows_length : rows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C3DDonorProjectionActual
end