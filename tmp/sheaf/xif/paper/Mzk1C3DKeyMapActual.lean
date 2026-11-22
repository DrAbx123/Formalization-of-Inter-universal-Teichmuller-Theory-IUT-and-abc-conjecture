/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3DIndexDataActual
import tmp.sheaf.xif.paper.S2717Cor312FullTargetActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import Mathlib.Tactic
/-! # GAP-P7-THETA-D: actual C3D key map at S2717C3 ... D -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1C3DKeyMapActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.Mzk1C3DIndexDataActual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
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
def actualDonorC3 : SourcePilotRegionData
    (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D
def actualC3DKeyMap : C3DIndexData (C3 := actualDonorC3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D) where
  dIndex := (actualDonorC3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D).tensorIndex
  indexEquiv := Equiv.refl _
  dPlaceIndex := (actualDonorC3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D).tensorPlaceIndex
  dPlaces := (actualDonorC3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D).tensorPlaces
  dTuple := (actualDonorC3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D).tensorTuple
theorem actualC3DKeyMap_indexEquiv :
    (actualC3DKeyMap R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D).indexEquiv
      = Equiv.refl _ := rfl
def rows : List String := ["dIndex", "indexEquiv := refl", "dPlaceIndex", "dPlaces", "dTuple", "ACTUAL at S2717C3...D"]
theorem rows_length : rows.length = 6 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C3DKeyMapActual
end