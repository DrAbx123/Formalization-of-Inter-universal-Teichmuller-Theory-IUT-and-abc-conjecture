/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.Ind3OutputHullQPilotActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import Mathlib.Tactic
/-! # GAP: P4-C Ind3 stage map (named data, no inhabitant) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P4CInd3StageMapActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Ind3OutputHullQPilotActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
structure Ind3StageMapData where
  carrier : Type
  image : Set carrier
  toBlock : carrier → qVFamTensorBlock T b
  compat : ∀ x, x ∈ image → toBlock x ∈ ind3OutputHull (l := l) T b
theorem ind3Image_subset_container (D : Ind3StageMapData (T := T) b) :
    D.toBlock '' D.image ⊆ ind3OutputHull (l := l) T b := by
  rintro y ⟨x, hx, rfl⟩
  exact D.compat x hx
def Ind3StageMapDataRequired : Prop := Nonempty (Ind3StageMapData (T := T) b)
def rows : List String := ["carrier", "image", "toBlock", "compat", "inhabitant NOT constructed"]
theorem rows_length : rows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P4CInd3StageMapActual
end