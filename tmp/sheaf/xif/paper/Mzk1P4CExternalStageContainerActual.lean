/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperFaithfulHullP4Actual
import tmp.sheaf.xif.paper.Ind3OutputHullQPilotActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

/-! # GAP: P4-C external Ind2/Ind3 stage image container

Ind2/Ind3 stage images live on S1902Carrier, not on qVFamTensorBlock.  This file records
an external container with a named map to the block; no map is constructed.
Conditional only: a structure field, not a theorem that the required map exists.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P4CExternalStageContainerActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Ind3OutputHullQPilotActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperFaithfulHullP4Actual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Named external stage-image container: a carrier, its image set, and a map to the
qVFam block with compatibility into ind3OutputHull.  No inhabitant is constructed. -/
structure ExternalStageImageData where
  carrier : Type
  image : Set carrier
  toBlock : carrier → qVFamTensorBlock T b
  compat : ∀ x, x ∈ image → toBlock x ∈ ind3OutputHull (l := l) T b

theorem externalImage_subset_blockContainer
    (D : ExternalStageImageData (T := T) b) :
    D.toBlock '' D.image ⊆ ind3OutputHull (l := l) T b := by
  rintro y ⟨x, hx, rfl⟩
  exact D.compat x hx

def ExternalStageImageDataRequired : Prop :=
  Nonempty (ExternalStageImageData (T := T) b)

def rows : List (String × String) :=
  [ ("ExternalStageImageData", "named carrier/image/toBlock/compat"),
    ("externalImage_subset_blockContainer", "conditional"),
    ("stage->block map inhabitant", "GAP") ]

theorem rows_length : rows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P4CExternalStageContainerActual

end