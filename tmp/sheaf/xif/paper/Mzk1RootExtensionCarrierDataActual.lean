/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import Mathlib.Tactic

/-! # #10: exact carrier data needed for normalized root-extension unit mass -/
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1RootExtensionCarrierDataActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Exact missing carrier data: measurable-space and sigma-finiteness instances on
the root extensions, so that `Measure.pi` of normalized local measures can be formed. -/
structure RootExtensionCarrierData where
  sigmaFinite : ∀ b : Bad (nativePlaceSelection T),
    SigmaFinite (rootExtensionHaar T b)

def RootExtensionCarrierDataRequired : Prop := Nonempty (RootExtensionCarrierData (T := T))

def rootCarrierRows : List (String × String) :=
  [ ("RootExtensionCarrierData", "MeasurableSpace + SigmaFinite for each rootNormedExtension"),
    ("normalizedRootExtensionHaar", "constructible once data supplied"),
    ("normalized UnitMass=1", "conditional on carrier data; Measure.pi needs SigmaFinite"),
    ("actual s1915UnitMass=1", "GAP: additive rootExtensionHaar unnormalized") ]
theorem rootCarrierRows_length : rootCarrierRows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1RootExtensionCarrierDataActual
