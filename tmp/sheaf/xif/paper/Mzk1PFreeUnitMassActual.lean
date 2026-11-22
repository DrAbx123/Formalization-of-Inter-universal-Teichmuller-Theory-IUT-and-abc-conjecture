/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1LocalUnitMassProductActual
import tmp.sheaf.xif.paper.Mzk1BadPlaceUnitMassProductActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import Mathlib.Tactic

/-! # #10 p-free finite-place unit product -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1PFreeUnitMassActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1LocalUnitMassProductActual
open LeanFormal.IUT.XiFPaper.Mzk1BadPlaceUnitMassProductActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem pfree_badPlaceUnitMassProduct_eq_one
    (K : Bad (nativePlaceSelection T) → Type)
    [∀ b, NormedField (K b)] [∀ b, IsUltrametricDist (K b)]
    [∀ b, ProperSpace (K b)] [∀ b, MeasurableSpace (K b)] [∀ b, BorelSpace (K b)] :
    badPlaceUnitMassProduct (T := T) K = 1 :=
  badPlaceUnitMassProduct_eq_one (T := T) K

theorem pfree_rootUnitMassProduct_eq_one :
    badPlaceUnitMassProduct (T := T) (fun b => rootNormedExtension T b) = 1 :=
  badPlaceUnitMassProduct_eq_one (T := T) (fun b => rootNormedExtension T b)

end LeanFormal.IUT.XiFPaper.Mzk1PFreeUnitMassActual
