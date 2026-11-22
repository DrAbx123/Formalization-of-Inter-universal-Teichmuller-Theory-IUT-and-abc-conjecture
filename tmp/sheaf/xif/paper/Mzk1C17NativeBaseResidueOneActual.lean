/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17ResidueFieldEquivActual
import tmp.sheaf.xif.paper.BaseQFamilyActual
import tmp.sheaf.xif.paper.Mzk1C17QCANDResNormComapActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17NativeBaseResidueOneActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueFieldEquivActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDResNormComapActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
def NativeBaseResidueFieldEquivInput : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    ResidueFieldEquiv
      (p := (comap (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b)).maximalIdeal.asIdeal)
      (P := (nativeBaseSectionPlace T b).maximalIdeal.asIdeal)
theorem localResidueDegree_nativeBase_eq_one_of_residueFieldEquiv
    (b : Bad (nativePlaceSelection T))
    (h : ResidueFieldEquiv
      (p := (comap (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b)).maximalIdeal.asIdeal)
      (P := (nativeBaseSectionPlace T b).maximalIdeal.asIdeal)) :
    localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1 := by
  change Ideal.inertiaDeg'
    (comap (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b)).maximalIdeal.asIdeal
    (nativeBaseSectionPlace T b).maximalIdeal.asIdeal = 1
  exact inertiaDeg'_eq_one_of_residueFieldEquiv h
theorem localResidueDegree_nativeBase_eq_one_of_input
    (h : NativeBaseResidueFieldEquivInput T) :
    ∀ b : Bad (nativePlaceSelection T),
      localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1 :=
  fun b => localResidueDegree_nativeBase_eq_one_of_residueFieldEquiv T b (h b)


end LeanFormal.IUT.XiFPaper.Mzk1C17NativeBaseResidueOneActual
