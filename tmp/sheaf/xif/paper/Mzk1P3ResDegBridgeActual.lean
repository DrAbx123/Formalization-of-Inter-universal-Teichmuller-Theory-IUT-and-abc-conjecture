/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3ResNormSlackActual
import tmp.sheaf.xif.paper.Mzk1P3ArithmeticRelativeBridgeActual
import tmp.sheaf.xif.paper.BaseQFamilyActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorResNormActual
import Mathlib.Tactic

/-! # P3 RESDEG bridge: relative residue degree one iff residue-norm equality at the bad section place

Combines the rfl bridge (localResidueDegree = relativeResidueDegree) with the green
ResNormSlack equivalence.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3ResDegBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1P3ResNormSlackActual
open LeanFormal.IUT.XiFPaper.Mzk1P3ArithmeticRelativeBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorResNormActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem relativeResidueDegree_native_eq_one_iff_residueNormBase_eq
    (b : Bad (nativePlaceSelection T)) :
    relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1
      ↔ residueNormBase (nativeBaseSectionPlace T b) = residueNormBase (b.1) := by
  rw [← localResidueDegree_eq_one_iff_relativeResidueDegree_eq_one
    (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b)]
  rw [localResidueDegree_eq_one_iff_residueNormBase_eq
    (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b)]
  rw [nativeBaseSectionPlace_comap]

def ResDegTarget : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1

theorem resDegTarget_iff_norm_eq_all :
    ResDegTarget T ↔
      ∀ b : Bad (nativePlaceSelection T),
        residueNormBase (nativeBaseSectionPlace T b) = residueNormBase (b.1) :=
  ⟨fun h b => (relativeResidueDegree_native_eq_one_iff_residueNormBase_eq T b).mp (h b),
    fun h b => (relativeResidueDegree_native_eq_one_iff_residueNormBase_eq T b).mpr (h b)⟩

def resDegBridgeRows : List (String × String × String) :=
  [ ("relativeResidueDegree_native_eq_one_iff_residueNormBase_eq", "f=1 iff residue norm equality", "PROVED (green chain)"),
    ("ResDegTarget", "all bad section places have relative f = 1", "DEF (target Prop)"),
    ("resDegTarget_iff_norm_eq_all", "quantified equivalence", "PROVED (green chain)") ]

theorem resDegBridgeRows_length : resDegBridgeRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3ResDegBridgeActual

end
