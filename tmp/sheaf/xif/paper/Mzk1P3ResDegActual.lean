/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3ResNormSlackActual
import tmp.sheaf.xif.paper.BaseQFamilyActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorResNormActual
import Mathlib.Tactic

/-! # P3 RESDEG: equivalence between residue degree one and residue-norm equality at the bad section place

CONDITIONAL reduction using green ResNormSlack equivalence.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3ResDegActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1P3ResNormSlackActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorResNormActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem resDeg_iff_norm_eq (b : Bad (nativePlaceSelection T)) :
    localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1
      ↔ residueNormBase (nativeBaseSectionPlace T b) = residueNormBase (b.1) := by
  rw [localResidueDegree_eq_one_iff_residueNormBase_eq
    (k := T.arithmetic.Fmod) (K := T.arithmetic.K) (nativeBaseSectionPlace T b),
    nativeBaseSectionPlace_comap]

def ResDegData : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    localResidueDegree (k := T.arithmetic.Fmod) (nativeBaseSectionPlace T b) = 1

theorem resDeg_iff_norm_eq_all :
    ResDegData T ↔
      ∀ b : Bad (nativePlaceSelection T),
        residueNormBase (nativeBaseSectionPlace T b) = residueNormBase (b.1) :=
  ⟨fun h b => (resDeg_iff_norm_eq T b).mp (h b),
    fun h b => (resDeg_iff_norm_eq T b).mpr (h b)⟩

end LeanFormal.IUT.XiFPaper.Mzk1P3ResDegActual

end
