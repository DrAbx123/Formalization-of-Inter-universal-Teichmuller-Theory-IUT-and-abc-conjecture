/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3WeightDegreeOneActual
import tmp.sheaf.xif.paper.Mzk1C17ResidueFieldEquivActual
import tmp.sheaf.xif.paper.Mzk1C17QCANDOrderResidueActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import Mathlib.Tactic

/-!
# P6-E4: residueFieldEquiv => localResidueDegree=1 => nativeBadLocalWeight=1

Status: CONDITIONAL.  Chains the residue-field equivalence sufficient input
through the local residue degree to qpilot's GAP-PC-WEIGHT conclusion.
No actual residue-field isomorphism is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17ResidueWeightChainActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneActual
open LeanFormal.IUT.XiFPaper.Mzk1C17ResidueFieldEquivActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Residue-field equivalence at the section place gives local residue degree 1. -/
theorem localResidueDegree_eq_one_of_residueFieldEquiv
    (b : Bad (nativePlaceSelection T))
    (h : ResidueFieldEquiv
      (p := (comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.asIdeal)
      (P := (nativeBadToKPlace T b).maximalIdeal.asIdeal)) :
    localResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1 := by
  change Ideal.inertiaDeg'
    (comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.asIdeal
    (nativeBadToKPlace T b).maximalIdeal.asIdeal = 1
  exact inertiaDeg'_eq_one_of_residueFieldEquiv h

/-- Full conditional GAP-PC-WEIGHT chain. -/
theorem nativeBadLocalWeight_eq_one_of_residueFieldEquiv
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (hunram : relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
    (hres : ResidueFieldEquiv
      (p := (comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.asIdeal)
      (P := (nativeBadToKPlace T b).maximalIdeal.asIdeal)) :
    nativeBadLocalWeight T b = 1 :=
  nativeBadLocalWeight_eq_one_of_unram_residue (l := l) T b hfinite hagree hunram
    (by
      simpa [localResidueDegree, relativeResidueDegree]
        using localResidueDegree_eq_one_of_residueFieldEquiv T b hres)

def residueWeightRows : List (String × String × String) :=
  [ ("localResidueDegree_eq_one_of_residueFieldEquiv", "residue equiv => local residue degree 1", "PROVED conditional"),
    ("nativeBadLocalWeight_eq_one_of_residueFieldEquiv", "residue equiv + unram/finite/agree => weight 1", "PROVED conditional") ]
theorem residueWeightRows_length : residueWeightRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1C17ResidueWeightChainActual
