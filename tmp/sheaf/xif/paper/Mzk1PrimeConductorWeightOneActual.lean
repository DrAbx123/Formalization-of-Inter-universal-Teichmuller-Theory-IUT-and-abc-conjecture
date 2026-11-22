/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorUnconditionalActual
import Mathlib.Tactic

/-! # GAP-PC-WEIGHT: unit actual local weight from tame local data

The actual weight is `(localCompletionDegree)⁻¹`; the local completion degree is
the finrank of the completed field extension.  Using
`FinitePlaceCompletionDegree.finrank_adicCompletion_eq_relativeCompletionDegree`,
the degree is the library relative degree `e·f`.  Hence:

* if the completed valuation-ring extension is finite (GAP-PC-FINITE) and the
  local completed data agrees with the number-ring place data (GAP-PC-AGREE),
* and the place extension is unramified with residue degree one
  (GAP-PC-UNRAM, GAP-PC-RESIDUE: the prime-conductor tame case `l ∤ e_p`),
then the actual local weight is exactly 1.

No sorry/axiom; every missing mathematical input is a named hypothesis/Prop.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorWeightOneActual

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorUnconditionalActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **GAP-PC-WEIGHT reduction.**  Under the three named local inputs
(finiteness of the completed valuation-ring extension, agreement of local data
with place data, and `e = f = 1`), the actual native local weight is 1. -/
theorem nativeBadLocalWeight_eq_one_of_tame_data
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod)
      (nativeBadToKPlace T b))
    (hram : relativeRamificationIndex (k := T.arithmetic.Fmod)
      (nativeBadToKPlace T b) = 1)
    (hres : relativeResidueDegree (k := T.arithmetic.Fmod)
      (nativeBadToKPlace T b) = 1) :
    nativeBadLocalWeight T b = 1 := by
  have hdegRel : relativeCompletionDegree (k := T.arithmetic.Fmod)
      (nativeBadToKPlace T b) = 1 :=
    (relativeCompletionDegree_eq_one_iff (k := T.arithmetic.Fmod)
      (nativeBadToKPlace T b)).mpr ⟨hram, hres⟩
  have hfin_eq := finrank_adicCompletion_eq_relativeCompletionDegree
    (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) hfinite hagree
  have hdeg : localCompletionDegree T.arithmetic (nativeBadToKPlace T b) = 1 := by
    unfold localCompletionDegree
    rw [hfin_eq, hdegRel]
  exact nativeBadLocalWeight_eq_one_of_localCompletionDegree_one T b hdeg

/-- Expected prime-conductor tame specialisation: the relative place extension at a
bad place is unramified of residue degree one.  This is the precise remaining input
(GAP-PC-UNRAM/GAP-PC-RESIDUE), not asserted. -/
def PrimeConductorTameLocalData (b : Bad (nativePlaceSelection T)) : Prop :=
  relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1 ∧
    relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1

/-- Consumer form: GAP-PC-FINITE + GAP-PC-AGREE + `PrimeConductorTameLocalData`
give the unit actual local weight. -/
theorem nativeBadLocalWeight_eq_one_of_tame
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod)
      (nativeBadToKPlace T b))
    (htame : PrimeConductorTameLocalData (l := l) T b) :
    nativeBadLocalWeight T b = 1 :=
  nativeBadLocalWeight_eq_one_of_tame_data T b hfinite hagree htame.1 htame.2

/-- Status rows. -/
def weightOneRows : List (String × String × String) :=
  [ ("localCompletionDegree", "finrank of completed field extension", "DEF"),
    ("nativeBadLocalWeight_eq_one_of_localCompletionDegree_one", "degree 1 => weight 1", "PROVED (imported)"),
    ("nativeBadLocalWeight_eq_one_of_tame_data", "finite + local-data agreement + e=f=1 => weight 1", "PROVED (conditional)"),
    ("nativeBadLocalWeight_eq_one_of_tame", "consumer form with PrimeConductorTameLocalData", "PROVED (conditional)"),
    ("PrimeConductorTameLocalData", "relative e = 1 and f = 1 at the bad place", "GAP-PC-UNRAM/GAP-PC-RESIDUE (input Prop)"),
    ("hfinite", "Module.Finite of completed valuation rings", "GAP-PC-FINITE (content input)"),
    ("hagree", "localDataAgreesWithPlaceData", "GAP-PC-AGREE (content input)") ]

theorem weightOneRows_length : weightOneRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorWeightOneActual

end
