/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3AgreeDegreeActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1 finite-place f_v alignment with localCompletionDegree -/
noncomputable section
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1P3AgreeDegreeActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P1FinitePlaceFvActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem nativeBad_localCompletionDegree_eq_relativeDegree
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)) :
    localCompletionDegree T.arithmetic (nativeBadToKPlace T b) =
      relativeCompletionDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) :=
  localCompletionDegree_eq_relativeCompletionDegree_of_agree T.arithmetic (nativeBadToKPlace T b) hfinite hagree
def finitePlaceFvRows : List (String × String) :=
  [ ("nativeBad_localCompletionDegree_eq_relativeDegree", "f_v = relativeCompletionDegree under FINITE/AGREE"),
    ("hfinite left module finite", "input"),
    ("hagree localDataAgreesWithPlaceData", "input") ]
theorem finitePlaceFvRows_length : finitePlaceFvRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P1FinitePlaceFvActual
