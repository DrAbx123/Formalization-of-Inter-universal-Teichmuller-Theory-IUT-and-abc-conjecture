import tmp.sheaf.xif.paper.Mzk1P3FLTFinrankSupplyActual
import tmp.sheaf.xif.paper.Mzk1P3WeightDegreeOneFinrankActual
import tmp.sheaf.xif.paper.Mzk1P3AgreeDegreeActual
import Mathlib.Tactic

/-! # CONDITIONAL: FLT global e*f=finrank + finrank=1 => weight=1

Composition of:
  FLTCompletionFinrankInput_of_FLT_global
  nativeBadLocalWeight_eq_one_of_FLT_finrank_one
The factor/finrank comparison hypotheses are the explicit bridge data.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3FinalWeightAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1P3AgreeDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1P3FLTCompletionInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P3FLTFinrankSupplyActual
open LeanFormal.IUT.XiFPaper.Mzk1P3WeightDegreeOneFinrankActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Final conditional assembly: FLT global e*f=finrank, factor comparisons,
our-completion/FLT-completion finrank comparison, FINITE+AGREE, and
our completion finrank one imply nativeBadLocalWeight=1. -/
theorem nativeBadLocalWeight_eq_one_of_FLT_global_finrank_one
    (b : Bad (nativePlaceSelection T))
    {A : Type*} (Kfield : Type*) (Lfield : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Field Kfield] [Field Lfield]
    [Algebra A Kfield] [IsFractionRing A Kfield] [Algebra B Lfield] [IsDedekindDomain A]
    [Algebra Kfield Lfield] [Algebra A Lfield] [IsScalarTower A B Lfield]
    [IsScalarTower A Kfield Lfield] [Algebra.IsIntegral A B] [IsFractionRing B Lfield]
    [IsDedekindDomain B]
    {v : IsDedekindDomain.HeightOneSpectrum A}
    (w : IsDedekindDomain.HeightOneSpectrum.Extension B v)
    [FiniteDimensional Kfield Lfield] [Module.Finite A B]
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (hram : relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) =
      (w.1.asIdeal).ramificationIdx A)
    (hres : relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) =
      (w.1.asIdeal).inertiaDeg A)
    (hfin1 : Module.finrank
        ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletion
          T.arithmetic.Fmod)
        ((nativeBadToKPlace T b).maximalIdeal.adicCompletion T.arithmetic.K) =
      Module.finrank (IsDedekindDomain.HeightOneSpectrum.adicCompletion Kfield v)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion Lfield w.1))
    (hfin : Module.finrank
        ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletion
          T.arithmetic.Fmod)
        ((nativeBadToKPlace T b).maximalIdeal.adicCompletion T.arithmetic.K) = 1) :
    nativeBadLocalWeight T b = 1 := by
  have hFLT : FLTCompletionFinrankInput (k := T.arithmetic.Fmod) (K := T.arithmetic.K)
      (nativeBadToKPlace T b) :=
    FLTCompletionFinrankInput_of_FLT_global Kfield Lfield w
      (nativeBadToKPlace T b) hram hres hfin1
  exact nativeBadLocalWeight_eq_one_of_FLT_finrank_one (l := l) T b
    hfinite hagree hFLT hfin

#check nativeBadLocalWeight_eq_one_of_FLT_global_finrank_one
end LeanFormal.IUT.XiFPaper.Mzk1P3FinalWeightAssemblyActual
end
