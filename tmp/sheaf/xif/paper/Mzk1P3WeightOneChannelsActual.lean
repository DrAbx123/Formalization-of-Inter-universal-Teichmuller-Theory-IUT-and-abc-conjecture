import tmp.sheaf.xif.paper.Mzk1C17UnramResidueBridgeActual
import tmp.sheaf.xif.paper.Mzk1P3FinalWeightAssemblyActual
import Mathlib.Tactic

/-! # GREEN: two independent weight=1 channels

Channel D (direct, shehdd): UNRAM=1 + RESIDUE=1 + FINITE + AGREE => weight=1.
Channel F (FLT finrank): FLT global e*f=finrank + factor/finrank comparisons
  + FINITE + AGREE + completion finrank=1 => weight=1.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3WeightOneChannelsActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1C17UnramResidueBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P3FinalWeightAssemblyActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Direct channel: e=f=1 + FINITE + AGREE => weight=1. -/
theorem nativeBadLocalWeight_eq_one_direct_channel
    (b : Bad (nativePlaceSelection T))
    (hfinite : Module.Finite
      ((comap (k := T.arithmetic.Fmod) (nativeBadToKPlace T b)).maximalIdeal.adicCompletionIntegers
        T.arithmetic.Fmod)
      ((nativeBadToKPlace T b).maximalIdeal.adicCompletionIntegers T.arithmetic.K))
    (hagree : localDataAgreesWithPlaceData (k := T.arithmetic.Fmod) (nativeBadToKPlace T b))
    (he : relativeRamificationIndex (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1)
    (hf : relativeResidueDegree (k := T.arithmetic.Fmod) (nativeBadToKPlace T b) = 1) :
    nativeBadLocalWeight T b = 1 :=
  Mzk1C17UnramResidueBridgeActual.nativeBadLocalWeight_eq_one_of_unram_residue_bridge
    (l := l) T b hfinite hagree he hf

/-- FLT finrank channel: FLT global e*f=finrank + comparisons + finrank=1 => weight=1. -/
theorem nativeBadLocalWeight_eq_one_FLT_channel
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
    nativeBadLocalWeight T b = 1 :=
  Mzk1P3FinalWeightAssemblyActual.nativeBadLocalWeight_eq_one_of_FLT_global_finrank_one
    (l := l) T b Kfield Lfield w hfinite hagree hram hres hfin1 hfin

#check nativeBadLocalWeight_eq_one_direct_channel
#check nativeBadLocalWeight_eq_one_FLT_channel
end LeanFormal.IUT.XiFPaper.Mzk1P3WeightOneChannelsActual
end
