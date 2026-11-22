import tmp.sheaf.xif.paper.Mzk1P3FLTMultiplicityActual
import tmp.sheaf.xif.paper.Mzk1P3FLTCompletionInputActual
import Mathlib.Tactic

/-! # CONDITIONAL: fill FLTCompletionFinrankInput from FLT global e*f=finrank

The FLT theorem gives global e*f=finrank for ring-of-integers completions.
The remaining named comparisons are:
  relativeRamificationIndex place = w.asIdeal.ramificationIdx A
  relativeResidueDegree place = w.asIdeal.inertiaDeg A
  our completion finrank = FLT adicCompletion finrank
These are the exact bridge data needed to fill FLTCompletionFinrankInput.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3FLTFinrankSupplyActual

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P3FLTCompletionInputActual
open LeanFormal.IUT.XiFPaper.Mzk1P3FLTMultiplicityActual

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- Conditional fill of FLTCompletionFinrankInput using FLT global multiplicity
and the exact factor/finrank comparisons. -/
theorem FLTCompletionFinrankInput_of_FLT_global
    {A : Type*} (Kfield : Type*) (Lfield : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Field Kfield] [Field Lfield]
    [Algebra A Kfield] [IsFractionRing A Kfield] [Algebra B Lfield] [IsDedekindDomain A]
    [Algebra Kfield Lfield] [Algebra A Lfield] [IsScalarTower A B Lfield]
    [IsScalarTower A Kfield Lfield] [Algebra.IsIntegral A B] [IsFractionRing B Lfield]
    [IsDedekindDomain B]
    {v : IsDedekindDomain.HeightOneSpectrum A}
    (w : IsDedekindDomain.HeightOneSpectrum.Extension B v)
    [FiniteDimensional Kfield Lfield] [Module.Finite A B]
    (place : NumberField.FinitePlace K)
    (hram : relativeRamificationIndex (k := k) place = (w.1.asIdeal).ramificationIdx A)
    (hres : relativeResidueDegree (k := k) place = (w.1.asIdeal).inertiaDeg A)
    (hfin1 : Module.finrank
        ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) =
      Module.finrank (IsDedekindDomain.HeightOneSpectrum.adicCompletion Kfield v)
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion Lfield w.1)) :
    FLTCompletionFinrankInput (k := k) (K := K) place := by
  unfold FLTCompletionFinrankInput
  rw [hram, hres, hfin1]
  exact FLT_ramificationIdx_mul_inertiaDeg_eq_finrank Kfield Lfield w

#check FLTCompletionFinrankInput_of_FLT_global
end LeanFormal.IUT.XiFPaper.Mzk1P3FLTFinrankSupplyActual
end
