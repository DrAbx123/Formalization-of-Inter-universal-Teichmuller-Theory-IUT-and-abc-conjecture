import tmp.sheaf.n8.closure.PaperKfUniformizerRelationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.PaperKfDVRGeneric
open LeanFormal.IUT.N8Closure.PaperKfHaarNormActual
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual

noncomputable section

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

local instance : MeasurableSpace (PaperKf S) := borel _
local instance : BorelSpace (PaperKf S) := ⟨rfl⟩
local instance : IsDiscreteValuationRing (Integers (PaperKf S)) :=
  LeanFormal.IUT.LocalFieldLogarithm.isDiscreteValuationRingIntegers (K := PaperKf S) (p := pNat S)

example : ‖((paperUniformizer S : Integers (PaperKf S)) : PaperKf S)‖ < 1 := by
  have hle : ‖((paperUniformizer S : Integers (PaperKf S)) : PaperKf S)‖ ≤ 1 :=
    (mem_integers_iff _).mp (paperUniformizer S).property
  have hne : ‖((paperUniformizer S : Integers (PaperKf S)) : PaperKf S)‖ ≠ 1 := by
    intro hnorm
    have hunit : IsUnit (paperUniformizer S) := by
      rw [Valued.integer.isUnit_iff_norm_eq_one]
      simpa using hnorm
    exact (paperUniformizer_irreducible S).not_unit hunit
  exact lt_of_le_of_ne hle hne

end
