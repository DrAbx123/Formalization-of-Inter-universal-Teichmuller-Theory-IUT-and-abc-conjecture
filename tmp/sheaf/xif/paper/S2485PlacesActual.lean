import Mathlib

noncomputable section
open scoped NumberField
namespace LeanFormal.IUT.XiFPaper.S2485PlacesActual

def S2485v5 : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.comap Rat.ringOfIntegersEquiv.toRingHom (Ideal.span {(5 : ℤ)})
  isPrime := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    haveI : (Ideal.span {(5 : ℤ)}).IsPrime :=
      (Int.ideal_span_isMaximal_of_prime 5).isPrime
    infer_instance
  ne_bot := by
    intro h
    have hcomap_inj : Function.Injective (Ideal.comap Rat.ringOfIntegersEquiv.toRingHom) :=
      Ideal.comap_injective_of_surjective
        (f := Rat.ringOfIntegersEquiv.toRingHom) Rat.ringOfIntegersEquiv.surjective
    have hbot : Ideal.comap Rat.ringOfIntegersEquiv.toRingHom (⊥ : Ideal ℤ) = ⊥ :=
      Ideal.comap_bot_of_injective
        (f := Rat.ringOfIntegersEquiv.toRingHom) Rat.ringOfIntegersEquiv.injective
    have hspan : Ideal.span {(5 : ℤ)} = ⊥ := hcomap_inj (by rw [h, hbot])
    exact (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (5 : ℤ) ≠ 0)) hspan

def S2485p5 : NumberField.FinitePlace ℚ := NumberField.FinitePlace.mk S2485v5

def S2485VModBad : Set (NumberField.FinitePlace ℚ) := {S2485p5}
theorem S2485VModBad_nonempty : S2485VModBad.Nonempty := ⟨S2485p5, rfl⟩

#print axioms S2485VModBad_nonempty

end LeanFormal.IUT.XiFPaper.S2485PlacesActual
end