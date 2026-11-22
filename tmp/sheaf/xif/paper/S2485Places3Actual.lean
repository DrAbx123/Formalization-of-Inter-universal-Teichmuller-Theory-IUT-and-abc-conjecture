import Mathlib

noncomputable section
open scoped NumberField
namespace LeanFormal.IUT.XiFPaper.S2485Places3Actual

def S2485v3 : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.comap Rat.ringOfIntegersEquiv.toRingHom (Ideal.span {(3 : ℤ)})
  isPrime := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : (Ideal.span {(3 : ℤ)}).IsPrime :=
      (Int.ideal_span_isMaximal_of_prime 3).isPrime
    infer_instance
  ne_bot := by
    intro h
    have hcomap_inj : Function.Injective (Ideal.comap Rat.ringOfIntegersEquiv.toRingHom) :=
      Ideal.comap_injective_of_surjective
        (f := Rat.ringOfIntegersEquiv.toRingHom) Rat.ringOfIntegersEquiv.surjective
    have hbot : Ideal.comap Rat.ringOfIntegersEquiv.toRingHom (⊥ : Ideal ℤ) = ⊥ :=
      Ideal.comap_bot_of_injective
        (f := Rat.ringOfIntegersEquiv.toRingHom) Rat.ringOfIntegersEquiv.injective
    have hspan : Ideal.span {(3 : ℤ)} = ⊥ := hcomap_inj (by rw [h, hbot])
    exact (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (3 : ℤ) ≠ 0)) hspan

def S2485p3 : NumberField.FinitePlace ℚ := NumberField.FinitePlace.mk S2485v3
def S2485VModBad : Set (NumberField.FinitePlace ℚ) := {S2485p3}
theorem S2485VModBad_nonempty : S2485VModBad.Nonempty := ⟨S2485p3, rfl⟩
end LeanFormal.IUT.XiFPaper.S2485Places3Actual
end