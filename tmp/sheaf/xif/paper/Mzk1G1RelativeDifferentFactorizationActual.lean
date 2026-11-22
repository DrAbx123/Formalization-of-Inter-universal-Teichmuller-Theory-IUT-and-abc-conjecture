/- H-T 8.2 (batch4c): factorization of the relative different norm: the absolute norm of
differentIdeal(O_K,O_L) is the product of absNorm(P) over the normalized factors, and for a
prime P the norm is absNorm(under P) ^ inertiaDeg.  These are the two actual Mathlib-based
ingredients for the relative-different norm identity (batch4a hlog). -/
import tmp.sheaf.xif.paper.Mzk1G1PlaceDataActual
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentFactorizationActual

open NumberField
open UniqueFactorizationMonoid
open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual

universe u

section

variable {K : Type u} [Field K] [NumberField K]
variable {L : Type u} [Field L] [NumberField L] [Algebra K L]
variable [Module.Finite (𝓞 K) (𝓞 L)]

/-- The absolute norm of the relative different is the product of the absolute norms of its
normalized prime factors (Dedekind factorization of ideals + multiplicativity of absNorm). -/
theorem absNorm_differentIdeal_eq_prod :
    Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) =
      ((normalizedFactors (differentIdeal (𝓞 K) (𝓞 L))).map Ideal.absNorm).prod := by
  have hI : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI]
  rw [map_multiset_prod]

/-- For a prime ideal P of O_L, the absolute norm is absNorm(under P) to the inertia degree
over O_K (Mathlib theorem absNorm_eq_pow_inertiaDeg'_of_liesOver). -/
theorem absNorm_prime_eq_pow_inertiaDeg (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    Ideal.absNorm P =
      Ideal.absNorm (P.under (𝓞 K)) ^ (P.under (𝓞 K)).inertiaDeg' P := by
  have hp_ne_bot : P.under (𝓞 K) ≠ ⊥ := by
    intro h
    haveI : P.LiesOver (⊥ : Ideal (𝓞 K)) := ⟨h.symm⟩
    exact hP (Ideal.eq_bot_of_liesOver_bot (A := 𝓞 K) P)
  exact Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P (P.under (𝓞 K))
    (Ideal.IsPrime.under (𝓞 K) P) hp_ne_bot

end

#print axioms absNorm_differentIdeal_eq_prod
#print axioms absNorm_prime_eq_pow_inertiaDeg
end LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentFactorizationActual
