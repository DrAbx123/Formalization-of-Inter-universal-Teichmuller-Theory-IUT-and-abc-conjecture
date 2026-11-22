import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Tactic
/-!
# F7 local-global different/discriminant dictionary (route §8.5), foundation layer

Goal (next layer): `v_p(|disc K|) = Σ_{P | p} v_P(𝔇) · f(P|p)`.
This file proves the foundation facts used by that transport:
the different ideal is nonzero, its normalized-factor product is itself,
its absolute norm is `|disc K|`, and the norm is the multiset product of
the absolute norms of its normalized factors — all from Mathlib donors.

Lead lane: H-T / P8-P.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1F7DiscLocalGlobalActual

open Module Ideal UniqueFactorizationMonoid NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

theorem differentIdeal_ne_bot_K : differentIdeal ℤ (𝓞 K) ≠ ⊥ :=
  differentIdeal_ne_bot

theorem prod_normalizedFactors_differentIdeal :
    (normalizedFactors (differentIdeal ℤ (𝓞 K))).prod = differentIdeal ℤ (𝓞 K) :=
  Ideal.prod_normalizedFactors_eq_self differentIdeal_ne_bot_K

theorem absNorm_differentIdeal_eq_discr :
    Ideal.absNorm (differentIdeal ℤ (𝓞 K)) = (NumberField.discr K).natAbs :=
  NumberField.absNorm_differentIdeal (K := K) (𝒪 := 𝓞 K)

theorem absNorm_differentIdeal_eq_multiset_prod :
    Ideal.absNorm (differentIdeal ℤ (𝓞 K)) =
      ((normalizedFactors (differentIdeal ℤ (𝓞 K))).map Ideal.absNorm).prod := by
  conv_lhs => rw [← prod_normalizedFactors_differentIdeal]
  exact map_multiset_prod Ideal.absNorm _

theorem discr_natAbs_factorization_eq_absNorm :
    ∀ p : ℕ, (NumberField.discr K).natAbs.factorization p =
      (Ideal.absNorm (differentIdeal ℤ (𝓞 K))).factorization p := by
  intro p
  rw [absNorm_differentIdeal_eq_discr]

end LeanFormal.IUT.XiFPaper.Mzk1F7DiscLocalGlobalActual

