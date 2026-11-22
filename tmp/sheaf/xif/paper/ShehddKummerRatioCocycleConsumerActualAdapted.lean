import LeanFormal.IUT.IUTII.Kummer.KummerGaloisClass

/-!
# ShehddKummerRatioCocycleConsumerActualAdapted — Kummer ratio Galois cocycle consumer

STEP 0 prior-art (reuse only; A475 search: Kummer Galois class found):
* IUTII/Kummer/KummerGaloisClass.lean (namespace KummerGaloisClass):
  kummerRatio (σ α / α ∈ μ_n), kummerRatio_pow_eq_one, kummerRatio_one,
  kummerRatio_mul (multiplicativity in the Galois variable under hμ),
  kummerRatioHom (Gal(L/K) →* μ_n(L)), kummerRatio_galois_fixed(_units).

This file packages the Kummer ratio as a Galois cocycle consumer: the hom's unit and
multiplication laws, n-torsion of every ratio, and the trivial ratio at 1.  No new
assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddKummerRatioCocycleConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.KummerGaloisClass

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ} [NeZero n]

/-- **PROVED consumer:** under the root-of-unity fixedness hypothesis, `σ ↦ σα/α` is a
monoid hom `Gal(L/K) →* μ_n(L)`, each ratio is an n-th root of unity, and the identity
Galois element gives ratio 1. -/
theorem kummerRatio_cocycle_consumer
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a) :
    (kummerRatioHom hμ α hα (1 : L ≃ₐ[K] L) = 1) ∧
      (∀ σ τ : L ≃ₐ[K] L,
        kummerRatioHom hμ α hα (σ * τ) =
          kummerRatioHom hμ α hα σ * kummerRatioHom hμ α hα τ) ∧
        (∀ σ : L ≃ₐ[K] L, kummerRatio α hα σ ^ n = 1) ∧
          kummerRatio α hα (1 : L ≃ₐ[K] L) = 1 :=
  ⟨(kummerRatioHom hμ α hα).map_one,
    fun σ τ => (kummerRatioHom hμ α hα).map_mul σ τ,
    fun σ => kummerRatio_pow_eq_one α hα σ,
    kummerRatio_one α hα⟩

/-- Row record: reused Kummer-class laws vs the consumer interface. -/
def kummerRatioCocycleRows : List (String × String × String) :=
  [ ("ratio definition in μ_n", "REUSED DEF", "KummerGaloisClass.kummerRatio")
  , ("n-torsion of each ratio", "REUSED PROVED", "kummerRatio_pow_eq_one")
  , ("trivial at identity / multiplicative in Galois variable", "REUSED PROVED", "kummerRatio_one / kummerRatio_mul")
  , ("monoid hom Gal -> μ_n", "REUSED DEF/PROVED", "kummerRatioHom (map_one'/map_mul')")
  , ("consumer bundle", "COMPOSED PROVED", "kummerRatio_cocycle_consumer") ]

theorem kummerRatioCocycleRows_length : kummerRatioCocycleRows.length = 5 := rfl

#check kummerRatio_cocycle_consumer
#check kummerRatioCocycleRows_length

end LeanFormal.IUT.XiFPaper.ShehddKummerRatioCocycleConsumerActualAdapted
end
