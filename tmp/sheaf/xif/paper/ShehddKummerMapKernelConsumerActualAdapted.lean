import LeanFormal.IUT.IUTII.Kummer.KummerGaloisClass

/-!
# ShehddKummerMapKernelConsumerActualAdapted — classical Kummer map kernel consumer

STEP 0 prior-art (reuse only; A475 search: Kummer kernel assets found):
* IUTII/Kummer/KummerGaloisClass.lean: kummerRatioHom_eq_one_iff (trivial hom <=>
  fixed root), kummerRatioHom_eq_of_root_mul / _of_pow_eq (root choice independence),
  kummerRootSubgroup, kummerMap, kummer_pow_mem_of_trivial, kummerMap_eq_one_iff
  (kernel = n-th powers, under [FiniteDimensional K L] [IsGalois K L]).

This file packages the classical Kummer injectivity statements as one consumer.  No new
assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddKummerMapKernelConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.KummerGaloisClass

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ} [NeZero n]
variable [FiniteDimensional K L] [IsGalois K L]

/-- **PROVED consumer:** the Kummer map's kernel is exactly the n-th powers in Kˣ
(classical Kummer injectivity), and the map is computed by kummerRatioHom on any chosen
root. -/
theorem kummerMap_kernel_consumer
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    (a : kummerRootSubgroup (K := K) (L := L) (n := n)) :
    (kummerMap hμ a = 1 ↔ ∃ b : Kˣ, b ^ n = (a : Kˣ)) ∧
      kummerMap hμ a =
        kummerRatioHom hμ (Classical.choose a.2) (Classical.choose_spec a.2) :=
  ⟨kummerMap_eq_one_iff hμ a, kummerMap_apply_choose hμ a⟩

/-- **PROVED consumer:** trivial Kummer hom implies the value is an n-th power in Kˣ;
and the hom is unchanged when the chosen root is multiplied by an n-th root of unity. -/
theorem kummer_trivial_and_root_choice_consumer
    (hμ : ∀ ζ : rootsOfUnity n L, ∀ σ : L ≃ₐ[K] L,
      σ ((ζ : Lˣ) : L) = ((ζ : Lˣ) : L))
    {a : Kˣ} (α : Lˣ)
    (hα : α ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (htriv : ∀ σ : L ≃ₐ[K] L, kummerRatioHom hμ α hα σ = 1) :
    (∃ b : Kˣ, b ^ n = a) ∧
      (∀ (α' : Lˣ) (hα' : α' ^ n = Units.map (algebraMap K L).toMonoidHom a)
        (ζ : rootsOfUnity n L), α' = (ζ : Lˣ) * α →
          kummerRatioHom hμ α' hα' = kummerRatioHom hμ α hα) :=
  ⟨kummer_pow_mem_of_trivial hμ α hα htriv,
    fun α' hα' ζ hζ => kummerRatioHom_eq_of_root_mul hμ hα hα' ζ hζ⟩

/-- Row record: reused Kummer-classical laws vs the consumer interface. -/
def kummerMapKernelRows : List (String × String × String) :=
  [ ("trivial hom <=> root fixed by Galois", "REUSED PROVED", "kummerRatioHom_eq_one_iff")
  , ("root-choice independence / multiplicativity", "REUSED PROVED", "kummerRatioHom_eq_of_root_mul / _of_pow_eq / _mul_roots")
  , ("kummerRootSubgroup + kummerMap definition", "REUSED DEF", "kummerRootSubgroup / kummerMap")
  , ("trivial hom => n-th power; kernel = n-th powers", "REUSED PROVED", "kummer_pow_mem_of_trivial / kummerMap_eq_one_iff")
  , ("consumer bundle", "COMPOSED PROVED", "kummerMap_kernel_consumer, kummer_trivial_and_root_choice_consumer") ]

theorem kummerMapKernelRows_length : kummerMapKernelRows.length = 5 := rfl

#check kummerMap_kernel_consumer
#check kummer_trivial_and_root_choice_consumer
#check kummerMapKernelRows_length

end LeanFormal.IUT.XiFPaper.ShehddKummerMapKernelConsumerActualAdapted
end
