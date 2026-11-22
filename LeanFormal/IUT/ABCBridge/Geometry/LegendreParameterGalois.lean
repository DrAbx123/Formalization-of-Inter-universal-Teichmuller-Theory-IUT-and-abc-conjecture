import LeanFormal.IUT.ABCBridge.Geometry.LegendreQuadraticParameterFields
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Coset.Card

/-!
# Galois structure of the actual Legendre parameter field

The field used here is the previously constructed compositum inside
`AlgebraicClosure K`, not a new field specified by desired properties.
Normality follows from the signs of the three square roots. In characteristic
zero separability then gives the actual `IsGalois K L` instance.

For `lam ≠ 0, 1`, automorphisms inject into the finite sign group `Fin 3 → ℤˣ`.
Consequently the extension degree divides eight, is a power of two, and is
coprime to every odd prime. The power-of-two conclusion uses group-cardinality
divisibility, not merely the earlier numerical bound on the degree.

These statements control a square-root extension used in parameter changes.
They do not identify it with a mod-l representation kernel from IUT or prove
all arithmetic admissibility hypotheses of that paper.
-/

noncomputable section

namespace LeanFormal.IUT.LegendreParameterGalois

open IntermediateField
open LeanFormal.IUT.LegendreQuadraticParameterFields

namespace RootSigns

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Two elements of a field with equal squares differ by sign. -/
theorem eq_or_eq_neg_of_square_eq {x y : E} (equal_squares : x ^ 2 = y ^ 2) :
    x = y ∨ x = -y := by
  have product_zero : (x - y) * (x + y) = 0 := by
    calc
      _ = x ^ 2 - y ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr equal_squares
  rcases mul_eq_zero.mp product_zero with difference_zero | sum_zero
  · exact Or.inl (sub_eq_zero.mp difference_zero)
  · exact Or.inr (eq_neg_of_add_eq_zero_left sum_zero)

/-- A base-field automorphism can only change the sign of a square root of a
base-field element. -/
theorem apply_eq_or_eq_neg (u : E) (d : F)
    (square_eq : u ^ 2 = algebraMap F E d) (sigma : E ≃ₐ[F] E) :
    sigma u = u ∨ sigma u = -u := by
  apply eq_or_eq_neg_of_square_eq
  calc
    (sigma u) ^ 2 = sigma (u ^ 2) := (map_pow sigma u 2).symm
    _ = sigma (algebraMap F E d) := congrArg sigma square_eq
    _ = algebraMap F E d := sigma.commutes d
    _ = u ^ 2 := square_eq.symm

/-- The two possible signs are actual units of the integers. -/
theorem exists_integerUnit_action (u : E) (d : F)
    (square_eq : u ^ 2 = algebraMap F E d) (sigma : E ≃ₐ[F] E) :
    ∃ epsilon : ℤˣ, sigma u = ((epsilon : ℤ) : E) * u := by
  rcases apply_eq_or_eq_neg u d square_eq sigma with positive | negative
  · exact ⟨1, by simpa using positive⟩
  · exact ⟨-1, by simpa using negative⟩

/-- The integer sign by which an automorphism acts on the specified root. -/
def integerSign (u : E) (d : F)
    (square_eq : u ^ 2 = algebraMap F E d) (sigma : E ≃ₐ[F] E) : ℤˣ :=
  Classical.choose (exists_integerUnit_action u d square_eq sigma)

theorem integerSign_action (u : E) (d : F)
    (square_eq : u ^ 2 = algebraMap F E d) (sigma : E ≃ₐ[F] E) :
    sigma u = ((integerSign u d square_eq sigma : ℤ) : E) * u :=
  Classical.choose_spec (exists_integerUnit_action u d square_eq sigma)

variable [CharZero E]

/-- For a nonzero root the sign is unique; characteristic zero makes the
integer-unit cast injective. -/
theorem integerSign_eq_of_action (u : E) (d : F)
    (square_eq : u ^ 2 = algebraMap F E d) (root_ne_zero : u ≠ 0)
    (sigma : E ≃ₐ[F] E) (epsilon : ℤˣ)
    (action_eq : sigma u = ((epsilon : ℤ) : E) * u) :
    integerSign u d square_eq sigma = epsilon := by
  apply Units.ext
  apply Int.cast_injective (α := E)
  exact mul_right_cancel₀ root_ne_zero
    ((integerSign_action u d square_eq sigma).symm.trans action_eq)

/-- The root sign is a group homomorphism on the actual automorphism group. -/
def integerSignHom (u : E) (d : F)
    (square_eq : u ^ 2 = algebraMap F E d) (root_ne_zero : u ≠ 0) :
    (E ≃ₐ[F] E) →* ℤˣ where
  toFun := integerSign u d square_eq
  map_one' := by
    apply integerSign_eq_of_action u d square_eq root_ne_zero
    simp
  map_mul' sigma tau := by
    apply integerSign_eq_of_action u d square_eq root_ne_zero
    calc
      (sigma * tau) u = sigma (tau u) := rfl
      _ = sigma (((integerSign u d square_eq tau : ℤ) : E) * u) :=
        congrArg sigma (integerSign_action u d square_eq tau)
      _ = ((integerSign u d square_eq tau : ℤ) : E) * sigma u := by simp
      _ = ((integerSign u d square_eq tau : ℤ) : E) *
          (((integerSign u d square_eq sigma : ℤ) : E) * u) := by
        rw [integerSign_action u d square_eq sigma]
      _ = (((integerSign u d square_eq sigma *
          integerSign u d square_eq tau : ℤˣ) : ℤ) : E) * u := by
        simp only [Units.val_mul, Int.cast_mul]
        ring

end RootSigns

variable (K : Type*) [Field K] [NumberField K]

/-- Every ambient automorphism preserves the actual simple square-root field. -/
theorem squareRootField_map_le (d : K)
    (sigma : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    (squareRootField K d).map sigma.toAlgHom ≤ squareRootField K d := by
  change (IntermediateField.adjoin K {algebraicSquareRoot K d}).map sigma.toAlgHom ≤
    IntermediateField.adjoin K {algebraicSquareRoot K d}
  rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro x ⟨root, root_member, rfl⟩
  have root_eq : root = algebraicSquareRoot K d := Set.mem_singleton_iff.mp root_member
  subst root
  rcases RootSigns.apply_eq_or_eq_neg (algebraicSquareRoot K d) d
      (algebraicSquareRoot_sq K d) sigma with positive | negative
  · rw [show sigma.toAlgHom (algebraicSquareRoot K d) = algebraicSquareRoot K d from positive]
    exact IntermediateField.mem_adjoin_simple_self K (algebraicSquareRoot K d)
  · rw [show sigma.toAlgHom (algebraicSquareRoot K d) = -algebraicSquareRoot K d from negative]
    exact (IntermediateField.adjoin K {algebraicSquareRoot K d}).neg_mem
      (IntermediateField.mem_adjoin_simple_self K (algebraicSquareRoot K d))

instance squareRootField_normal (d : K) : Normal K (squareRootField K d) := by
  apply IntermediateField.normal_iff_forall_map_le'.mpr
  exact squareRootField_map_le K d

/-- Normality of the actual three-root compositum, proved by stability of each
of its generators under ambient automorphisms. -/
instance legendreParameterField_normal (lam : K) :
    Normal K (legendreParameterField K lam) := by
  apply IntermediateField.normal_iff_forall_map_le'.mpr
  intro sigma
  change ((squareRootField K (-1) ⊔ squareRootField K lam) ⊔
      squareRootField K (1 - lam)).map sigma.toAlgHom ≤
    (squareRootField K (-1) ⊔ squareRootField K lam) ⊔ squareRootField K (1 - lam)
  rw [IntermediateField.map_sup, IntermediateField.map_sup]
  exact sup_le_sup
    (sup_le_sup (squareRootField_map_le K (-1) sigma)
      (squareRootField_map_le K lam sigma))
    (squareRootField_map_le K (1 - lam) sigma)

/-- The constructed parameter field is an actual finite Galois extension of
the number field K. Normality also holds at the excluded parameters; their
exclusion is needed below for the three nonzero sign coordinates. -/
instance legendreParameterField_isGalois (lam : K) :
    IsGalois K (legendreParameterField K lam) where
  to_isSeparable := inferInstance
  to_normal := legendreParameterField_normal K lam

/-- The compositum is generated by precisely the three ambient roots. -/
theorem legendreParameterField_eq_adjoin (lam : K) :
    legendreParameterField K lam = IntermediateField.adjoin K
      {algebraicSquareRoot K (-1), algebraicSquareRoot K lam,
        algebraicSquareRoot K (1 - lam)} := by
  change (IntermediateField.adjoin K {algebraicSquareRoot K (-1)} ⊔
      IntermediateField.adjoin K {algebraicSquareRoot K lam}) ⊔
      IntermediateField.adjoin K {algebraicSquareRoot K (1 - lam)} = _
  rw [← IntermediateField.adjoin_union, ← IntermediateField.adjoin_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Ordered roots for the three sign coordinates: minus one, parameter,
and complementary parameter. -/
def parameterRoot (lam : K) (index : Fin 3) : legendreParameterField K lam :=
  ![legendreSqrtNegOne K lam, legendreSqrtParameter K lam,
    legendreSqrtComplement K lam] index

/-- The corresponding base-field radicands. -/
def parameterRadicand (lam : K) (index : Fin 3) : K :=
  ![-1, lam, 1 - lam] index

theorem parameterRoot_sq (lam : K) (index : Fin 3) :
    parameterRoot K lam index ^ 2 =
      algebraMap K (legendreParameterField K lam) (parameterRadicand K lam index) := by
  fin_cases index <;>
    simp [parameterRoot, parameterRadicand, map_sub]

theorem parameterRoot_ne_zero (lam : K)
    (parameter_ne_zero : lam ≠ 0) (parameter_ne_one : lam ≠ 1) (index : Fin 3) :
    parameterRoot K lam index ≠ 0 := by
  fin_cases index
  · exact legendreSqrtNegOne_ne_zero K lam
  · exact legendreSqrtParameter_ne_zero K lam parameter_ne_zero
  · exact legendreSqrtComplement_ne_zero K lam parameter_ne_one

/-- Automorphisms of the actual parameter field are determined by the three
root images; this uses the adjoin description, not merely cardinal bounds. -/
theorem automorphism_ext (lam : K)
    (sigma tau : legendreParameterField K lam ≃ₐ[K] legendreParameterField K lam)
    (roots_eq : ∀ index : Fin 3,
      sigma (parameterRoot K lam index) = tau (parameterRoot K lam index)) :
    sigma = tau := by
  have hom_eq : sigma.toAlgHom = tau.toAlgHom := by
    apply IntermediateField.algHom_ext_of_eq_adjoin K
      (legendreParameterField_eq_adjoin K lam)
    intro x member
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
    rcases member with rfl | rfl | rfl
    · exact roots_eq 0
    · exact roots_eq 1
    · exact roots_eq 2
  ext x
  exact congrArg Subtype.val (DFunLike.congr_fun hom_eq x)

/-- The three root signs define a homomorphism into the finite sign group. -/
def legendreSignHom (lam : K)
    (parameter_ne_zero : lam ≠ 0) (parameter_ne_one : lam ≠ 1) :
    (legendreParameterField K lam ≃ₐ[K] legendreParameterField K lam) →*
      (Fin 3 → ℤˣ) where
  toFun sigma index :=
    RootSigns.integerSignHom (parameterRoot K lam index) (parameterRadicand K lam index)
      (parameterRoot_sq K lam index)
      (parameterRoot_ne_zero K lam parameter_ne_zero parameter_ne_one index) sigma
  map_one' := by
    funext index
    exact map_one (RootSigns.integerSignHom
      (parameterRoot K lam index) (parameterRadicand K lam index)
      (parameterRoot_sq K lam index)
      (parameterRoot_ne_zero K lam parameter_ne_zero parameter_ne_one index))
  map_mul' sigma tau := by
    funext index
    exact map_mul (RootSigns.integerSignHom
      (parameterRoot K lam index) (parameterRadicand K lam index)
      (parameterRoot_sq K lam index)
      (parameterRoot_ne_zero K lam parameter_ne_zero parameter_ne_one index)) sigma tau

/-- Each coordinate of the homomorphism records the actual root action. -/
theorem legendreSignHom_action (lam : K)
    (parameter_ne_zero : lam ≠ 0) (parameter_ne_one : lam ≠ 1)
    (sigma : legendreParameterField K lam ≃ₐ[K] legendreParameterField K lam)
    (index : Fin 3) :
    sigma (parameterRoot K lam index) =
      ((legendreSignHom K lam parameter_ne_zero parameter_ne_one sigma index : ℤ) :
        legendreParameterField K lam) * parameterRoot K lam index :=
  RootSigns.integerSign_action (parameterRoot K lam index) (parameterRadicand K lam index)
    (parameterRoot_sq K lam index) sigma

/-- The sign homomorphism is injective, so this is an actual group embedding. -/
theorem legendreSignHom_injective (lam : K)
    (parameter_ne_zero : lam ≠ 0) (parameter_ne_one : lam ≠ 1) :
    Function.Injective (legendreSignHom K lam parameter_ne_zero parameter_ne_one) := by
  intro sigma tau signs_eq
  apply automorphism_ext K lam sigma tau
  intro index
  rw [legendreSignHom_action K lam parameter_ne_zero parameter_ne_one sigma index,
    legendreSignHom_action K lam parameter_ne_zero parameter_ne_one tau index,
    congrFun signs_eq index]

/-- Every integer sign has square one. -/
theorem integerUnit_sq (epsilon : ℤˣ) : epsilon ^ 2 = 1 := by
  rcases Int.units_eq_one_or epsilon with rfl | rfl <;> norm_num

/-- Every automorphism of the actual parameter field has square one. -/
theorem automorphism_sq_eq_one (lam : K)
    (parameter_ne_zero : lam ≠ 0) (parameter_ne_one : lam ≠ 1)
    (sigma : legendreParameterField K lam ≃ₐ[K] legendreParameterField K lam) :
    sigma ^ 2 = 1 := by
  apply legendreSignHom_injective K lam parameter_ne_zero parameter_ne_one
  rw [map_pow, map_one]
  funext index
  exact integerUnit_sq _

/-- All automorphisms commute because the faithful sign representation lands
in a commutative group. -/
theorem automorphism_mul_comm (lam : K)
    (parameter_ne_zero : lam ≠ 0) (parameter_ne_one : lam ≠ 1)
    (sigma tau : legendreParameterField K lam ≃ₐ[K] legendreParameterField K lam) :
    sigma * tau = tau * sigma := by
  apply legendreSignHom_injective K lam parameter_ne_zero parameter_ne_one
  rw [map_mul, map_mul, mul_comm]

/-- The actual target sign group has eight elements. -/
theorem card_signGroup : Nat.card (Fin 3 → ℤˣ) = 8 := by
  norm_num [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_units_int]

/-- The degree divides eight, using Galois cardinality and Lagrange's theorem
for the image of the injective sign homomorphism. -/
theorem legendreParameterField_finrank_dvd_eight (lam : K)
    (parameter_ne_zero : lam ≠ 0) (parameter_ne_one : lam ≠ 1) :
    Module.finrank K (legendreParameterField K lam) ∣ 8 := by
  let signMap := legendreSignHom K lam parameter_ne_zero parameter_ne_one
  have injective_signMap : Function.Injective signMap :=
    legendreSignHom_injective K lam parameter_ne_zero parameter_ne_one
  have card_eq_range :
      Nat.card (legendreParameterField K lam ≃ₐ[K] legendreParameterField K lam) =
        Nat.card signMap.range := by
    apply Nat.card_congr
    apply Equiv.ofBijective (fun sigma =>
      (⟨signMap sigma, ⟨sigma, rfl⟩⟩ : signMap.range))
    constructor
    · intro sigma tau image_eq
      apply injective_signMap
      exact congrArg Subtype.val image_eq
    · rintro ⟨signs, ⟨sigma, rfl⟩⟩
      exact ⟨sigma, rfl⟩
  rw [← IsGalois.card_aut_eq_finrank K (legendreParameterField K lam), card_eq_range,
    ← card_signGroup]
  exact Subgroup.card_subgroup_dvd_card signMap.range

/-- The extension degree is genuinely a power of two, with exponent at most
three. This includes the degree-one case with exponent zero. -/
theorem legendreParameterField_finrank_eq_two_pow (lam : K)
    (parameter_ne_zero : lam ≠ 0) (parameter_ne_one : lam ≠ 1) :
    ∃ exponent ≤ 3, Module.finrank K (legendreParameterField K lam) = 2 ^ exponent := by
  apply (Nat.dvd_prime_pow Nat.prime_two).mp
  exact legendreParameterField_finrank_dvd_eight K lam parameter_ne_zero parameter_ne_one

/-- If the base already contains a square root of minus one, the power-of-two
exponent is at most two. -/
theorem legendreParameterField_finrank_eq_two_pow_of_sqrt_neg_one (lam : K)
    (parameter_ne_zero : lam ≠ 0) (parameter_ne_one : lam ≠ 1)
    (sqrt_neg_one_in_base : ∃ i : K, i ^ 2 = -1) :
    ∃ exponent ≤ 2, Module.finrank K (legendreParameterField K lam) = 2 ^ exponent := by
  obtain ⟨exponent, exponent_le_three, degree_eq⟩ :=
    legendreParameterField_finrank_eq_two_pow K lam parameter_ne_zero parameter_ne_one
  refine ⟨exponent, ?_, degree_eq⟩
  have degree_le_four := legendreParameterField_finrank_le_four K lam sqrt_neg_one_in_base
  by_contra not_le_two
  have exponent_eq_three : exponent = 3 := by omega
  rw [degree_eq, exponent_eq_three] at degree_le_four
  norm_num at degree_le_four

/-- The improved field degree actually divides four, not just bounds four. -/
theorem legendreParameterField_finrank_dvd_four (lam : K)
    (parameter_ne_zero : lam ≠ 0) (parameter_ne_one : lam ≠ 1)
    (sqrt_neg_one_in_base : ∃ i : K, i ^ 2 = -1) :
    Module.finrank K (legendreParameterField K lam) ∣ 4 := by
  obtain ⟨exponent, exponent_le_two, degree_eq⟩ :=
    legendreParameterField_finrank_eq_two_pow_of_sqrt_neg_one K lam
      parameter_ne_zero parameter_ne_one sqrt_neg_one_in_base
  rw [degree_eq]
  simpa using Nat.pow_dvd_pow 2 exponent_le_two

/-- The relative degree is coprime to every prime other than two. -/
theorem legendreParameterField_finrank_coprime_prime (lam : K)
    (parameter_ne_zero : lam ≠ 0) (parameter_ne_one : lam ≠ 1)
    (ell : ℕ) (ell_prime : ell.Prime) (ell_ne_two : ell ≠ 2) :
    Nat.Coprime (Module.finrank K (legendreParameterField K lam)) ell := by
  obtain ⟨exponent, _, degree_eq⟩ :=
    legendreParameterField_finrank_eq_two_pow K lam parameter_ne_zero parameter_ne_one
  have ell_not_dvd_two : ¬ell ∣ 2 := by
    intro divides_two
    exact ell_ne_two (le_antisymm (Nat.le_of_dvd (by decide) divides_two) ell_prime.two_le)
  have two_coprime_ell : Nat.Coprime 2 ell :=
    Nat.coprime_comm.mp ((ell_prime.coprime_iff_not_dvd).mpr ell_not_dvd_two)
  rw [degree_eq]
  exact Nat.Coprime.pow_left exponent two_coprime_ell

/-- The odd-prime formulation used by controlled extension consumers. -/
theorem legendreParameterField_finrank_coprime_odd_prime (lam : K)
    (parameter_ne_zero : lam ≠ 0) (parameter_ne_one : lam ≠ 1)
    (ell : ℕ) (ell_prime : ell.Prime) (ell_odd : Odd ell) :
    Nat.Coprime (Module.finrank K (legendreParameterField K lam)) ell := by
  apply legendreParameterField_finrank_coprime_prime K lam
    parameter_ne_zero parameter_ne_one ell ell_prime
  intro ell_eq_two
  rw [ell_eq_two] at ell_odd
  norm_num at ell_odd

end LeanFormal.IUT.LegendreParameterGalois
