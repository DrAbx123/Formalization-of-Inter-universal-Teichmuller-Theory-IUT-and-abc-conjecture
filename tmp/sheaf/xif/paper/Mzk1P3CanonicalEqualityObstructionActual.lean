import tmp.sheaf.xif.paper.Mzk1P3TensorCoreActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
/-! #6/#1 equality case: if a tensor block is algebraically a product of root
extensions, any factor of degree > 1 forces `card Bad < finrank block`; hence
`card Bad = finrank block` forces every factor degree 1. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P3CanonicalEqualityObstructionActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P3TensorCoreActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
/-- A finite product of nontrivial finite-dimensional vector spaces with one
factor of dimension > 1 has cardinal smaller than its dimension. -/
theorem card_lt_finrank_pi_of_one_degree_gt_one
    {K : Type*} [Field K] {J : Type*} [Fintype J] {E : J → Type*}
    [∀ j, AddCommGroup (E j)] [∀ j, Module K (E j)] [∀ j, FiniteDimensional K (E j)]
    [∀ j, Nontrivial (E j)] (j0 : J)
    (h0 : 1 < Module.finrank K (E j0)) :
    Fintype.card J < Module.finrank K ((j : J) → E j) := by
  rw [Module.finrank_pi_fintype]
  have hle : ∀ j ∈ Finset.univ, (1 : ℕ) ≤ Module.finrank K (E j) := by
    intro j _
    exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt ((Module.finrank_pos_iff_of_free (R := K) (M := E j)).mpr inferInstance))
  have hlt : (∑ _j : J, (1 : ℕ)) < ∑ j : J, Module.finrank K (E j) := by
    apply Finset.sum_lt_sum
    · exact hle
    · exact ⟨j0, Finset.mem_univ _, h0⟩
  simpa using hlt
/-- Canonical equality-case obstruction: if a tensor block is algebraically a
product of root extensions and one factor has degree > 1, then the number of
bad places is strictly smaller than the block dimension. -/
theorem canonical_card_lt_finrank
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {V : ι → Type} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i)
    [∀ b, Algebra ℚ_[p] (rootNormedExtension T b)]
    [∀ b, FiniteDimensional ℚ_[p] (rootNormedExtension T b)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]]
      ((b : Bad (nativePlaceSelection T)) → rootNormedExtension T b))
    (b0 : Bad (nativePlaceSelection T))
    (h0 : 1 < Module.finrank ℚ_[p] (rootNormedExtension T b0)) :
    Fintype.card (Bad (nativePlaceSelection T)) <
      Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) := by
  have hpi := card_lt_finrank_pi_of_one_degree_gt_one (K := ℚ_[p])
    (J := Bad (nativePlaceSelection T)) (E := fun b => rootNormedExtension T b) b0 h0
  simpa [e.toLinearEquiv.finrank_eq] using hpi
/-- Equality case: `card Bad = finrank block` forces every root-extension factor
to have degree 1. -/
theorem canonical_all_degree_one_of_card_eq_finrank
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {V : ι → Type} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i)
    [∀ b, Algebra ℚ_[p] (rootNormedExtension T b)]
    [∀ b, FiniteDimensional ℚ_[p] (rootNormedExtension T b)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]]
      ((b : Bad (nativePlaceSelection T)) → rootNormedExtension T b))
    (h : Fintype.card (Bad (nativePlaceSelection T)) =
      Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    ∀ b, Module.finrank ℚ_[p] (rootNormedExtension T b) = 1 := by
  intro b
  by_contra hb
  have hle : 1 ≤ Module.finrank ℚ_[p] (rootNormedExtension T b) :=
    Nat.one_le_iff_ne_zero.mpr
      (ne_of_gt ((Module.finrank_pos_iff_of_free (R := ℚ_[p]) (M := rootNormedExtension T b)).mpr inferInstance))
  have hgt : 1 < Module.finrank ℚ_[p] (rootNormedExtension T b) := by omega
  have hlt := canonical_card_lt_finrank T places tuple e b hgt
  omega
end LeanFormal.IUT.XiFPaper.Mzk1P3CanonicalEqualityObstructionActual
end