import Mathlib.RingTheory.Etale.Finite

/-!
# Finite etale K-algebras, the actual fiber functor, and the separably closed Galois equivalence

Actual Mathlib instances for the tree: CommAlgCat.FiniteEtale K (category),
CommAlgCat.FiniteEtale.fiber K Ω (actual fiber functor), and for separably
closed Ω the actual anti-equivalence CommAlgCat.FiniteEtale.equivOfIsSepClosed Ω
: (FiniteEtale Ω)ᵒᵖ ≌ FintypeCat.  Only the general-K GaloisCategory/
fundamental-group identification with finite continuous G_K-sets is frozen as an
explicit card (no inhabitant).  No curve pi1 identification, no theta/q claim.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

universe u

open CategoryTheory CommAlgCat

/-- The actual category of finite etale K-algebras (Mathlib's
CommAlgCat.FiniteEtale K, not a card). -/
abbrev finiteEtaleCategory (K : Type u) [Field K] : Type (u + 1) :=
  CommAlgCat.FiniteEtale.{u} K

/-- The actual fiber functor of finite etale K-algebras at a geometric point
Ω: the functor S ↦ (S →ₐ[K] Ω), to finite types. -/
abbrev finiteEtaleFiber {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] :
    (finiteEtaleCategory K)ᵒᵖ ⥤ FintypeCat.{u} :=
  CommAlgCat.FiniteEtale.fiber K Ω

/-- The genuine fiber functor over a general field K, taken at an actual
algebraic closure of K (which is in particular a geometric point). -/
abbrev finiteEtaleFiberAtAlgebraicClosure (K : Type u) [Field K] :
    (finiteEtaleCategory K)ᵒᵖ ⥤ FintypeCat.{u} :=
  finiteEtaleFiber (K := K) (Ω := AlgebraicClosure K)

/-- For a separably closed field Ω, Mathlib's actual anti-equivalence between
finite etale Ω-algebras and finite types. -/
noncomputable abbrev finiteEtaleSeparablyClosedEquiv (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] :
    (finiteEtaleCategory Ω)ᵒᵖ ≌ FintypeCat.{u} :=
  CommAlgCat.FiniteEtale.equivOfIsSepClosed.{u} Ω

/-- The fiber functor at a separably closed field is an actual equivalence of
categories (Mathlib instance). -/
theorem finiteEtaleFiber_isEquivalence_of_isSepClosed (Ω : Type u) [Field Ω]
    [IsSepClosed Ω] : (finiteEtaleFiber (K := Ω) (Ω := Ω)).IsEquivalence :=
  inferInstance

/-! ## Frozen card: the general-K Galois category and finite continuous G_K-sets -/

/-- Frozen card: the missing general-K identification of the Galois category
with finite continuous G_K-sets.  It records only the data to be constructed
(no inhabitant, no fake instance). -/
structure generalKGaloisCategoryCard (K : Type u) [Field K] where
  finiteContinuousGSetCategory : Type u
  instGSetCategory : CategoryTheory.Category.{u, u} finiteContinuousGSetCategory
  galoisCategory : Type u
  instGaloisCategory : CategoryTheory.Category.{u, u} galoisCategory
  fiber : galoisCategory -> Type u

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
end
