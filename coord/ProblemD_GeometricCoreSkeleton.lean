import Mathlib

/-! # Problem D skeleton — GeometricCore through the function field

SKELETON ONLY.  Proofs are `sorry` except one line of integer arithmetic.  NOT compiled.
Kept outside `tmp/sheaf/xif/paper` on purpose.  Source: coord/OPEN-HARD-PROBLEMS.md,
Problem D; paper lines 222-265.

What the rest of the proof of Theorem 2.5 consumes from psi : X -> P^1 is only
"psi^{-1}(0) = T with all multiplicities one".  That is: a function g with zero divisor
exactly the sum of T.  The isomorphism psi^* O(1) = O(D) is how the paper builds psi; it
is not used afterwards, and deg psi = |T| follows from the fibre.

Construction.  D = sum of T, deg D >= 2g+1.
* Riemann-Roch for D and D - t (both of degree > 2g-2) gives l(D) - l(D - t) = 1, so each
  L(D - t) is a proper subspace of L(D).
* Over an infinite field a vector space is not a finite union of proper subspaces; take
  h in L(D) outside every L(D - t).  Then h has a simple pole at each t in T and no other
  pole.
* g = 1/h.

Deep input: only function-field Riemann-Roch, i.e. the ported
`AlgebraicCurve.FunctionFieldRiemannRoch K F`
(tmp/external/ported/flt_test/Definitions/Def_AlgebraicCurve_RiemannRochRows.lean:47),
plus l(E) = 0 for deg E < 0 and deg K = 2g-2.  No Cartier divisor, Picard group or
pencil-to-morphism API.

`PencilData` below is an abstract interface.  Instantiating it with the ported
`AlgebraicCurve.Place`, `Divisor`, `ell` is not done here; that API was not read beyond
the Riemann-Roch statement.

Two defects of the current witness (Mzk1GeometricCorePreciseActual.lean:32-66), to fix
when restating: `Mzk1GeometricCoreRecastPrecise` is stated for an arbitrary scheme over an
arbitrary ring and arbitrary sets T, D, where existence cannot hold; `MapsTToZero` is
conditional on `t ∈ fm.U`, hence vacuous when T misses U.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ProblemDGeometricCoreSkeleton

/-! ## 1. Riemann-Roch arithmetic -/

/-- If Riemann-Roch holds for D and D - t and both dual terms vanish, then
l(D) - l(D - t) = 1. -/
theorem ell_drop_of_rr {g ellD ellDt ellKD ellKDt degD : ℤ}
    (h1 : ellD - ellKD = degD + 1 - g)
    (h2 : ellDt - ellKDt = (degD - 1) + 1 - g)
    (v1 : ellKD = 0) (v2 : ellKDt = 0) : ellD - ellDt = 1 := by
  omega

/-! ## 2. Avoiding finitely many proper subspaces -/

/-- Over an infinite field, U is not covered by finitely many proper subspaces.
Proof: Mathlib `Subspace.biUnion_ne_univ_of_top_nmem` (renamed `..._notMem` in recent
versions) applied inside U. -/
theorem exists_mem_notMem_of_proper {K V ι : Type*} [Field K] [Infinite K]
    [AddCommGroup V] [Module K V] (s : Finset ι) (W : ι → Submodule K V)
    (U : Submodule K V) (h : ∀ i ∈ s, W i < U) :
    ∃ v ∈ U, ∀ i ∈ s, v ∉ W i := by
  sorry

/-! ## 3. Abstract interface and the construction -/

/-- What the construction needs from the function field F of the curve over K, with
places P.  `proper` is the Riemann-Roch consequence; the other fields are the
definitions of L(D) and L(D - t) read through the order function. -/
structure PencilData (K F P : Type*) [Field K] [Field F] [Algebra K F] where
  /-- order of a nonzero function at a place -/
  ord : P → F → ℤ
  /-- the prescribed points -/
  T : Finset P
  /-- L(D), D = sum of T -/
  LD : Submodule K F
  /-- L(D - t) -/
  LDt : P → Submodule K F
  proper : ∀ t ∈ T, LDt t < LD
  pole : ∀ h ∈ LD, ∀ t ∈ T, h ∉ LDt t → ord t h = -1
  regular : ∀ h ∈ LD, h ≠ 0 → ∀ p, p ∉ T → 0 ≤ ord p h
  ord_inv : ∀ p (h : F), h ≠ 0 → ord p h⁻¹ = -ord p h

/-- A function with a simple pole at every point of T and no other pole.
Proof: `exists_mem_notMem_of_proper` with W = LDt, U = LD; nonzero because it is outside
some LDt t. -/
theorem exists_simple_pole_function {K F P : Type*} [Field K] [Infinite K] [Field F]
    [Algebra K F] (X : PencilData K F P) (hT : X.T.Nonempty) :
    ∃ h ∈ X.LD, h ≠ 0 ∧ (∀ t ∈ X.T, X.ord t h = -1) ∧
      ∀ p, p ∉ X.T → 0 ≤ X.ord p h := by
  sorry

/-- **GeometricCore in function-field form**: g has a simple zero at every point of T and
no other zero.  As a map to P^1: g(T) = {0}, g is unramified over 0, and g^{-1}(0) = T,
so 0 is not in g(S) for S disjoint from T.  Proof: g = h⁻¹ and `ord_inv`. -/
theorem exists_function_with_zero_divisor {K F P : Type*} [Field K] [Infinite K]
    [Field F] [Algebra K F] (X : PencilData K F P) (hT : X.T.Nonempty) :
    ∃ g : F, g ≠ 0 ∧ (∀ t ∈ X.T, X.ord t g = 1) ∧
      ∀ p, p ∉ X.T → X.ord p g ≤ 0 := by
  sorry

end LeanFormal.IUT.XiFPaper.ProblemDGeometricCoreSkeleton
end
