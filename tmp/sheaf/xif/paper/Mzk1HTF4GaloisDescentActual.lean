import tmp.sheaf.xif.paper.Mzk1HTF4OrbitProductActual
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
/-!
# F4 Galois-orbit descent: invariance of the orbit product under reindexing

Route §8.3: the coefficients of `P_i = ∏_{σ} L_{σ x}` lie in ℚ because the product is
taken over a complete finite Galois orbit.  This file formalizes the combinatorial core:
if `L : ι → MvPolynomial (Fin 3) ℚ` is a finite family and `e : ι ≃ ι` is any
reindexing of the orbit representatives, then `∏ i, L (e i) = ∏ i, L i`; equivalently
the product is invariant under the action of the symmetric group on the index set.

## Reuse / donor check (2026-11-17)
* `Mzk1HTF4OrbitProductActual` DONE 12:54:03 (`OrbitProductData.P = ∏ i, L i`);
* Mathlib `Finset.prod_equiv`/`Equiv.Perm` for the reindexing invariance.

**Explicit obligation**: the actual Galois action of `Gal(ℚ̄/ℚ)` on geometric points and
the trace/norm descent (that the orbit product's coefficients are rational) are NOT
formalized here; this file proves the finite product is independent of the chosen
ordering/representatives, which is the combinatorial part of the descent.
-/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.HTF4GaloisDescentActual
open LeanFormal.IUT.XiFPaper.HTF4OrbitProductActual

variable {ι : Type*} [Fintype ι] {R : Type*} [CommSemiring R]
  (L : ι → MvPolynomial (Fin 3) ℚ)

/-- **Reindexing invariance**: the orbit product does not depend on the chosen
enumeration of the orbit representatives. -/
theorem orbitProduct_prod_equiv (e : ι ≃ ι) :
    (∏ i, L (e i)) = ∏ i, L i := by
  exact Equiv.prod_comp e L

/-- Orbit product is invariant under the permutation action of `Equiv.Perm ι`. -/
theorem orbitProduct_prod_perm (σ : Equiv.Perm ι) :
    (∏ i, L (σ i)) = ∏ i, L i :=
  orbitProduct_prod_equiv L σ

/-- The orbit product of a family is unchanged when the family is permuted; hence a
Galois-orbit product is well-defined independently of the representative choice. -/
theorem orbitProduct_P_eq_of_perm (D : OrbitProductData ι Unit) (σ : Equiv.Perm ι) :
    (∏ i, D.L (σ i)) = D.P := by
  unfold OrbitProductData.P
  exact orbitProduct_prod_equiv D.L σ

#print axioms orbitProduct_prod_equiv
#print axioms orbitProduct_prod_perm
#print axioms orbitProduct_P_eq_of_perm
end LeanFormal.IUT.XiFPaper.HTF4GaloisDescentActual
end