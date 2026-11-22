/-
  Coefficients fixed by a finite group action on a split finite algebra.

  B is a finite split S-algebra with a chosen S-algebra equivalence e : B ~= S^n.
  A finite group G acts by S-algebra automorphisms.  For the standard idempotents
  e_i = e.symm (single i 1), the coefficients
    a g i j = (e (g • e_i)) j
  are idempotents in S and are fixed by the diagonal S-action (which is trivial
  because S-algebra automorphisms fix the diagonal copy of S).
  The finite coefficient set and its Boolean/ring closure are therefore G-fixed.
-/
import Mathlib

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace LeanFormal.IUT.CoefficientFixedByG

universe u v w

variable {S : Type u} [CommRing S]
  {B : Type v} [CommRing B] [Algebra S B]
  {G : Type w} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G S B]
  {n : ℕ} (e : B ≃ₐ[S] (Fin n → S))

/-- Standard idempotent e_i = e.symm (Pi.single i 1). -/
def standardIdempotent (i : Fin n) : B :=
  e.symm (fun j => if j = i then (1 : S) else 0)

/-- The standard idempotents are idempotent in B. -/
theorem standardIdempotent_idem (i : Fin n) :
    standardIdempotent e i * standardIdempotent e i = standardIdempotent e i := by
  apply e.injective
  simp only [standardIdempotent, AlgEquiv.apply_symm_apply, map_mul]
  funext j
  by_cases h : j = i <;> simp [h]

/-- The coefficient a g i j = (e (g • e_i)) j. -/
def coefficient (g : G) (i j : Fin n) : S :=
  e (g • standardIdempotent e i) j

/-- Each coefficient is an idempotent of S. -/
theorem coefficient_idempotent (g : G) (i j : Fin n) :
    coefficient e g i j * coefficient e g i j = coefficient e g i j := by
  have hg : (g • standardIdempotent e i) * (g • standardIdempotent e i) =
      g • standardIdempotent e i := by
    calc
      (g • standardIdempotent e i) * (g • standardIdempotent e i)
          = g • (standardIdempotent e i * standardIdempotent e i) := by
              rw [smul_mul']
      _ = g • standardIdempotent e i := by rw [standardIdempotent_idem]
  have hvec : e (g • standardIdempotent e i) * e (g • standardIdempotent e i) =
      e (g • standardIdempotent e i) := by
    rw [← map_mul, hg]
  exact congrFun hvec j

/-- The diagonal S-action: S-algebra automorphisms fix S pointwise, so the
induced action on the diagonal copy of S is trivial. -/
noncomputable def diagonalActionHom (S : Type u) [CommRing S] (G : Type w) [Group G] :
    G →* (S ≃+* S) where
  toFun _ := RingEquiv.refl S
  map_one' := rfl
  map_mul' _ _ := rfl

instance diagonalMulSemiringAction (S : Type u) [CommRing S] (G : Type w) [Group G] :
    MulSemiringAction G S :=
  MulSemiringAction.compHom S (diagonalActionHom S G)

@[simp] theorem diagonal_smul_eq_self (h : G) (s : S) : h • s = s := rfl

/-- Each coefficient is fixed by G under the diagonal action. -/
theorem coefficient_fixed (h g : G) (i j : Fin n) :
    h • coefficient e g i j = coefficient e g i j :=
  diagonal_smul_eq_self h (coefficient e g i j)

/-- The finite set of all coefficients a g i j. -/
def coefficientSet (G : Type w) [Group G] [Finite G]
    (e : B ≃ₐ[S] (Fin n → S)) : Set S :=
  Set.range (fun p : G × Fin n × Fin n => coefficient e p.1 p.2.1 p.2.2)

theorem coefficientSet_finite : (coefficientSet G e).Finite := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  exact Set.finite_range _

/-- Every element of the ring closure of the coefficient set (in particular
every Boolean combination) is G-fixed. -/
def coefficientClosure (G : Type w) [Group G] [Finite G]
    (e : B ≃ₐ[S] (Fin n → S)) : Subring S :=
  Subring.closure (coefficientSet G e)

theorem coefficientClosure_fixed (h : G) {x : S}
    (hx : x ∈ coefficientClosure G e) : h • x = x :=
  diagonal_smul_eq_self h x

end LeanFormal.IUT.CoefficientFixedByG

end