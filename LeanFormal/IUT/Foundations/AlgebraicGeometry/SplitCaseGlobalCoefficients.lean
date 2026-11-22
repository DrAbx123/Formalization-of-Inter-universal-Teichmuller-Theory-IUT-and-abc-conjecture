import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseGlobalAtoms
import Mathlib.Tactic

/-!
# M2-global coefficient idempotents from a component action

For B = S^(Fin n) with a finite group G acting by S-algebra automorphisms,
define the coefficient family a g i j = (g • e_i) j.  These are idempotents;
together with the production epsilonAtom_completeOrthogonal they give the
Boolean atom family and the product decomposition of S.
-/

open scoped BigOperators

namespace SplitCaseGlobalCoefficients

noncomputable section

universe u

variable {S : Type u} [CommRing S] {G : Type u} [Group G] [Fintype G]
  [DecidableEq G] {n : ℕ}
  [MulSemiringAction G (Fin n → S)] [SMulCommClass G S (Fin n → S)]

/-- Standard coordinate idempotent in S^(Fin n). -/
def stdIdem (i : Fin n) : Fin n → S := Pi.single i (1 : S)

/-- Matrix coefficient of the G-action on the standard coordinate. -/
def coeff (g : G) (i j : Fin n) : S := (g • stdIdem (S := S) i) j

lemma stdIdem_idempotent (i : Fin n) : IsIdempotentElem (stdIdem (S := S) i) := by
  rw [IsIdempotentElem]
  ext j
  by_cases h : j = i <;> simp [stdIdem, Pi.single, h]

lemma coeff_idempotent (g : G) (i j : Fin n) :
    IsIdempotentElem (coeff (S := S) g i j) := by
  have hstd : IsIdempotentElem (stdIdem (S := S) i) := stdIdem_idempotent i
  have hfun : IsIdempotentElem (g • stdIdem (S := S) i) := by
    rw [IsIdempotentElem]
    rw [← smul_mul', hstd.eq]
  have hcoord := congrFun hfun.eq j
  simpa [coeff, IsIdempotentElem] using hcoord

/-- The coefficient is fixed by the G-action after scalar extension to B. -/
lemma coeff_smul_algebraMap (g h : G) (i j : Fin n) :
    h • algebraMap S (Fin n → S) (coeff (S := S) g i j) =
      algebraMap S (Fin n → S) (coeff (S := S) g i j) := by
  simp

/-- The finite coefficient index set K = G × Fin n × Fin n. -/
abbrev CoeffIndex (G : Type u) (n : ℕ) := G × Fin n × Fin n

/-- Coefficient family indexed by K. -/
def coeffFamily : CoeffIndex G n → S :=
  fun p => coeff (S := S) p.1 p.2.1 p.2.2

theorem coeffFamily_idempotent (p : CoeffIndex G n) :
    IsIdempotentElem (coeffFamily (S := S) p) :=
  coeff_idempotent p.1 p.2.1 p.2.2

/-- The Boolean atoms of the coefficient family are complete orthogonal. -/
theorem coeffFamily_completeOrthogonal :
    CompleteOrthogonalIdempotents (I := Finset (CoeffIndex G n)) (R := S)
      (fun A => SplitCaseGlobalAtoms.epsilonAtom (K := CoeffIndex G n) (S := S)
        (coeffFamily (S := S) (G := G) (n := n)) A) :=
  SplitCaseGlobalAtoms.epsilonAtom_completeOrthogonal (K := CoeffIndex G n) (S := S)
    (coeffFamily (S := S) (G := G) (n := n))
    (coeffFamily_idempotent (S := S) (G := G) (n := n))

/-- Product decomposition: S is the product of the quotients S/(1 - e_A). -/
noncomputable def productEquiv :
    RingEquiv S ((A : Finset (CoeffIndex G n)) →
      S ⧸ Ideal.span ({1 - SplitCaseGlobalAtoms.epsilonAtom (coeffFamily (S := S)) A} : Set S)) :=
  RingEquiv.ofBijective
    (RingHom.pi fun A =>
      Ideal.Quotient.mk (Ideal.span ({1 - SplitCaseGlobalAtoms.epsilonAtom
        (coeffFamily (S := S)) A} : Set S)))
    (coeffFamily_completeOrthogonal (S := S) (G := G) (n := n)).bijective_pi

end

end SplitCaseGlobalCoefficients
