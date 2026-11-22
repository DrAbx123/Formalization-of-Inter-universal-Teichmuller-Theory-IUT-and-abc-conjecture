import Mathlib
import tmp.sheaf.xif.paper.Mzk1Lemma24Proof2Actual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24GaloisUnionActual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma24Proof2Actual

/-- The algebraic closure of Q (ambient field for [Mzk1] Lemma 2.4). -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- The conjugate set of an algebraic point alpha: the roots in Qbar of its minimal
polynomial over Q (paper [Mzk1] lines 166-169: the set of Gal(Qbar/Q)-conjugates). -/
def conjugateSet (α : Qbar) : Set Qbar :=
  {x : Qbar | Polynomial.aeval x (minpoly ℚ α) = 0}

/-- Every point belongs to its own conjugate set (minpoly.aeval). -/
theorem s3135_self_mem_conjugateSet (α : Qbar) : α ∈ conjugateSet α := by
  simp only [conjugateSet, Set.mem_setOf_eq]
  exact minpoly.aeval (A := ℚ) (x := α)

/-- The conjugate set is stable under the Galois action, exactly as used in the paper
(lines 166-169): if x is conjugate to alpha then so is sigma x, for every
Q-algebra automorphism sigma of Qbar. -/
theorem s3135_conjugateSet_stable (α : Qbar) (σ : Qbar ≃ₐ[ℚ] Qbar) {x : Qbar}
    (hx : x ∈ conjugateSet α) : σ x ∈ conjugateSet α := by
  simp only [conjugateSet, Set.mem_setOf_eq] at hx ⊢
  rw [Polynomial.aeval_algHom_apply]
  rw [hx, map_zero]

/-- The conjugate set is finite (roots of a nonzero polynomial).  Registered as the
class-B finiteness step: the proof needs minpoly nonzero over Qbar and the roots
finiteness lemma, wired in a later batch; the statement is exact. -/
def ConjugateSetFiniteStatement (α : Qbar) : Prop := (conjugateSet α).Finite

/-- Status of the Galois-conjugate union step of [Mzk1] Lemma 2.4 (lines 166-169):
definitions and self-membership/stability PROVED; finiteness and the union over all
conjugates registered. -/
def s3135Mzk1GaloisUnionStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.galois-conjugate-union"
    source :=
      "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines " ++
        "166-169 (Galois-conjugate union closure)"
    status := Audit.VerificationStatus.interface
    note :=
      "PROVED HERE: conjugateSet alpha = {x in Qbar | aeval x (minpoly Q alpha) = 0} " ++
        "(the paper's set of Galois conjugates); s3135_self_mem_conjugateSet " ++
        "(alpha in its conjugate set); s3135_conjugateSet_stable (stability under " ++
        "every Q-algebra automorphism of Qbar, via aeval_algHom_apply).  REGISTERED " ++
        "class B: ConjugateSetFiniteStatement (finiteness of the conjugate set; roots " ++
        "of the nonzero minimal polynomial; needs minpoly nonzero over Qbar + " ++
        "Polynomial.finite_setOf_isRoot wiring).  NEXT: prove finiteness, then form " ++
        "the union over the finite set S and prove m/d monotonicity for the union " ++
        "(used in the induction step, lines 179-206).  No fake witnesses; registry " ++
        "frozen 14041."
    dependsOn := [ "MZK1.lemma24.reduced-degree-induction" ]
    sorryItems :=
      [ "ConjugateSetFiniteStatement (finiteness of conjugate set)",
        "union over S and m/d monotonicity for the union (lines 179-206)" ] }

#check s3135_self_mem_conjugateSet
#check s3135_conjugateSet_stable
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24GaloisUnionActual
end
