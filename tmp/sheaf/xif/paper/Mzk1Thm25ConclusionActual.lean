import tmp.sheaf.xif.paper.Mzk1GeometricCoreRealStructureActual
import Mathlib.Tactic

/-! # Mzk1Thm25ConclusionActual — [Mzk1] Theorem 2.5 conclusion, conditional on GeometricCore

STEP 0 prior-art: Mzk1GeometricCoreRealStructureActual (real structure over ported green
FiniteMapData/RiemannRochRows; Mzk1GeometricCoreWitness with explicit condition Prop
fields), Mzk1Theorem25StatementActual (statement/reduction architecture), Mzk1Lemma22
/24 induction plans, Mzk1Lemma21/23 proved fragments.

PAPER: [Mzk1] Theorem 2.5 (lines 207-221): for X smooth proper connected over Qbar,
finite disjoint S,T in X(Qbar): there exists phi : X -> P^1_Q unramified over
P^1_Q minus {0,1,infinity}, phi(S) subset {0,1,infinity}, phi(T) intersect {0,1,infinity}
empty; descent over a number field F.

THIS FILE records the conditional form: GeometricCore as the SINGLE hypothesis, and
the conclusion packaged from the witness's fields (finite map + degree positive +
the three condition Prop fields).  The remaining mathematical content is the
reduction of the paper's Thm 2.5 hypotheses to GeometricCore and the construction of
the witness conditions (T-side/line-bundle APIs); these stay explicit obligations.
NOT a full proof of Thm 2.5. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm25ConclusionActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual

universe u

/-- The [Mzk1] Thm 2.5 conclusion data, packaged from a GeometricCore witness: a
finite map to P^1 of positive degree together with the three paper conditions. -/
def Mzk1Thm25Conclusion {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (T D : Set C) (W : Mzk1GeometricCoreWitness c ε T D) : Prop :=
  0 < W.finiteMap.m ∧ W.maps_T_to_zero ∧ W.unramified_over_zero ∧ W.pullback_iso

/-- Conditional [Mzk1] Thm 2.5 conclusion: GeometricCore (existence of a witness) is
the single named hypothesis, and the conclusion is read off from the witness. -/
/-- NOTE: witness conditions remain explicit Prop fields (see residual obligations). -/
theorem mzk1Thm25Conclusion_of_geometricCore {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (T D : Set C) (hcore : Mzk1GeometricCoreRecast c ε T D) :
    ∃ W : Mzk1GeometricCoreWitness c ε T D, Mzk1Thm25Conclusion c ε T D W :=
  let W := Classical.choice hcore
  ⟨W, W.degree_pos, W.maps_T_to_zero_proof, W.unramified_over_zero_proof,
    W.pullback_iso_proof⟩

/-- The residual reduction obligations (data): what remains to turn the conditional
conclusion into the paper's Theorem 2.5. -/
def mzk1Thm25ResidualObligations : List (String × String) :=
  [ ("GeometricCore", "single named hypothesis (real-structure skeleton Mzk1GeometricCoreRecast)"),
    ("T-side conditions", "maps_T_to_zero/unramified_over_zero/pullback_iso are explicit Prop fields; APIs MISSING"),
    ("reduction of paper hypotheses to GeometricCore", "reduce to P1, Lemma 2.4, Lemma 2.3, Lemma 2.2 (Mzk1Lemma22/24 plans); MISSING proofs"),
    ("descent over number field F", "Galois-stability/descent; MISSING") ]

theorem mzk1Thm25ResidualObligations_length : mzk1Thm25ResidualObligations.length = 4 := rfl

#check mzk1Thm25Conclusion_of_geometricCore
#check mzk1Thm25ResidualObligations_length

end LeanFormal.IUT.XiFPaper.Mzk1Thm25ConclusionActual
end