import Mathlib
import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.Belyi
import tmp.sheaf.xif.paper.Mzk1Lemma24DescentActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24MainStatementActual

abbrev Qbar : Type := AlgebraicClosure ℚ

/-- **(M) consumed TauCeti Belyi asset** (ported fresh in tmp/external/ported/belyi_poly,
Apache-2.0): for every finite set S of algebraic numbers there is a nonconstant polynomial
q over Q with rational coefficients whose values on S lie in {0,1} and whose critical
values lie in {0,1}.  This is the object language needed by the [Mzk1] Lemma 2.4
conclusion (paper lines 144-160: phi with phi(S) subset S_phi, unramified away from
S_phi; here S_phi can be taken as {0,1,infinity}). -/
theorem s3135_belyi_polynomial_of_finiteSet {S : Finset Qbar}
    (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : Polynomial ℚ, 0 < q.natDegree ∧
      (∀ s ∈ S, Polynomial.aeval s q ∈ ({0, 1} : Set Qbar)) ∧
      (q.criticalValues Qbar ⊆ ({0, 1} : Set Qbar)) := by
  obtain ⟨q, hq, hqS, hqcrit⟩ :=
    TauCeti.exists_polynomial_aeval_mem_criticalValues_subset (K := Qbar) hS
  exact ⟨q, hq, hqS, hqcrit Qbar⟩

/-- **(M) shape, partial**: with S_phi := {0,1,infinity} (the polynomial Belyi recipe),
a finite set S of algebraic numbers is mapped into S_phi by a nonconstant rational
polynomial q; the remaining paper conclusions are (b) beta avoids S_phi and (c)
unramified away from S_phi (see the status obligation). -/
theorem s3135_mainReduction_shape_partial {S : Finset Qbar}
    (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : Polynomial ℚ, 0 < q.natDegree ∧
      (∀ s ∈ S, Polynomial.aeval s q ∈ ({0, 1} : Set Qbar)) := by
  obtain ⟨q, hq, hqS, _⟩ := s3135_belyi_polynomial_of_finiteSet hS
  exact ⟨q, hq, hqS⟩

/-- **(M) main statement status** (paper [Mzk1] Lemma 2.4 lines 144-160): the exact
inventory of what is proved and what remains, with the consumed TauCeti Belyi assets. -/
def s3135Mzk1MainStatus : Audit.Obligation :=
  { id := "MZK1.lemma24.main-statement"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 144-160"
    status := Audit.VerificationStatus.interface
    note := "CONSUMED (ported TauCeti, Apache-2.0, tmp/external/ported/belyi_poly): TauCeti.exists_polynomial_aeval_mem_criticalValues_subset (Belyi.lean:314; rational q, nonconstant, aeval(S) subset {0,1}, critical values subset {0,1}) and TauCeti.criticalValues (CriticalValues.lean). PROVED HERE: s3135_belyi_polynomial_of_finiteSet (for finite S subset Qbar with IsIntegral: nonconstant q in Q[X] with q(S) subset {0,1} and critical values subset {0,1}) and s3135_mainReduction_shape_partial (q(S) subset {0,1}). REMAINING (named, not faked): (M1) beta-avoidance: need a Belyi-type q with q(beta) NOT in S_phi={0,1,infinity} (paper Lemma 2.3-style separation + composition; not in the ported asset); (M2) P^1-morphism/unramified-away predicate: Mathlib has no unramified-morphism API here (TauCeti AnalyticBelyiPair closure blocked by Mathlib drift; qpilot/ports may supply later) — the paper clause (c) must be stated against such a predicate; (M3) descent of q's coefficients to F via (D): coefficient-level descent proved in Mzk1Lemma24DescentActual; rational-function representative wiring remains. No fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.descent" ]
    sorryItems :=
      [ "(M1) beta-avoidance Belyi-type polynomial above beta outside S_phi",
        "(M2) P^1-morphism/unramified-away predicate (language gap)",
        "(M3) rational-function representative over F (descent wiring)" ] }

#check s3135_belyi_polynomial_of_finiteSet
#check s3135_mainReduction_shape_partial
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24MainStatementActual
end