import Mathlib
import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.Belyi
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.Mzk1BelyiCanonicalActual
import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24P1ApplicationActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

abbrev Qbar : Type := AlgebraicClosure ℚ

local instance : DecidableEq (P1Point Qbar) := Classical.decEq _

/-- **(M2) Interface application**: for a finite set S of algebraic points, the
Belyification produces a nonconstant P^1-morphism (stage4 interface) whose mapPoints
carries the finite set into the target set {0,1,infinity}.  The remaining interface
clauses (AvoidsPoint beta, UnramifiedOver) are the named residuals. -/
theorem s3135_p1Morphism_preserves_of_belyi (S : Finset Qbar) :
    ∃ (φ : P1Morphism Qbar) (targetSet : Set (P1Point Qbar)),
      φ.nonconstant ∧
        PreservesSet φ ((↑(S.image (P1Point.ofFinite (K := Qbar))) : Set (P1Point Qbar)))
          targetSet := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic (k := ℚ)
  have hInt : ∀ x ∈ S, IsIntegral ℚ x :=
    fun x _ => IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨q, hq, hqS, hqcrit⟩ :=
    TauCeti.exists_polynomial_aeval_mem_criticalValues_subset (K := Qbar) hInt
  have hqcritQ : q.criticalValues Qbar ⊆ ({0, 1} : Set Qbar) := hqcrit Qbar
  let mapPoints : P1Point Qbar → P1Point Qbar :=
    fun p => p.map (fun x => Polynomial.aeval x q)
  let φ : P1Morphism Qbar :=
    { ratFunc := 0
      mapPoints := mapPoints
      nonconstant := 0 < q.natDegree
      nonconstant_proof := hq }
  let targetSet : Set (P1Point Qbar) :=
    {(P1Point.infty : P1Point Qbar), P1Point.ofFinite (0 : Qbar), P1Point.ofFinite (1 : Qbar)}
  refine ⟨φ, targetSet, hq, ?_⟩
  intro p hp
  obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hp
  have hqx : Polynomial.aeval x q ∈ ({0, 1} : Set Qbar) := hqS x hxS
  show (φ.mapPoints (P1Point.ofFinite x)) ∈ targetSet
  simp only [φ, mapPoints, P1Point.ofFinite, Option.map_some, targetSet, Set.mem_insert_iff,
    Set.mem_singleton_iff, Option.some.injEq]
  rcases hqx with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- (M2) status: P^1-morphism interface applied via Belyification; remaining clauses
AvoidsPoint beta (M1: monic growth PROVED, Lemma 2.3 normalization wiring pending) and
UnramifiedOver (unramifiedAt data interface). -/
def s3135Mzk1P1Status : Audit.Obligation :=
  { id := "MZK1.lemma24.p1-interface-application"
    source := "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines 144-160"
    status := Audit.VerificationStatus.interface
    note := "CONSUMED: stage4 Mzk1P1MorphismInterfaceActual (P1Point := Option K, P1Morphism, PreservesSet/AvoidsPoint/UnramifiedOver, Mzk1Lemma24StatementShape) and Belyi assets (tauceti_belyi_core + stepxi Mzk1BelyiCanonicalActual). PROVED: s3135_p1Morphism_preserves_of_belyi (nonconstant P1Morphism over Qbar with PreservesSet of the finite set into {0,1,infty}). REMAINING interface clauses: AvoidsPoint beta (M1; monic growth estimate PROVED in Mzk1Lemma24GrowthActual; Lemma 2.3 normalization wiring pending) and UnramifiedOver (unramifiedAt data interface); Mzk1Lemma24StatementShape then follows by plugging the clauses. No fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.wiring.M-M1-M3", "MZK1.lemma24.main-statement" ]
    sorryItems :=
      [ "AvoidsPoint beta (Lemma 2.3 normalization wiring + growth)",
        "UnramifiedOver unramifiedAt data (stage4 interface)" ] }

#check s3135_p1Morphism_preserves_of_belyi
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24P1ApplicationActual
end