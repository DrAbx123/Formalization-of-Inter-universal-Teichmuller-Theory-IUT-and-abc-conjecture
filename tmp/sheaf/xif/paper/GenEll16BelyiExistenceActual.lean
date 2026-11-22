import tmp.external.ported.tauceti_belyi_core.TauCeti.Algebra.Polynomial.Belyi

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: Belyi|CriticalValues|exists_polynomial_aeval_mem_criticalValues_subset -> hits tmp/external/ported/tauceti_belyi_core/TauCeti/Algebra/Polynomial/Belyi.lean:285/:317 (PORTED, FRESH EXIT=0, Apache-2.0) with exists_polynomial_eval_mem_criticalValues_subset and exists_polynomial_aeval_mem_criticalValues_subset; CriticalValues.lean FRESH EXIT=0; BelyiReduction.lean BUILT -> REUSE (polynomial Belyification CONSUMED; no re-proof of Belyi existence).

# [GenEll] 16: GeometricCore Belyi-existence input (consumed ported polynomial Belyification)

Corpus: papers/motizuki_corpus/text/Noncritical Belyi Maps.txt, Theorem 2.5
(statement 207-221, proof 222-281) and Lemma 2.2/2.4; GeometricCore finite-map
existence is the deep input.  TauCeti (Apache-2.0, ported fresh) proves POLYNOMIAL
BELYIFICATION: every finite set of algebraic numbers is carried into {0,1} by a
nonconstant rational polynomial whose critical values lie in {0,1} in every
characteristic-zero field.  This is the Belyi-existence content for the P^1 model.
HONESTY: the scheme-level finite-map conversion + the three GeometricCore conditions
(maps T to 0, unramified over 0, pullback O(1)=O(D)) remain named; this file proves
the Belyi certificate and records the consumption.  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.GenEll16BelyiExistenceActual

universe u

open Polynomial
open TauCeti

/-- **Polynomial Belyification (consumed ported theorem):** every finite set of
rational numbers is carried into {0,1} by a nonconstant rational polynomial whose
critical values in every characteristic-zero field lie in {0,1}. -/
theorem genEll16_belyi_poly_eval (S : Finset ℚ) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧ (∀ s ∈ S, q.eval s ∈ ({0, 1} : Set ℚ)) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ {0, 1} :=
  exists_polynomial_eval_mem_criticalValues_subset S

/-- **Polynomial Belyification of algebraic numbers (consumed ported theorem):**
every finite set S of elements algebraic over Q in K is carried into {0,1} by a
nonconstant rational polynomial whose critical values in every characteristic-zero
field lie in {0,1}. -/
theorem genEll16_belyi_poly_aeval {K : Type*} [Field K] [Algebra ℚ K]
    {S : Finset K} (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧ (∀ s ∈ S, aeval s q ∈ ({0, 1} : Set K)) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ {0, 1} :=
  exists_polynomial_aeval_mem_criticalValues_subset hS

/-- The polynomial Belyi certificate (the Belyi-existence content for the P^1
model of GeometricCore). -/
def BelyiPolynomialCertificate {K : Type*} [Field K] [Algebra ℚ K]
    (S : Finset K) : Prop :=
  ∃ q : ℚ[X], 0 < q.natDegree ∧ (∀ s ∈ S, aeval s q ∈ ({0, 1} : Set K)) ∧
    ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ {0, 1}

/-- **Belyi certificate PROVED** for finite sets of algebraic numbers (direct
consumption of the ported Belyification theorem). -/
theorem genEll16_belyiCertificate {K : Type*} [Field K] [Algebra ℚ K]
    {S : Finset K} (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    BelyiPolynomialCertificate S :=
  genEll16_belyi_poly_aeval hS

/-- Consumption/wiring rows for the GeometricCore Belyi input. -/
def genEll16Rows : List (String × String × String) :=
  [ ("polynomial Belyification over Q", "A", "CONSUMED ported theorem exists_polynomial_eval_mem_criticalValues_subset (Belyi.lean:285; FRESH EXIT=0)")
  , ("polynomial Belyification of algebraic numbers", "A", "CONSUMED ported theorem exists_polynomial_aeval_mem_criticalValues_subset (Belyi.lean:317; FRESH EXIT=0)")
  , ("Belyi certificate packaged", "A", "PROVED genEll16_belyiCertificate (BelyiPolynomialCertificate)")
  , ("maps S into {0,1} / critical values in {0,1}", "A", "PROVED as part of the certificate (from the ported theorem)")
  , ("scheme-level finite map to P^1 conversion", "B", "NAMED: polynomial -> scheme morphism bridge (ported FiniteMapData / BelyiPair layer pending qpilot port)")
  , ("three GeometricCore conditions (T to 0, unramified over 0, pullback O(1)=O(D))", "B", "NAMED; line-bundle/unramified APIs pending (GenEll15GeometricCoreAssemblyActual rows)")
  , ("GenEll05 noncriticalBelyiExists type bridge", "coordination", "GenEll05 input is typed at Mzk1GeometricCoreStatement placeholder; needs placeholder replacement approval (mainline/stage4)") ]

/-- The Belyi consumption row record has seven rows. -/
theorem genEll16Rows_length : genEll16Rows.length = 7 := rfl

#check genEll16_belyi_poly_eval
#check genEll16_belyi_poly_aeval
#check genEll16_belyiCertificate
#check BelyiPolynomialCertificate
#check genEll16Rows_length

end LeanFormal.IUT.XiFPaper.GenEll16BelyiExistenceActual
end