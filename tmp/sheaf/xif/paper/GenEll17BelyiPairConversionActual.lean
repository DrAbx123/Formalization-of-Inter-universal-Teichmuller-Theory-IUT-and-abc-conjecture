import tmp.sheaf.xif.paper.GenEll16BelyiExistenceActual
import tmp.sheaf.xif.paper.Mzk1GeometricCoreRealStructureActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: GeometricCore(iii)|polynomial->scheme|finite map to P1|Belyi|CriticalValues|FiniteMapData -> hits GenEll16BelyiExistenceActual (BelyiPolynomialCertificate + genEll16_belyiCertificate, ported algebraic Belyi FRESH), Mzk1GeometricCoreRealStructureActual (Mzk1FiniteMapData = ported flt_test SmoothProperCurve.FiniteMapData; Mzk1GeometricCoreWitness/Recast), AG_FLT_FiniteMapDataPromotionActual (flt_th alias; NOT imported here to avoid flt_th/flt_test duplicate-namespace clash) -> REUSE (algebraic Belyi + scheme-level finite map) / ADAPT (bridge named).

# [GenEll] 17: GeometricCore (iii) polynomial->scheme finite-map bridge (algebraic route)

Corpus: papers/motizuki_corpus/text/Noncritical Belyi Maps.txt, Thm 2.5 (207-221),
proof 222-281; GeometricCore statement (222-265).
LEAD RULING A197: belyi_pair SPLIT approved - algebraic/Belyi part green canonical
(TauCeti.Algebra.Polynomial.CriticalValues/Belyi via GenEll16), analytic/topology part
(BelyiPair/AnalyticBelyiPair) DEFERRED as independent adaptation subproject and NOT a
dependency here.  This file therefore: (a) consumes the PROVED algebraic Belyi
polynomial certificate; (b) consumes the scheme-level finite-map datum (ported
SmoothProperCurve.FiniteMapData re-exported as Mzk1FiniteMapData); (c) takes the
polynomial->scheme finite-map conversion as a NAMED bridge (GenEll17FiniteMapBridge:
a concrete finiteMap + degree_eq, no abstract replacement); and (d) derives the
Mzk1GeometricCoreRecast from the bridge + the three paper conditions (named inputs).
Three GeometricCore conditions stay named; no Belyi existence is re-proved.
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.GenEll17BelyiPairConversionActual

universe u

open LeanFormal.IUT.XiFPaper.GenEll16BelyiExistenceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open Polynomial
open CategoryTheory AlgebraicGeometry
open NeronModelInfra

/-- **GeometricCore (iii) bridge data:** a scheme-level finite map to P^1 (ported
FiniteMapData) together with the degree relation `m = q.natDegree` to a rational
Belyi polynomial q.  The polynomial->scheme realizability itself is the deferred
paper conversion (A197); here it is represented by the concrete finite-map datum +
the degree equation, both fully consumed by the construction below. -/
structure GenEll17FiniteMapBridge {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (q : ℚ[X]) where
  finiteMap : Mzk1FiniteMapData c ε
  degree_eq : finiteMap.m = q.natDegree

/-- **Bridge -> GeometricCore recast (conditional on the three paper conditions):**
from a positive-degree rational polynomial q, a finite-map bridge for q, and the
three paper conditions (as named inputs with proofs), construct the GeometricCore
witness hence the recast.  Every input is consumed (no decorative field). -/
theorem genEll17_recast_of_bridge {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (q : ℚ[X]) (hq : 0 < q.natDegree)
    (bridge : GenEll17FiniteMapBridge c ε q)
    (mapsT : Prop) (hmapsT : mapsT)
    (unram : Prop) (hunram : unram)
    (pullback : Prop) (hpullback : pullback) :
    Mzk1GeometricCoreRecast c ε T D :=
  ⟨{ finiteMap := bridge.finiteMap
     degree_pos := by rw [bridge.degree_eq]; exact hq
     maps_T_to_zero := mapsT
     maps_T_to_zero_proof := hmapsT
     unramified_over_zero := unram
     unramified_over_zero_proof := hunram
     pullback_iso := pullback
     pullback_iso_proof := hpullback }⟩

/-- **Algebraic Belyi polynomial with positive degree** (consumed ported theorem):
every finite set of algebraic numbers has a nonconstant rational polynomial carrying
it into {0,1} with critical values in {0,1} in every characteristic-zero field. -/
theorem genEll17_belyi_polynomial {K : Type*} [Field K] [Algebra ℚ K]
    {S : Finset K} (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧ (∀ s ∈ S, aeval s q ∈ ({0, 1} : Set K)) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ {0, 1} :=
  genEll16_belyi_poly_aeval hS

/-- The (iii) bridge rows: what is consumed/proved vs the named residuals. -/
def genEll17Rows : List (String × String × String) :=
  [ ("algebraic Belyi polynomial certificate (nonconstant, S -> {0,1}, critical values in {0,1})", "A", "CONSUMED GenEll16BelyiExistenceActual genEll16_belyiCertificate / genEll16_belyi_poly_aeval (ported FRESH Belyi.lean:285/:317)")
  , ("scheme-level finite map to P^1 datum", "A", "Mzk1FiniteMapData = ported flt_test SmoothProperCurve.FiniteMapData (EXIT=0); alias AG_FLT_FiniteMapDataPromotionActual (flt_th) exists but is not co-imported to avoid duplicate namespaces")
  , ("bridge -> GeometricCore recast with three conditions", "A", "PROVED genEll17_recast_of_bridge (bridge finiteMap+degree_eq and three named condition inputs all consumed)")
  , ("polynomial -> scheme finite-map conversion (paper realizability)", "B", "NAMED (BelyiPair/AnalyticBelyiPair closure DEFERRED per A197; not a gate dependency). Bridge represented by concrete finiteMap + degree_eq only")
  , ("three GeometricCore conditions (T -> 0, unramified over 0, O(1)=O(D))", "B", "NAMED Prop inputs; line-bundle/unramified API pending")
  , ("paper hypotheses (smooth proper connected X/Qbar, |T| >= 2g+1)", "B", "NAMED; curve/genus API wiring pending") ]

/-- The (iii) bridge row record has six rows. -/
theorem genEll17Rows_length : genEll17Rows.length = 6 := rfl

#check GenEll17FiniteMapBridge
#check genEll17_recast_of_bridge
#check genEll17_belyi_polynomial
#check genEll17Rows_length

end LeanFormal.IUT.XiFPaper.GenEll17BelyiPairConversionActual
end