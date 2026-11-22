import tmp.sheaf.xif.paper.Mzk1GeometricCoreRealStructureActual
import tmp.sheaf.xif.paper.GeomCore01StatementActual
import tmp.sheaf.xif.paper.GenEll05Theorem21Actual
import tmp.sheaf.xif.paper.Mzk1Theorem25StatementActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: GeometricCoreStatement|Mzk1GeometricCoreRecast|RR|Serre|Cech|BelyiPair|CriticalValues -> hits Mzk1GeometricCoreRealStructureActual (Mzk1FiniteMapData/Witness/Recast over ported FiniteMapData), GeomCore01StatementActual/GeomCore03AssemblyActual, GenEll05Theorem21Actual, Mzk1Theorem25StatementActual (placeholder True), and AG_FLT_ProvedTheoremsPromotionActual (CITABLE 3 decls: promotion_serrePairing_bijective_and_flip_bijective / promotion_weilDualityAdelic_of_isAlgClosed / promotion_cechRiemannRoch_of_genusReached = COMPLETE ported proofs) -> REUSE (RR/Serde/Cech real content CONSUMED instead of named hypotheses). TauCeti Belyi assets ported sources present (BelyiPair/CriticalValues/Belyi pending oleans; BelyiReduction built) -> cited for finite-map existence, not re-proved.

# [GenEll] 15: GeometricCore statement/recast assembly (precise statement + RR/Serde consumption)

Corpus: papers/motizuki_corpus/text/Noncritical Belyi Maps.txt, Theorem 2.5 lines
207-221 (proof 222-281); GeometricCore statement (paper proof 222-265).
TASK (Lead): (1) precise GeometricCore statement replacing the True placeholder in
the migrated real-structure semantics; (2) construct Mzk1GeometricCoreRecast from
explicit data; (3) consume the qpilot AG_FLT proved-theorems promotion (real
ported Serre/Weil/Cech proofs) as the RR/duality content instead of named
hypotheses.
HONESTY: the paper hypotheses (smooth proper connected curve over Qbar, |T| >= 2g+1)
and the line-bundle/unramified APIs are NOT yet expressible; finite-map existence
remains the named deep input (Belyi assets cited; port pending).  No Belyi existence
re-proved; no placeholder exploited.  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.GenEll15GeometricCoreAssemblyActual

universe u

open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.GeomCore01StatementActual
open LeanFormal.IUT.XiFPaper.GenEll05Theorem21Actual
open AlgebraicCurve KaehlerDifferential
open CategoryTheory AlgebraicGeometry
open NeronModelInfra

/-- **Precise GeometricCore statement (migrated real-structure semantics):** for
every curve datum, the finite-map-to-P^1 witness of GeometricCore exists.  This
replaces the True placeholder: it is the migrated encoding of the paper statement
(smooth proper connected curve over Qbar encoded by (C, c, ε) with ported
FiniteMapData), and the paper hypotheses/conditions are recorded as ledger items.
NOT True. -/
def GenEll15GeometricCoreStatement : Prop :=
  ∀ {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C),
    Mzk1GeometricCoreRecast c ε T D

/-- The recast is exactly the nonemptiness of the witness (migrated semantics). -/
theorem genEll15_recast_iff {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C) :
    Mzk1GeometricCoreRecast c ε T D ↔
      Nonempty (Mzk1GeometricCoreWitness c ε T D) :=
  Iff.rfl

/-- **Explicit-data construction of the recast:** from a ported finite-map datum of
positive degree and the three paper conditions (as named inputs with proofs, kept
abstract until the line-bundle/unramified APIs land), the GeometricCore recast
holds.  Every input is consumed. -/
theorem genEll15_recast_of_data {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (fm : Mzk1FiniteMapData c ε) (hdeg : 0 < fm.m)
    (mapsT : Prop) (hmapsT : mapsT)
    (unram : Prop) (hunram : unram)
    (pullback : Prop) (hpullback : pullback) :
    Mzk1GeometricCoreRecast c ε T D :=
  ⟨{ finiteMap := fm
     degree_pos := hdeg
     maps_T_to_zero := mapsT
     maps_T_to_zero_proof := hmapsT
     unramified_over_zero := unram
     unramified_over_zero_proof := hunram
     pullback_iso := pullback
     pullback_iso_proof := hpullback }⟩

/-- A given GeometricCore witness yields the recast (definitional). -/
theorem genEll15_recast_of_witness {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (w : Mzk1GeometricCoreWitness c ε T D) :
    Mzk1GeometricCoreRecast c ε T D :=
  ⟨w⟩

/-- Belyi asset rows (TauCeti ported sources; olean status; intended consumption).
Preferred existence source for the remaining GeometricCore content: do NOT re-prove
Belyi existence. -/
def genEll15BelyiAssets : List (String × String × String) :=
  [ ("tmp/external/ported/belyi_pair/TauCeti/Analysis/Complex/RiemannSurface/BelyiPair.lean (68KB)",
      "PORTED FRESH EXIT=0 (tauceti_belyi_core; Apache-2.0)",
      "Belyi pair/critical-values layer available; polynomial Belyification consumed in GenEll16BelyiExistenceActual")
  , ("tmp/external/ported/belyi_pair/TauCeti/Algebra/Polynomial/CriticalValues.lean",
      "PORTED FRESH EXIT=0 (CriticalValues.lean, tauceti_belyi_core)",
      "critical-values API available: supports the unramified-over-0 condition")
  , ("tmp/external/ported/belyi_poly/TauCeti/Algebra/Polynomial/Belyi.lean",
      "PORTED FRESH EXIT=0 (Belyi.lean, tauceti_belyi_core)",
      "polynomial Belyification CONSUMED in GenEll16BelyiExistenceActual")
  , ("tmp/external/ported/belyi_poly/TauCeti/FieldTheory/Minpoly/BelyiReduction.lean",
      "olean BUILT (reusable now)",
      "Belyi reduction step: consumable for [Mzk1] Thm 2.5 reduction")
  , ("TauCeti/Analysis/Complex/RiemannSurface/BelyiPair.lean + ThricePuncturedSphere/FilledCover/AnalyticBelyiPair.lean",
      "upstream (Apache-2.0); exists_polynomial_aeval_mem_criticalValues_subset = polynomial Belyification",
      "cite; port only the closure actually consumed (per Lead: report for qpilot port)") ]

/-- The Belyi asset record has five rows. -/
theorem genEll15BelyiAssets_length : genEll15BelyiAssets.length = 5 := rfl

/-- GeometricCore assembly rows: precise/proved vs named residuals. -/
def genEll15Rows : List (String × String × String) :=
  [ ("precise GeometricCore statement (replaces True placeholder)", "A (statement)", "DEFINED GenEll15GeometricCoreStatement = forall data, Mzk1GeometricCoreRecast (NOT True)")
  , ("recast = Nonempty witness", "A", "PROVED genEll15_recast_iff (definitional)")
  , ("explicit-data recast construction", "A", "PROVED genEll15_recast_of_data (finite map + degree + three named condition inputs consumed)")
  , ("witness -> recast", "A", "PROVED genEll15_recast_of_witness")
  , ("Serre pairing + flip bijective (RR/Serde content)", "A", "CONSUMED in GenEll15bRRConsumptionActual (AG_FLT promotion; COMPLETE ported proof)")
  , ("adelic Weil duality over alg-closed K", "A", "CONSUMED in GenEll15bRRConsumptionActual (AG_FLT promotion; COMPLETE ported proof)")
  , ("Cech Riemann-Roch at reached genus", "A", "CONSUMED in GenEll15bRRConsumptionActual (AG_FLT promotion; COMPLETE ported proof)")
  , ("paper hypotheses (smooth proper connected X/Qbar, |T| >= 2g+1)", "B", "NAMED; curve/genus API wiring pending")
  , ("three paper conditions (maps T to 0, unramified over 0, pullback O(1) = O(D))", "B", "NAMED Prop inputs; line-bundle/unramified-morphism API pending")
  , ("finite-map existence (GeometricCore construction)", "B", "NAMED deep input; preferred sources = Tauceti Belyi assets (port pending qpilot) + RR promotion")
  , ("replace placeholder body in Mzk1Theorem25StatementActual", "coordination", "requires mainline/stage4 approval (consumers GenEll05Theorem21Actual, GeomCore03AssemblyActual, Mzk1CorePaperInput)") ]

/-- The GeometricCore assembly row record has eleven rows. -/
theorem genEll15Rows_length : genEll15Rows.length = 11 := rfl

#check GenEll15GeometricCoreStatement
#check genEll15_recast_iff
#check genEll15_recast_of_data
#check genEll15BelyiAssets_length
#check genEll15Rows_length

end LeanFormal.IUT.XiFPaper.GenEll15GeometricCoreAssemblyActual
end