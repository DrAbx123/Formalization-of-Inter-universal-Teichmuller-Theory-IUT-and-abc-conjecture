import tmp.sheaf.xif.paper.Mzk1GeomCorePencilActual
import tmp.sheaf.xif.paper.Mzk1GeomCorePreciseToOldActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: Problem D consolidation (Lead A412/A414) -> sources:
* Mzk1GeomCorePencilActual (19322B, EXIT0 dea52239): REAL function-field layer on the
  ported flt_test API (Place/ord/Divisor/ell/canonicalDivisorOf), REAL free functions
  ell_drop_of_rr, exists_mem_notMem_of_proper (Mathlib finite-union lemma), punctureDivisor
  (degree = |T|), exists_simple_pole_function, exists_function_with_zero_divisor, the
  GeometricCore zero datum, MapsTToZeroOn (vacuity fix), and the RR-conditional
  exists_geometricCore_of_riemannRoch (named inputs hRR and hdual);
* Mzk1GeomCoreRRWitnessActual (30576B, EXIT0 c00698b7): function-field zero_divisor_exists
  (RR-conditional), FibreOverZeroEq (vacuity-fixed scheme condition), the restated precise
  witness and the consumer chain to GenEll15.

# Mzk1GeomCoreFoundationActual — SINGLE CANONICAL Problem D foundation layer

CONSOLIDATION: this file is the canonical foundation; the two sources above are
supplementary/legacy.  It re-exports the RR-INDEPENDENT base layer unchanged (no
re-proof), adds the RR-conditional function-field corollary with named inputs explicit,
and preserves the scheme-level vacuity fix + restated witness + consumer chain.

BEFORE (two parallel implementations):
  RRWitness: ell/pointSum/degree + zero_divisor_exists (RR conditional) + FibreOverZeroEq
             + restated witness + consumer chain;  Pencil: same arithmetic/pencil part +
             punctureDivisor/degree=|T| + MapsTToZeroOn; duplicated definitions, no
             single canonical path.
AFTER (this file):
  * BASE (RR-independent, PROVED, canonical): ell_drop_of_rr,
    exists_mem_notMem_of_proper, PencilData, exists_simple_pole_function,
    exists_function_with_zero_divisor, GeometricCoreZeroDatum,
    exists_geometricCore_zeroDatum, zeroSet_eq_T, zero_divisor_eq_one/_zero/_degree,
    Curve.punctureDivisor (+ apply lemmas, sub_single_le, degree_punctureDivisor = |T|),
    MapsTToZeroOn (+ mapsTToZero_of_on/_of_disjoint/_iff).
  * NOT-YET (RR-conditional, named inputs explicit): zero_divisor_exists consumes
    hRR : FunctionFieldRiemannRoch K F and hdual (dual vanishing; deg<0 => ell=0 is not
    in the ported flt_test API).  Curve.exists_geometricCore_of_riemannRoch remains the
    underlying conditional construction.
  * SCHEME LAYER (PROVED, vacuity fixed): FibreOverZeroEq, fibreOverZeroEq_mapsTToZero,
    fibreOverZeroEq_of_eq_zeroLocus, Mzk1GeometricCoreWitnessPreciseRestated,
    restatedToPrecise/restatedToOld, recast_of_restated, restatedWitness_of_data,
    Mzk1GeometricCoreRecastPreciseRestated, recast_of_recastRestated, consumer links.
  * NOT-YET: scheme <-> function-field bridge (no API linking fm.f on U to F);
    finite map to P^1 (GeometricCore construction) remains a named input.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual

universe u

/-! ## PART 1: canonical BASE layer (RR-independent; re-exported, not re-proved) -/

export LeanFormal.IUT.XiFPaper.Mzk1GeomCorePencilActual
  (ell_drop_of_rr exists_mem_notMem_of_proper PencilData exists_simple_pole_function
   exists_function_with_zero_divisor zeroSet GeometricCoreZeroDatum
   exists_geometricCore_zeroDatum zeroSet_eq_T zero_divisor_eq_one zero_divisor_eq_zero
   zero_divisor_degree)

export LeanFormal.IUT.XiFPaper.Mzk1GeomCorePencilActual
  (MapsTToZeroOn mapsTToZero_of_on mapsTToZero_of_disjoint mapsTToZeroOn_iff)

export LeanFormal.IUT.XiFPaper.Mzk1GeomCorePencilActual.Curve
  (punctureDivisor punctureDivisor_apply_of_mem punctureDivisor_apply_of_notMem
   punctureDivisor_sub_single_le degree_punctureDivisor)

export LeanFormal.IUT.XiFPaper.Mzk1GeomCorePencilActual.Curve
  (GeomCorePencilWitness GeomCorePencilRecast geomCorePencilRows geomCorePencilRows_length)

/-! ## PART 2: RR-conditional function-field corollary (NOT-YET; named inputs explicit) -/

section RRConditional

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1GeomCorePencilActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCorePencilActual.Curve

/-- **NOT-YET (RR-conditional): zero divisor exactly sum_T [t].** Inputs: the named
Riemann-Roch statement `hRR`, the named dual-vanishing input `hdual` (not derivable in
the ported flt_test API: deg(omega) = 2g-2 and 'deg<0 => ell=0' live in incompatible
ported trees), T finite with |T| >= 2g+1.  The construction/order argument is PROVED in
`Curve.exists_geometricCore_of_riemannRoch`; this corollary only extracts the zero
divisor form consumed downstream. -/
theorem zero_divisor_exists {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates]
    {ω : KaehlerDifferential K F} (hω : ω ≠ 0)
    (T : Finset (Place K F)) (hcard : 2 * genus K F + 1 ≤ T.card)
    (hdual : ∀ t ∈ T,
      (ell (canonicalDivisorOf hω - punctureDivisor T) : ℤ) = 0 ∧
      (ell (canonicalDivisorOf hω - (punctureDivisor T - Finsupp.single t (1 : ℤ))) : ℤ) = 0)
    (hRR : FunctionFieldRiemannRoch K F) :
    ∃ g : F, g ≠ 0 ∧ (∀ p : Place K F, 0 < p.ord g ↔ p ∈ T) ∧
      ∀ t ∈ T, t.ord g = 1 := by
  obtain ⟨W⟩ := Curve.exists_geometricCore_of_riemannRoch (K := K) (F := F)
    hω T hcard hdual hRR
  refine ⟨W.g, W.g_ne_zero, ?_, W.zero_simple⟩
  intro p
  constructor
  · intro hp
    by_contra hpT
    exact absurd hp (not_lt.mpr (W.no_other_zero p hpT))
  · intro hp
    rw [W.zero_simple p hp]
    norm_num

end RRConditional

/-! ## PART 3: SCHEME layer — vacuity fix, restated precise witness, consumer chain -/

namespace SchemeLayer

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCorePreciseToOldActual
open LeanFormal.IUT.XiFPaper.GenEll15GeometricCoreAssemblyActual

/-- The fibre over zero is exactly T, without vacuity: T lies in U, and on U the zero
locus of f is exactly T. -/
def FibreOverZeroEq {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (fm : Mzk1FiniteMapData c ε) (T : Set C) : Prop :=
  T ⊆ (fm.U : Set C) ∧
    ∀ t : C, t ∈ (fm.U : Set C) → (t ∉ (C.basicOpen fm.f : Set C) ↔ t ∈ T)

/-- The restated fibre condition implies the old MapsTToZero (strengthening). -/
theorem fibreOverZeroEq_mapsTToZero {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {fm : Mzk1FiniteMapData c ε} {T : Set C} (h : FibreOverZeroEq c ε fm T) :
    MapsTToZero c ε fm T :=
  fun t ht _ => (h.2 t (h.1 ht)).mpr ht

/-- The fibre condition is non-vacuous (T the zero locus of f inside U). -/
theorem fibreOverZeroEq_of_eq_zeroLocus {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {fm : Mzk1FiniteMapData c ε} {T : Set C}
    (hT : T = (fm.U : Set C) \ (C.basicOpen fm.f : Set C)) :
    FibreOverZeroEq c ε fm T := by
  refine ⟨?_, ?_⟩
  · intro t ht
    rw [hT] at ht
    exact ht.1
  · intro t ht
    rw [hT]
    exact ⟨fun h => ⟨ht, h⟩, fun h => h.2⟩

/-- Restated precise geometric-core witness (vacuous MapsTToZero replaced). -/
structure Mzk1GeometricCoreWitnessPreciseRestated {R : Type u} [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C) where
  finiteMap : Mzk1FiniteMapData c ε
  degree_pos : 0 < finiteMap.m
  fibre_zero : FibreOverZeroEq c ε finiteMap T
  unramified_over_zero : UnramifiedOverZero c ε finiteMap
  pullback_iso_degree : PullbackIsoDegree c ε finiteMap D

/-- Restated witness -> old precise witness. -/
def restatedToPrecise {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (w : Mzk1GeometricCoreWitnessPreciseRestated c ε T D) :
    Mzk1GeometricCoreWitnessPrecise c ε T D where
  finiteMap := w.finiteMap
  degree_pos := w.degree_pos
  maps_T_to_zero := fibreOverZeroEq_mapsTToZero w.fibre_zero
  unramified_over_zero := w.unramified_over_zero
  pullback_iso_degree := w.pullback_iso_degree

/-- Restated witness -> old (real-structure) witness. -/
def restatedToOld {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (w : Mzk1GeometricCoreWitnessPreciseRestated c ε T D) :
    Mzk1GeometricCoreWitness c ε T D :=
  toOldWitness (restatedToPrecise w)

/-- Nonempty restated witnesses give the old recast. -/
theorem recast_of_restated {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (h : Nonempty (Mzk1GeometricCoreWitnessPreciseRestated c ε T D)) :
    Mzk1GeometricCoreRecast c ε T D :=
  toOldRecast (h.elim fun w => ⟨restatedToPrecise w⟩)

/-- Conditional construction from explicit data. -/
def restatedWitness_of_data {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (fm : Mzk1FiniteMapData c ε) (hdeg : 0 < fm.m)
    (hfibre : FibreOverZeroEq c ε fm T)
    (hunram : UnramifiedOverZero c ε fm)
    (hpull : PullbackIsoDegree c ε fm D) :
    Mzk1GeometricCoreWitnessPreciseRestated c ε T D :=
  { finiteMap := fm
    degree_pos := hdeg
    fibre_zero := hfibre
    unramified_over_zero := hunram
    pullback_iso_degree := hpull }

/-- Existence of the restated precise witness (data-level recast). -/
def Mzk1GeometricCoreRecastPreciseRestated {R : Type u} [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C) : Prop :=
  Nonempty (Mzk1GeometricCoreWitnessPreciseRestated c ε T D)

/-- Restated recast -> old recast. -/
theorem recast_of_recastRestated {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T D : Set C}
    (h : Mzk1GeometricCoreRecastPreciseRestated c ε T D) :
    Mzk1GeometricCoreRecast c ε T D :=
  recast_of_restated h

/-- Consumer link: restated existence -> old precise existence statement. -/
theorem genEll15GeometricCoreStatementPrecise_of_restated
    (h : ∀ {R : Type u} [CommRing R] {C : Scheme.{u}}
      (c : C ⟶ Spec (CommRingCat.of R))
      (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C),
      Mzk1GeometricCoreRecastPreciseRestated c ε T D) :
    GenEll15GeometricCoreStatementPrecise.{u} :=
  fun c ε T D => (h c ε T D).elim fun w => ⟨restatedToPrecise w⟩

/-- Consumer link into the GenEll15 assembly statement. -/
theorem genEll15GeometricCoreStatement_of_restated
    (h : ∀ {R : Type u} [CommRing R] {C : Scheme.{u}}
      (c : C ⟶ Spec (CommRingCat.of R))
      (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C),
      Mzk1GeometricCoreRecastPreciseRestated c ε T D) :
    GenEll15GeometricCoreStatement.{u} :=
  genEll15GeometricCoreStatement_of_precise
    (genEll15GeometricCoreStatementPrecise_of_restated h)

end SchemeLayer

/-! ## PART 4: BEFORE/AFTER ledger -/

namespace Rows

/-- Consolidation ledger: BEFORE (two parallel files) / AFTER (this canonical file). -/
def problemDRows : List (String × String × String) :=
  [ ("BEFORE: RRWitness (30576B c00698b7)", "SUPPLEMENTARY", "function-field zero_divisor_exists (RR conditional) + FibreOverZeroEq + restated witness + consumer chain")
  , ("BEFORE: Pencil (19322B dea52239)", "SUPPLEMENTARY", "base layer (ell_drop, finite-union, PencilData, simple pole, punctureDivisor degree=|T|, MapsTToZeroOn) + RR-conditional construction")
  , ("AFTER: BASE layer (RR-independent)", "CANONICAL PROVED", "ell_drop_of_rr, exists_mem_notMem_of_proper, PencilData, exists_simple_pole_function, exists_function_with_zero_divisor, GeometricCoreZeroDatum, exists_geometricCore_zeroDatum, zeroSet_eq_T, zero_divisor_eq_one/_zero/_degree, punctureDivisor + degree_punctureDivisor = |T|, MapsTToZeroOn (+ lemmas)")
  , ("AFTER: RR-conditional zero_divisor_exists", "NOT-YET", "named hRR : FunctionFieldRiemannRoch K F + hdual (dual vanishing); underlying Curve.exists_geometricCore_of_riemannRoch")
  , ("AFTER: scheme layer (vacuity fix + restated witness)", "CANONICAL PROVED", "FibreOverZeroEq, restatedToPrecise/ToOld, recast_of_restated, restatedWitness_of_data, recast_of_recastRestated")
  , ("AFTER: consumer chain to GenEll15", "CANONICAL PROVED", "genEll15GeometricCoreStatementPrecise_of_restated, genEll15GeometricCoreStatement_of_restated")
  , ("scheme <-> function-field bridge", "NOT-YET (MISSING API)", "no API linking fm.f (section on U) to a function-field element F")
  , ("finite map to P^1 (GeometricCore construction)", "NAMED INPUT", "Belyi/finite-map existence; conditional construction only") ]

theorem problemDRows_length : problemDRows.length = 8 := rfl

end Rows

#check ell_drop_of_rr
#check exists_mem_notMem_of_proper
#check punctureDivisor
#check degree_punctureDivisor
#check MapsTToZeroOn
#check zero_divisor_exists
#check SchemeLayer.FibreOverZeroEq
#check SchemeLayer.Mzk1GeometricCoreWitnessPreciseRestated
#check SchemeLayer.genEll15GeometricCoreStatement_of_restated
#check Rows.problemDRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual
end