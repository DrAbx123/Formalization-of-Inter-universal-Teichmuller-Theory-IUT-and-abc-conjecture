import tmp.sheaf.xif.paper.Mzk1GeomCoreFoundationActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreBridgeInterfaceActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: scheme<->function-field bridge (Lead A427/A428) -> root-neutral interface Mzk1GeomCoreBridgeInterfaceActual (EXIT0 210300 SIZE 6352: ZeroDivisorDatum/FibreBridgeAbstract/zeroSet_eq_of_abstract) + legacy scheme layer Mzk1GeomCoreFoundationActual (FibreOverZeroEq/restated witness) -> ADAPT legacy adapter: derive FibreOverZeroEq + restated precise witness from bridge data; finite-map construction route analysis in rows.

# Mzk1GeomCoreBridgeLegacyActual — flt_test-side adapter of the root-neutral bridge

SOLUTION TO ROOT CONFLICT: flt_test (scheme layer: Mzk1FiniteMapData) and flt_core
(RR/function field) cannot be imported together.  The bridge interface is root-neutral
(Mathlib only); this file is the flt_test-side adapter, a separate flt_core-side adapter
(Mzk1GeomCoreRRBridgeActual) supplies ZeroDivisorDatum from RR.  Together they define the
conditional scheme<->field connection WITHOUT importing both roots in one file.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeLegacyActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual.SchemeLayer
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {F : Type*} [Field F] {P : Type*}

/-- **Bridge => vacuity-fixed fibre condition (flt_test side).**  Given the finite map
datum and the root-neutral bridge data (placePoint/sectionMap + compatibility), the fibre
over zero of fm.f is exactly the image of the bridge's T-places. -/
theorem fibreOverZeroEq_of_bridge (ord : P → F → ℤ) (fm : Mzk1FiniteMapData c ε)
    (B : FibreBridgeAbstract C Γ(C, fm.U) F (fm.U : Set C) fm.f
      (C.basicOpen fm.f : Set C) P ord) :
    FibreOverZeroEq c ε fm (B.placePoint '' (B.Tplaces : Set P)) := by
  have h := zeroSet_eq_of_abstract B
  refine ⟨?_, ?_⟩
  · rintro t ⟨p, hp, rfl⟩
    exact B.placePoint_mem_U p hp
  · intro t htU
    constructor
    · intro htb
      have hmem : t ∈ ({t : C | t ∈ (fm.U : Set C) ∧
          t ∉ (C.basicOpen fm.f : Set C)} : Set C) := ⟨htU, htb⟩
      rw [h] at hmem
      exact hmem
    · intro ht
      have hmem : t ∈ ({t : C | t ∈ (fm.U : Set C) ∧
          t ∉ (C.basicOpen fm.f : Set C)} : Set C) := by
        rw [h]
        exact ht
      exact hmem.2

/-- **Bridge + finite-map data => restated precise witness.**  The bridge supplies the
non-vacuous fibre condition; positive degree, generic etaleness and the pullback degree
bookkeeping remain explicit inputs (unramified-over-zero and the line-bundle/degree
layer are named). -/
def restatedWitness_of_bridge (ord : P → F → ℤ) (fm : Mzk1FiniteMapData c ε)
    (hdeg : 0 < fm.m)
    (B : FibreBridgeAbstract C Γ(C, fm.U) F (fm.U : Set C) fm.f
      (C.basicOpen fm.f : Set C) P ord)
    (D : Set C) (hunram : UnramifiedOverZero c ε fm)
    (hpull : PullbackIsoDegree c ε fm D) :
    Mzk1GeometricCoreWitnessPreciseRestated c ε
      (B.placePoint '' (B.Tplaces : Set P)) D :=
  restatedWitness_of_data c ε _ D fm hdeg (fibreOverZeroEq_of_bridge ord fm B) hunram hpull

/-- Bridge + datum => old recast (conditional). -/
theorem recast_of_bridge (ord : P → F → ℤ) (fm : Mzk1FiniteMapData c ε)
    (hdeg : 0 < fm.m)
    (B : FibreBridgeAbstract C Γ(C, fm.U) F (fm.U : Set C) fm.f
      (C.basicOpen fm.f : Set C) P ord)
    (D : Set C) (hunram : UnramifiedOverZero c ε fm)
    (hpull : PullbackIsoDegree c ε fm D) :
    Mzk1GeometricCoreRecast c ε (B.placePoint '' (B.Tplaces : Set P)) D :=
  recast_of_restated ⟨restatedWitness_of_bridge ord fm hdeg B D hunram hpull⟩

/-- Rows: bridge adapter status + finite-map construction route analysis. -/
def bridgeLegacyRows : List (String × String × String) :=
  [ ("root-neutral bridge interface", "REUSED", "Mzk1GeomCoreBridgeInterfaceActual (EXIT0 210300): ZeroDivisorDatum/FibreBridgeAbstract/zeroSet_eq_of_abstract")
  , ("bridge => FibreOverZeroEq (flt_test side)", "PROVED", "fibreOverZeroEq_of_bridge (uses zeroSet_eq_of_abstract)")
  , ("bridge + fm => restated precise witness", "PROVED (conditional)", "restatedWitness_of_bridge: positive degree + unramified-over-zero + pullback degree remain inputs")
  , ("bridge => old recast", "PROVED (conditional)", "recast_of_bridge")
  , ("sectionMap : Gamma(C,U) ->+* F", "NAMED API GAP", "no Mathlib/ported API links a scheme section ring to a function field")
  , ("placePoint : P -> C", "NAMED API GAP", "no API links function-field places to scheme points")
  , ("finite-map construction from a function field", "NOT-YET (route analysis)", "ported Mzk1FiniteMapData is a DATUM (two affine opens U,V + sections f,g + grading); no constructor from a function-field element exists. Route: from g with zero divisor sum_T (flt_core side) build f := g on the chart U where g is regular and the second chart V around the poles; needs (i) a two-affine-open cover of C with gluing to P^1 (Mathlib has no projective-scheme morphism API), (ii) transition compatibility, (iii) generic-etale/level-set grading. Extensible points: reuse ported Scheme.TwoAffineOpenCover API (algebraOfHom), LevelSetsGenericallyEtale fields; Belyi polynomial gives P^1->P^1 only, NOT a map from C")
  , ("finite-map existence", "NAMED INPUT", "remains the named construction input; bridge makes the fibre condition non-vacuous once provided") ]

theorem bridgeLegacyRows_length : bridgeLegacyRows.length = 8 := rfl

#check fibreOverZeroEq_of_bridge
#check restatedWitness_of_bridge
#check recast_of_bridge
#check bridgeLegacyRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeLegacyActual
end