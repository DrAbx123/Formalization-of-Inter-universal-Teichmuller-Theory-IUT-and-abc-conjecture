import tmp.sheaf.xif.paper.Mzk1GeomCoreBridgeInterfaceActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreFoundationActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreBridgeLegacyActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: scheme<->function-field bridge (DAG foundation:D.bridgeLegacy / Dbridge-* advances) -> ZeroDivisorDatum (Mzk1GeomCoreBridgeInterfaceActual) + FibreBridgeAbstract + legacy Foundation FibreOverZeroEq/restated witness + BridgeLegacy fibreOverZeroEq_of_bridge/restatedWitness_of_bridge -> CONSUMER: zero-divisor datum + bridge => fibre condition and restated precise witness (T = image of datum.T). No new math beyond rewriting the bridge fibre T with the RR-side datum; no closure.

# Mzk1GeomCoreZeroDatumFibreActual — RR zero-divisor datum => scheme fibre (conditional)

PROVED:
* `fibreOverZeroEq_of_zeroDatum`: if the bridge's T-places are exactly the zero-divisor
  datum's T, then the fibre over zero of fm.f is the image of the datum's T;
* `restatedWitness_of_zeroDatum`: adding positive degree, generic etaleness and pullback
  degree yields the legacy restated precise witness;
* `recast_of_zeroDatum`: the corresponding old recast;
* `zeroDatum_zero_simple` / `zeroDatum_no_other_zero`: datum order facts (PROVED projections).
NAMED: the two bridge maps (sectionMap/placePoint) and the finite-map datum; the RR
zero divisor itself is supplied by the flt_core adapter (zeroDivisorDatum_nonempty_of_RR).
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreZeroDatumFibreActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual.SchemeLayer
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeLegacyActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {F : Type*} [Field F] {P : Type*}

/-- Datum order facts (PROVED projections). -/
theorem zeroDatum_zero_simple (ord : P → F → ℤ) (Z : ZeroDivisorDatum P F ord)
    {t : P} (ht : t ∈ Z.T) : ord t Z.g = 1 := Z.zero_simple t ht

theorem zeroDatum_no_other_zero (ord : P → F → ℤ) (Z : ZeroDivisorDatum P F ord)
    {p : P} (hp : p ∉ Z.T) : ord p Z.g ≤ 0 := Z.no_other_zero p hp

/-- **PROVED:** the bridge fibre condition with the zero-divisor datum's T. -/
theorem fibreOverZeroEq_of_zeroDatum (ord : P → F → ℤ) (fm : Mzk1FiniteMapData c ε)
    (B : FibreBridgeAbstract C Γ(C, fm.U) F (fm.U : Set C) fm.f
      (C.basicOpen fm.f : Set C) P ord)
    (Z : ZeroDivisorDatum P F ord) (hT : Z.T = B.Tplaces) :
    FibreOverZeroEq c ε fm (B.placePoint '' (Z.T : Set P)) := by
  have h := fibreOverZeroEq_of_bridge ord fm B
  rw [hT]
  exact h

/-- **PROVED (conditional):** RR datum + bridge + finite-map data => restated precise
witness. -/
def restatedWitness_of_zeroDatum (ord : P → F → ℤ) (fm : Mzk1FiniteMapData c ε)
    (hdeg : 0 < fm.m)
    (B : FibreBridgeAbstract C Γ(C, fm.U) F (fm.U : Set C) fm.f
      (C.basicOpen fm.f : Set C) P ord)
    (Z : ZeroDivisorDatum P F ord) (hT : Z.T = B.Tplaces)
    (D : Set C) (hunram : UnramifiedOverZero c ε fm)
    (hpull : PullbackIsoDegree c ε fm D) :
    Mzk1GeometricCoreWitnessPreciseRestated c ε
      (B.placePoint '' (Z.T : Set P)) D :=
  restatedWitness_of_data c ε _ D fm hdeg
    (fibreOverZeroEq_of_zeroDatum ord fm B Z hT) hunram hpull

/-- **PROVED (conditional):** old recast via the zero-datum fibre. -/
theorem recast_of_zeroDatum (ord : P → F → ℤ) (fm : Mzk1FiniteMapData c ε)
    (hdeg : 0 < fm.m)
    (B : FibreBridgeAbstract C Γ(C, fm.U) F (fm.U : Set C) fm.f
      (C.basicOpen fm.f : Set C) P ord)
    (Z : ZeroDivisorDatum P F ord) (hT : Z.T = B.Tplaces)
    (D : Set C) (hunram : UnramifiedOverZero c ε fm)
    (hpull : PullbackIsoDegree c ε fm D) :
    Mzk1GeometricCoreRecast c ε (B.placePoint '' (Z.T : Set P)) D :=
  recast_of_restated ⟨restatedWitness_of_zeroDatum ord fm hdeg B Z hT D hunram hpull⟩

/-- Rows: proved consumer vs named layers. -/
def zeroDatumFibreRows : List (String × String × String) :=
  [ ("zero-divisor datum order facts", "PROVED", "zeroDatum_zero_simple / zeroDatum_no_other_zero")
  , ("datum T + bridge => fibre condition", "PROVED", "fibreOverZeroEq_of_zeroDatum")
  , ("datum + bridge + fm => restated precise witness", "PROVED (conditional)", "restatedWitness_of_zeroDatum")
  , ("datum + bridge + fm => old recast", "PROVED (conditional)", "recast_of_zeroDatum")
  , ("RR zero divisor (flt_core)", "AVAILABLE (separate root)", "Mzk1GeomCoreRRBridgeActual.zeroDivisorDatum_nonempty_of_RR (flt_core adapter; cannot be imported in this flt_test-root file)")
  , ("bridge maps sectionMap/placePoint", "NAMED API GAP", "no Mathlib/ported API links scheme sections/points to function field")
  , ("finite-map datum", "NAMED INPUT", "Mzk1FiniteMapData construction (finite-map chart interface) remains named") ]

theorem zeroDatumFibreRows_length : zeroDatumFibreRows.length = 7 := rfl

#check fibreOverZeroEq_of_zeroDatum
#check restatedWitness_of_zeroDatum
#check recast_of_zeroDatum
#check zeroDatumFibreRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreZeroDatumFibreActual
end