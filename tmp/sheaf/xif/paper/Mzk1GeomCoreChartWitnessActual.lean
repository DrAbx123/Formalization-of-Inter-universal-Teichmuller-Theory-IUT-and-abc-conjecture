import tmp.sheaf.xif.paper.Mzk1GeomCoreFiniteMapChartInterfaceActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreBridgeInterfaceActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreFoundationActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreBridgeLegacyActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: finite-map chart interface + bridge => witness (DAG foundation:D.finiteMapChart / bridgeLegacy advance) -> FiniteMapChartData.toFiniteMapData (Mzk1GeomCoreFiniteMapChartInterfaceActual) + FibreBridgeAbstract + Foundation restated witness + BridgeLegacy fibreOverZeroEq_of_bridge -> chart data + bridge maps => restated precise witness; construction of the 16 chart fields stays named. No closure.

# Mzk1GeomCoreChartWitnessActual — chart interface + bridge => restated precise witness

PROVED:
* `chart_fibreOverZeroEq`: bridge data for the chart yields the vacuity-fixed fibre
  condition for the constructed finite map datum;
* `chart_restatedWitness`: adding positive degree, generic etaleness and pullback degree
  yields the legacy restated precise witness;
* `chart_recast`: the corresponding old recast.
NAMED: the 16-field chart construction from the function field and the two bridge maps.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartWitnessActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePreciseActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFoundationActual.SchemeLayer
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeLegacyActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {F : Type*} [Field F] {P : Type*}

/-- **PROVED:** the chart interface plus bridge data gives the fibre condition. -/
theorem chart_fibreOverZeroEq (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord) :
    FibreOverZeroEq c ε X.toFiniteMapData (B.placePoint '' (B.Tplaces : Set P)) := by
  exact fibreOverZeroEq_of_bridge ord X.toFiniteMapData B

/-- **PROVED (conditional):** chart + bridge + degree/unramified/pullback => restated
precise witness. -/
def chart_restatedWitness (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (hdeg : 0 < X.m)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord)
    (D : Set C) (hunram : UnramifiedOverZero c ε X.toFiniteMapData)
    (hpull : PullbackIsoDegree c ε X.toFiniteMapData D) :
    Mzk1GeometricCoreWitnessPreciseRestated c ε
      (B.placePoint '' (B.Tplaces : Set P)) D :=
  restatedWitness_of_data c ε _ D X.toFiniteMapData hdeg
    (chart_fibreOverZeroEq ord X B) hunram hpull

/-- **PROVED (conditional):** old recast from the chart+bridge witness. -/
theorem chart_recast (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (hdeg : 0 < X.m)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord)
    (D : Set C) (hunram : UnramifiedOverZero c ε X.toFiniteMapData)
    (hpull : PullbackIsoDegree c ε X.toFiniteMapData D) :
    Mzk1GeometricCoreRecast c ε (B.placePoint '' (B.Tplaces : Set P)) D :=
  recast_of_restated ⟨chart_restatedWitness ord X hdeg B D hunram hpull⟩

/-- Rows: proved chart+bridge consumer vs named construction. -/
def chartWitnessRows : List (String × String × String) :=
  [ ("chart interface => finite map datum", "PROVED", "FiniteMapChartData.toFiniteMapData (chart interface file)")
  , ("chart + bridge => fibre condition", "PROVED", "chart_fibreOverZeroEq")
  , ("chart + bridge + degree/unramified/pullback => restated witness", "PROVED (conditional)", "chart_restatedWitness")
  , ("chart + bridge => old recast", "PROVED (conditional)", "chart_recast")
  , ("construction of the 16 chart fields from the function field", "NAMED GAP", "finiteMapChartGapText (charts/transition/finiteness/level-set grading)")
  , ("bridge maps sectionMap/placePoint", "NAMED API GAP", "no Mathlib/ported API links scheme sections/points to the function field") ]

theorem chartWitnessRows_length : chartWitnessRows.length = 6 := rfl

#check chart_fibreOverZeroEq
#check chart_restatedWitness
#check chart_recast
#check chartWitnessRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreChartWitnessActual
end