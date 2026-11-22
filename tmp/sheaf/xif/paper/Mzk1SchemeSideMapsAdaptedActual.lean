import tmp.sheaf.xif.paper.Mzk1GeomCoreBridgeInterfaceActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreFiniteMapChartInterfaceActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# Mzk1SchemeSideMapsAdaptedActual (adapted copy, A475 reuse) — scheme-side maps interface

A472: implements the scheme-side maps stub
(iut-pre-stage4:D.gap.schemeSideMaps): sectionMap : Gamma(C,U) -> F and
placePoint : P -> C, using the existing bridge interface + chart data
assets (no new math). Real Lean; no sorry/axioms. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1SchemeSideMapsAdaptedActual

open CategoryTheory AlgebraicGeometry
open NeronModelInfra
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreBridgeInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreFiniteMapChartInterfaceActual

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {F : Type*} [Field F] {P : Type*}

/-- Scheme-side data: a finite map chart plus the two bridge maps. -/
structure SchemeSideMapsData
    (fm : Mzk1FiniteMapData c ε) (ord : P → F → ℤ) where
  /-- map from sections on the chart open to the function field -/
  sectionMap : Γ(C, fm.U) → F
  /-- map from places to points of the curve -/
  placePoint : P → C
  placePoint_mem_U : ∀ p : P, placePoint p ∈ (fm.U : Set C)

/-- The maps extracted from a bridge interface on a chart. -/
def schemeSideMapsDataOfBridge
    (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord) :
    SchemeSideMapsData X.toFiniteMapData ord :=
  { sectionMap := B.sectionMap
    placePoint := B.placePoint
    placePoint_mem_U := fun p => B.placePoint_mem_U p }

/-- Section map of the extracted data is the bridge section map. -/
theorem schemeSideMaps_sectionMap
    (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord) :
    (schemeSideMapsDataOfBridge ord X B).sectionMap = B.sectionMap := rfl

/-- Place point map of the extracted data is the bridge place map. -/
theorem schemeSideMaps_placePoint
    (ord : P → F → ℤ) (X : FiniteMapChartData c ε)
    (B : FibreBridgeAbstract C Γ(C, X.U) F (X.U : Set C) X.f
      (C.basicOpen X.f : Set C) P ord) :
    (schemeSideMapsDataOfBridge ord X B).placePoint = B.placePoint := rfl

def schemeSideMapsRows : List (String × String × String) :=
  [ ("scheme-side maps data", "DEFINED", "SchemeSideMapsData"),
    ("extraction from bridge", "PROVED", "schemeSideMapsDataOfBridge"),
    ("sectionMap projection", "PROVED", "schemeSideMaps_sectionMap"),
    ("placePoint projection", "PROVED", "schemeSideMaps_placePoint") ]

theorem schemeSideMapsRows_length : schemeSideMapsRows.length = 4 := rfl

#check schemeSideMapsDataOfBridge
#check schemeSideMapsRows_length

end LeanFormal.IUT.XiFPaper.Mzk1SchemeSideMapsAdaptedActual
end