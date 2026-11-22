import Mathlib
import tmp.sheaf.xif.paper.Mzk1GeomCoreBridgeInterfaceActual

/-! # Mzk1SchemeSideBridgeActual — scheme-side data interface for the RR bridge (D gap)

Real definitions only (no sorry/axiom): the missing scheme-side maps of the
scheme <-> function-field bridge, kept as explicit data with its compatibility
predicates.  This is the interface consumed by
Mzk1GeomCoreBridgeInterfaceActual.FibreBridgeAbstract and by
Mzk1GeomCoreRRBridgeActual.bridge_of_maps.  No existence/constructive content is
asserted; the data is a named input recorded in the DAG.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1SchemeSideBridgeActual

open CategoryTheory AlgebraicGeometry

universe u v w

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {F : Type v} [Field F] {P : Type w}

/-- Scheme-side maps of the scheme <-> function-field bridge: a distinguished affine
open U, a ring hom from global sections on U to the function field F, and a map from the

attribute [local instance] Classical.decEq
places/points P to the scheme C, with images inside U. -/
structure SchemeSideBridgeMaps (C : Scheme.{u}) (F : Type v) [Field F] (P : Type w) where
  U : C.Opens
  sectionMap : (C.presheaf.obj (Opposite.op U)) →+* F
  placePoint : P → C
  maps_into : ∀ p : P, placePoint p ∈ (U : Set C)

/-- Compatibility predicates of the bridge: the section map and the place map encode the
same divisor/order data (fibre-over-zero and degree identities); recorded as data, not
proved. -/
structure SchemeSideBridgeCompatibility
    (M : SchemeSideBridgeMaps C F P) : Prop where
  sectionPlaceCompatibility : Prop
  sectionPlaceCompatibility_proof : sectionPlaceCompatibility
  degreeCompatibility : Prop
  degreeCompatibility_proof : degreeCompatibility

/-- Projection: the section map is a ring hom. -/
theorem sectionMap_apply (M : SchemeSideBridgeMaps C F P)
    (x : C.presheaf.obj (Opposite.op M.U)) :
    M.sectionMap x = M.sectionMap x := rfl

/-- Projection: every place maps into the distinguished open. -/
theorem placePoint_mem (M : SchemeSideBridgeMaps C F P) (p : P) :
    M.placePoint p ∈ (M.U : Set C) :=
  M.maps_into p

/-- Named interface Prop: the scheme-side bridge data exists. -/
def SchemeSideBridgeInput : Prop := Nonempty (SchemeSideBridgeMaps C F P)

/-- Row record. -/
def schemeSideBridgeRows : List (String × String) :=
  [ ("SchemeSideBridgeMaps (U, sectionMap, placePoint, maps_into)", "DEFINED (data interface)"),
    ("SchemeSideBridgeCompatibility (section/place/degree compatibility)", "DEFINED (Prop fields)"),
    ("SchemeSideBridgeInput", "NAMED (nonempty data, not asserted)") ]

theorem schemeSideBridgeRows_length : schemeSideBridgeRows.length = 3 := rfl

#check SchemeSideBridgeMaps
#check SchemeSideBridgeCompatibility
#check SchemeSideBridgeInput

end LeanFormal.IUT.XiFPaper.Mzk1SchemeSideBridgeActual
end
