import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic

/-! # IUTExternalGeoAnDefsActual — E1 [GeoAn] anabelioid definitions (class-D statement layer)

STEP 0 prior-art: deep search 'anabelioid|GeoAn|finite coproducts|Galois category' ->
Mathlib has CategoryTheory/Limits/FiniteCoproducts (reused); no LeanFormal anabelioid
definition exists; corpus [GeoAn] used for citations.

CORPUS: Mochizuki, 'Topics in Absolute Anabelian Geometry I' ([AbsTopI]) and
'Absolute Anabelian Cuspidalizations' ([AbsCusp]) for the anabelioid formalism.

LABEL: class-D external-object definitions/statements (proved:=false); no paper
result is claimed. -/

namespace LeanFormal.IUT.XiFPaper.IUTExternalGeoAnDefsActual

open CategoryTheory
open CategoryTheory.Limits

universe u v

/-- An anabelioid ([GeoAn]): a category with finite coproducts. -/
class Anabelioid (C : Type u) [Category.{v} C] : Prop where
  /-- the defining property: finite coproducts exist -/
  hasFiniteCoproducts : HasFiniteCoproducts C

/-- A connected anabelioid: an anabelioid with a chosen point and connectedness data
(recorded as statement fields; class D). -/
structure ConnectedAnabelioid (C : Type u) [Category.{v} C] [Anabelioid C] where
  point : C
  connected : Prop
  connected_proof : connected

/-- Paper-facing statement ledger for [GeoAn] (class D; no proof). -/
structure IUTExternalGeoAnRow where
  item : String
  corpus : String
  status : String
  proved : Bool

def iutExternalGeoAnStatements : List IUTExternalGeoAnRow :=
  [ ⟨"anabelioid definition (category with finite coproducts)", "[GeoAn] §1", "DEFINITION LAYER (this file)", false⟩,
    ⟨"connected anabelioid / point", "[GeoAn] §1", "DEFINITION LAYER (statement fields)", false⟩,
    ⟨"anabelioid fundamental group", "[GeoAn] §2", "STATEMENT (class D)", false⟩,
    ⟨"tempered anabelioid formalism", "[AbsTopI] §1", "STATEMENT (class D)", false⟩ ]

theorem iutExternalGeoAnStatements_length : iutExternalGeoAnStatements.length = 4 := rfl

#check Anabelioid
#check ConnectedAnabelioid
#check iutExternalGeoAnStatements_length

end LeanFormal.IUT.XiFPaper.IUTExternalGeoAnDefsActual