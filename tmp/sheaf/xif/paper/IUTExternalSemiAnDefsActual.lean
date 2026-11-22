import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic

/-! # IUTExternalSemiAnDefsActual — E1 [SemiAn] semi-graph definitions (class-D statement layer)

STEP 0 prior-art: deep-search query 'SemiAn|semi-graph|semi-graph of anabelioids|GeoAn|
anabelioid|CbGC|NodNon' -> no LeanFormal/ported definition of semi-graphs or anabelioids
(all hits are unrelated graph theory); papers/motizuki_corpus corpus used for citations.
Reuse: Mathlib CategoryTheory basics only.

CORPUS: Mochizuki, 'Semi-graphs of Anabelioids' ([SemiAn]); 'Absolute Anabelian Cuspidalizations'.

LABEL: class-D external-object definitions (no proof content; proved:=false rows for
statements).  The definitions themselves are honest mathematical structures; no theorem
of this file is counted as a paper result. -/

namespace LeanFormal.IUT.XiFPaper.IUTExternalSemiAnDefsActual

universe u v

/-- A semi-graph ([SemiAn], §1): a set of vertices and a set of edges, each edge with
a source and a target vertex, plus a genus function on vertices. -/
structure SemiGraph where
  V : Type u
  E : Type v
  s : E → V
  t : E → V
  genus : V → ℕ

/-- A morphism of semi-graphs: maps on vertices and edges compatible with source/target
and genus. -/
structure SemiGraphMorphism (G H : SemiGraph.{u, v}) where
  mapV : G.V → H.V
  mapE : G.E → H.E
  mapV_s : ∀ e : G.E, mapV (G.s e) = H.s (mapE e)
  mapV_t : ∀ e : G.E, mapV (G.t e) = H.t (mapE e)
  mapV_genus : ∀ v : G.V, H.genus (mapV v) = G.genus v

/-- The identity morphism of a semi-graph. -/
def SemiGraphMorphism.id (G : SemiGraph.{u, v}) : SemiGraphMorphism G G where
  mapV := fun v => v
  mapE := fun e => e
  mapV_s := fun _ => rfl
  mapV_t := fun _ => rfl
  mapV_genus := fun _ => rfl

/-- Composition of semi-graph morphisms. -/
def SemiGraphMorphism.comp {G H K : SemiGraph.{u, v}}
    (f : SemiGraphMorphism G H) (g : SemiGraphMorphism H K) : SemiGraphMorphism G K where
  mapV := fun v => g.mapV (f.mapV v)
  mapE := fun e => g.mapE (f.mapE e)
  mapV_s := fun e => by rw [f.mapV_s, g.mapV_s]
  mapV_t := fun e => by rw [f.mapV_t, g.mapV_t]
  mapV_genus := fun v => by rw [g.mapV_genus, f.mapV_genus]

/-- Paper-facing statement ledger for [SemiAn] (class D; no proof). -/
structure IUTExternalStatementRow where
  item : String
  corpus : String
  status : String
  proved : Bool

def iutExternalSemiAnStatements : List IUTExternalStatementRow :=
  [ ⟨"semi-graph and morphism definitions", "[SemiAn] §1", "DEFINITION LAYER (this file)", false⟩,
    ⟨"semi-graph of anabelioids", "[SemiAn] §2", "STATEMENT (needs GeoAn anabelioid layer)", false⟩,
    ⟨"fundamental group of a semi-graph of anabelioids", "[SemiAn] §2", "STATEMENT (class D)", false⟩,
    ⟨"tame fundamental group comparison", "[SemiAn] §3", "STATEMENT (class D)", false⟩ ]

theorem iutExternalSemiAnStatements_length : iutExternalSemiAnStatements.length = 4 := rfl

#check SemiGraph
#check SemiGraphMorphism.comp
#check iutExternalSemiAnStatements_length

end LeanFormal.IUT.XiFPaper.IUTExternalSemiAnDefsActual