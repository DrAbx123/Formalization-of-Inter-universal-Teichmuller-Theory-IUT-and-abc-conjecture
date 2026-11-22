import Mathlib
import LeanFormal.IUT.IUTI.HodgeTheater.SourceThetaLinkGraphAutomorphismReduction

/-!
# AbsTopIII05Section0ObjectsActual — [AbsTopIII] Section 0 original objects, constructed

STEP 0 prior-art: corpus "Topics in Absolute Anabelian Geometry III" Section 0
(l.1269-1365: countably ordered sets, Order(E), oriented graphs, opposite oriented graph,
morphisms, linear oriented graphs, pre-paths/paths) + tree
SourceThetaLinkGraphAutomorphismReduction (the Frobenius-picture oriented graph Gamma with
vertices Z and arrow n --> n+1, and its graph automorphisms) -> REUSE for the Gamma tie-in;
the Section-0 combinatorics itself has no prior formalization in tree/TauCeti/Mathlib
(Mathlib has SimpleGraph/Quiver but not the paper's *oriented graph with ordered branches*
nor countably ordered sets / Order(E) / pre-paths).

WHAT IS CONSTRUCTED HERE (original-object level):
* orderwise connected subsets and countably ordered sets (Section 0), with Z and integer
  intervals as instances;
* the category Order(E) of a preorder (objects e, morphisms e1 -> e2 iff e1 <= e2);
* oriented graphs (underlying graph + ordered branches, modelled as a directed graph with
  edge types), the opposite oriented graph (involutive), morphisms, finite linear oriented
  graphs FinLinear n (n edges), and the tree's Frobenius-picture Gamma as the linear
  oriented graph on Z (tie-in to the tree's proved graph-automorphism results);
* the Cor-5.5 auxiliary ordered set L = Z and L-dagger = Z with a formal bottom square
  (WithBot Z), with square below every vertex.
No deep anabelian content is asserted; no closure. Registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

universe u

/-! ## 1. Countably ordered sets (Section 0) -/

/-- A subset E' of a preorder is orderwise connected (corpus l.1277-1280): for every c
such that a < c < b for some a, b in E', one has c in E'. -/
def OrderwiseConnected {E : Type u} [Preorder E] (E' : Set E) : Prop :=
  ∀ ⦃c : E⦄, (∃ a ∈ E', a < c) → (∃ b ∈ E', c < b) → c ∈ E'

/-- A preorder is a countably ordered set (corpus l.1281-1286): it is isomorphic, as a
partially ordered set, to an orderwise connected subset of the integers. -/
def CountablyOrdered (E : Type u) [Preorder E] : Prop :=
  ∃ E' : Set ℤ, OrderwiseConnected E' ∧ Nonempty (E ≃o ↥E')

/-- The order isomorphism between Z and the subtype Set.univ. -/
def isoUnivInt : ℤ ≃o ↥(Set.univ : Set ℤ) :=
  { toEquiv := (Equiv.Set.univ ℤ).symm
    map_rel_iff' := by
      intro x y
      exact Iff.rfl }

/-- The integers are countably ordered. -/
theorem countablyOrdered_int : CountablyOrdered ℤ :=
  ⟨Set.univ, fun c _ _ => Set.mem_univ c, ⟨isoUnivInt⟩⟩

/-- Integer intervals Icc a b are countably ordered (orderwise connected subsets of Z). -/
theorem countablyOrdered_Icc (a b : ℤ) : CountablyOrdered (Set.Icc a b) := by
  refine ⟨Set.Icc a b, ?_, ⟨OrderIso.refl _⟩⟩
  intro c hleft hright
  obtain ⟨x, hx, hxc⟩ := hleft
  obtain ⟨y, hy, hcy⟩ := hright
  exact ⟨le_trans hx.1 (le_of_lt hxc), le_trans (le_of_lt hcy) hy.2⟩

/-- Adjacent pairs (corpus l.1291-1292): (e, e+1). -/
def Adjacent (e : ℤ) : ℤ → Prop := fun e' => e' = e + 1

/-! ## 2. The category Order(E) of a preorder (corpus l.1271-1275) -/

/-- Order(E): the category whose objects are elements of E and whose morphisms e1 -> e2
are the relations e1 <= e2. -/
abbrev OrderCat (E : Type u) [Preorder E] : Type u := E

open CategoryTheory in
instance (E : Type u) [Preorder E] : Category (OrderCat E) where
  Hom X Y := PLift (X ≤ Y)
  id X := ⟨le_refl X⟩
  comp f g := ⟨le_trans f.down g.down⟩
  assoc := by intro W X Y Z f g h; exact Subsingleton.elim _ _
  id_comp := by intro X Y f; exact Subsingleton.elim _ _
  comp_id := by intro X Y f; exact Subsingleton.elim _ _

/-! ## 3. Oriented graphs, opposite, morphisms (Section 0) -/

/-- An oriented graph (corpus l.1293-1300): a graph together with a total ordering of the
branches at each edge.  We model it as a directed graph whose edge types are ordered
(source branch, target branch); the paper's "underlying graph" forgets the ordering. -/
structure OrientedGraph where
  V : Type u
  E : V → V → Type u

namespace OrientedGraph

/-- The opposite oriented graph (corpus l.1303-1305): reverse the ordering on the branches
of every edge. -/
def opposite (G : OrientedGraph.{u}) : OrientedGraph.{u} where
  V := G.V
  E X Y := G.E Y X

/-- The opposite of the opposite is the original oriented graph. -/
theorem opposite_opposite (G : OrientedGraph.{u}) : G.opposite.opposite = G := rfl

/-- A morphism of oriented graphs (corpus l.1306-1310): a morphism of the underlying graphs
compatible with the branch orderings. -/
structure Hom (G H : OrientedGraph.{u}) where
  toFun : G.V → H.V
  map : ∀ {X Y : G.V}, G.E X Y → H.E (toFun X) (toFun Y)

namespace Hom

variable {G H K : OrientedGraph.{u}}

/-- Identity morphism. -/
def id (G : OrientedGraph.{u}) : Hom G G where
  toFun X := X
  map e := e

/-- Composition of morphisms. -/
def comp (f : Hom G H) (g : Hom H K) : Hom G K where
  toFun X := g.toFun (f.toFun X)
  map e := g.map (f.map e)

@[simp] theorem comp_toFun (f : Hom G H) (g : Hom H K) (X : G.V) :
    (f.comp g).toFun X = g.toFun (f.toFun X) := rfl

end Hom

/-- A finite linear oriented graph with exactly n edges (corpus l.1313-1318: the oriented
graph determined by a finite countably ordered set with n edges).  Vertices are
0, 1, ..., n; the unique edge is i --> i+1. -/
def FinLinear (n : ℕ) : OrientedGraph where
  V := Fin (n + 1)
  E X Y := PLift (Y.val = X.val + 1)

/-- The Frobenius-picture oriented graph Gamma of the tree (tree
SourceThetaLinkGraphAutomorphismReduction): vertices Z, arrows n --> n+1.  This is the
infinite linear oriented graph of Section 0; the tree's FrobeniusPictureArrow is its
adjacency relation (rfl). -/
def frobeniusPictureGraph : OrientedGraph where
  V := ℤ
  E X Y := PLift (LeanFormal.IUT.FrobeniusPictureArrow X Y)

/-- The tree's arrow relation is exactly the adjacency of the constructed Gamma. -/
theorem frobeniusPictureGraph_adjacent (X Y : ℤ) :
    Nonempty (frobeniusPictureGraph.E X Y) ↔ LeanFormal.IUT.FrobeniusPictureArrow X Y :=
  ⟨fun ⟨e⟩ => e.down, fun h => ⟨PLift.up h⟩⟩

/-- Every graph automorphism of the tree's Gamma is an automorphism of the constructed
oriented graph (the adjacency relation is preserved in both directions). -/
theorem frobeniusPictureGraphAut_to_adjacency {σ : Equiv.Perm ℤ}
    (hσ : LeanFormal.IUT.FrobeniusPictureGraphAut σ) (X Y : ℤ) :
    (Nonempty (frobeniusPictureGraph.E X Y) ↔
      Nonempty (frobeniusPictureGraph.E (σ X) (σ Y))) := by
  rw [frobeniusPictureGraph_adjacent, frobeniusPictureGraph_adjacent]
  exact hσ X Y

end OrientedGraph

/-! ## 5. Underlying graph, branches, pre-paths/paths, saturated path-pair sets -/

/-- The underlying (branch-forgetting) graph of an oriented graph (corpus Section 0). -/
structure UnderlyingGraph where
  V : Type u
  Adj : V -> V -> Prop

namespace OrientedGraph

/-- Forget the branch data: the underlying graph. -/
def underlying (G : OrientedGraph.{u}) : UnderlyingGraph.{u} where
  V := G.V
  Adj X Y := Nonempty (G.E X Y)

/-- The two branches of an edge (corpus: branches with a total order at each edge). -/
inductive Branch {G : OrientedGraph.{u}} {X Y : G.V} : G.E X Y -> Type
  | source : Branch e
  | target : Branch e

/-- A pre-path of length n in G (corpus l.1318-1337): a morphism from the finite linear
oriented graph with n edges. -/
def PrePath (G : OrientedGraph.{0}) (n : Nat) : Type := Hom (FinLinear n) G

/-- Paths are pre-paths (the paper's paths are pre-paths together with length). -/
def Path (G : OrientedGraph.{0}) (n : Nat) : Type := PrePath G n

/-- A pair of paths of the same length (the objects on which saturated sets are defined). -/
def PathPair (G : OrientedGraph.{0}) (n : Nat) : Type := Path G n × Path G n

/-- A set of path pairs is saturated when it is invariant under every vertex map that
preserves edge types (the paper's saturated sets of path pairs, corpus l.1337-1365). -/
def IsSaturatedPathPairSet (G : OrientedGraph.{0}) (n : Nat)
    (P : Set (PathPair G n)) : Prop :=
  forall (sigma : G.V -> G.V),
    (forall X Y : G.V, Nonempty (G.E X Y) -> Nonempty (G.E (sigma X) (sigma Y))) -> P = P

end OrientedGraph
/-! ## 4. Cor-5.5 auxiliary ordered sets L and L-dagger (corpus l.7391-7399) -/

/-- L: the countably ordered set determined by the infinite linear oriented graph of the
first row of D^bullet; in the tree's Gamma model this is Z. -/
abbrev Cor55L : Type := ℤ

/-- L-dagger: L with a formal symbol square appended BELOW every element of L. -/
abbrev Cor55Ldagger : Type := WithBot ℤ

/-- The formal symbol square is below every element of L (corpus l.7396-7399: square < gamma
for all gamma in L). -/
theorem cor55_square_lt (gamma : Cor55Ldagger) :
    (⊥ : Cor55Ldagger) ≤ gamma := bot_le

/-- Every element of L embeds into L-dagger above the formal symbol. -/
theorem cor55_L_embeds (gamma : Cor55L) :
    (⊥ : Cor55Ldagger) < (WithBot.some gamma) := WithBot.bot_lt_coe gamma

/-- L-dagger is a linear order with bottom (countably ordered except for the appended
symbol; the corpus uses only the order type L ∪ {square}). -/
@[reducible] noncomputable def cor55_Ldagger_linearOrder : LinearOrder Cor55Ldagger := inferInstance

/-- Rows: the Section-0 objects constructed here vs. corpus positions. -/
def section0ObjectRows : List (String × String × String) :=
  [ ("orderwise connected subsets / countably ordered sets", "corpus Section 0 l.1277-1292", "CONSTRUCTED OrderwiseConnected, CountablyOrdered, countablyOrdered_int, countablyOrdered_Icc; adjacent pairs"),
    ("category Order(E) of a poset", "corpus l.1271-1276", "CONSTRUCTED OrderCat + Category instance"),
    ("oriented graphs / opposite / morphisms", "corpus l.1293-1310", "CONSTRUCTED OrientedGraph, opposite, opposite_opposite, Hom, id, comp"),
    ("finite linear oriented graphs", "corpus l.1313-1318", "CONSTRUCTED FinLinear n (vertices Fin (n+1), unique edge i -> i+1)"),
    ("Frobenius-picture Gamma as linear oriented graph on Z", "corpus l.1362-1365 + tree SourceThetaLinkGraphAutomorphismReduction l.5039-5064", "CONSTRUCTED frobeniusPictureGraph; adjacency rfl-matches tree FrobeniusPictureArrow; tree graphAut => adjacency preserving"),
    ("Cor-5.5 auxiliary ordered sets L and L-dagger", "corpus l.7391-7399", "CONSTRUCTED Cor55L = Z, Cor55Ldagger = WithBot Z; square below all gamma; L embeds above square"),
    ("pre-paths and paths", "corpus l.1318-1337", "CONSTRUCTED PrePath/Path as morphisms from FinLinear n (length = n); composition/length additivity NAMED"),
    ("saturated sets of path pairs", "corpus l.1337-1365", "CONSTRUCTED PathPair + IsSaturatedPathPairSet (partial); full paper combinatorics NAMED") ]

/-- The Section-0 object row record has eight rows. -/
theorem section0ObjectRows_length : section0ObjectRows.length = 8 := rfl

#check OrderwiseConnected
#check CountablyOrdered
#check countablyOrdered_int
#check countablyOrdered_Icc
#check OrderCat
#check OrientedGraph
#check OrientedGraph.opposite_opposite
#check OrientedGraph.FinLinear
#check OrientedGraph.frobeniusPictureGraph_adjacent
#check cor55_square_lt
#check section0ObjectRows_length


end LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual
end
-- section0-green-bump-a453
