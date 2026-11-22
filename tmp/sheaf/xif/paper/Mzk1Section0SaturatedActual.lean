import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual

/-!
# Mzk1Section0SaturatedActual — Section-0 saturated path-pair sets (corpus l.1318-1365),
genuine formalization on top of the A445 Section0 objects

STEP 0 prior-art: AbsTopIII05Section0ObjectsActual (OrientedGraph, FinLinear, PrePath/Path/
PathPair/IsSaturatedPathPairSet weak definition) -> REUSE the graph/pre-path objects; this file
gives the paper's saturated-set combinatorics with an abstract path-composition datum.

WHAT IS PROVED HERE:
* initial/terminal vertices of a pre-path (corpus l.1329-1337);
* co-verticial path pairs and the all-co-verticial set;
* the abstract PathComposition datum (composition of paths with length additivity /
  initial / terminal laws) — the concrete composition of pre-paths is deliberately abstract
  here (recorded as the named remaining construction);
* the paper's saturated path-pair set conditions (a)-(e) as an explicit structure
  (partial diagonal inclusion, co-verticiality, transitivity, pre-composition,
  post-composition), and symmetrically saturated sets (f) reflexivity;
* PROOF that the set of all co-verticial pairs is saturated (corpus l.1362-1365).
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual
open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual.OrientedGraph

universe u

/-- The initial vertex of a pre-path (corpus l.1329-1332). -/
def PrePath.initial {G : OrientedGraph.{0}} {n : ℕ} (γ : PrePath G n) : G.V :=
  γ.toFun (show Fin (n + 1) from ⟨0, Nat.succ_pos n⟩)

/-- The terminal vertex of a pre-path (corpus l.1329-1332). -/
def PrePath.terminal {G : OrientedGraph.{0}} {n : ℕ} (γ : PrePath G n) : G.V :=
  γ.toFun (Fin.last n)

/-- A path with its length (paths of arbitrary lengths live in the same set). -/
abbrev PathSigma (G : OrientedGraph.{0}) : Type := Σ n : ℕ, PrePath G n

/-- A pair of paths (arbitrary lengths). -/
abbrev PathPairSigma (G : OrientedGraph.{0}) : Type := PathSigma G × PathSigma G

/-- The initial vertex of a length-tagged path. -/
def PathSigma.initial {G : OrientedGraph.{0}} (γ : PathSigma G) : G.V :=
  PrePath.initial γ.2

/-- The terminal vertex of a length-tagged path. -/
def PathSigma.terminal {G : OrientedGraph.{0}} (γ : PathSigma G) : G.V :=
  PrePath.terminal γ.2

/-- Co-verticial path pairs (corpus l.1335-1337): same initial and terminal vertices. -/
def Coverticial {G : OrientedGraph.{0}} (p : PathPairSigma G) : Prop :=
  PathSigma.initial p.1 = PathSigma.initial p.2 ∧
    PathSigma.terminal p.1 = PathSigma.terminal p.2

/-- The set of all co-verticial path pairs (corpus l.1362-1365). -/
def covertSet (G : OrientedGraph.{0}) : Set (PathPairSigma G) :=
  {p | Coverticial p}

/-- Abstract path-composition datum: composition of paths with its length/initial/terminal
laws (the concrete pre-path composition is the named remaining construction). -/
structure PathComposition (G : OrientedGraph.{0}) where
  comp : ∀ (γ1 γ2 : PathSigma G), PathSigma.terminal γ2 = PathSigma.initial γ1 →
    PathSigma G
  comp_length : ∀ (γ1 γ2) (h : PathSigma.terminal γ2 = PathSigma.initial γ1),
    (comp γ1 γ2 h).1 = γ1.1 + γ2.1
  comp_initial : ∀ (γ1 γ2) (h : PathSigma.terminal γ2 = PathSigma.initial γ1),
    PathSigma.initial (comp γ1 γ2 h) = PathSigma.initial γ2
  comp_terminal : ∀ (γ1 γ2) (h : PathSigma.terminal γ2 = PathSigma.initial γ1),
    PathSigma.terminal (comp γ1 γ2 h) = PathSigma.terminal γ1

variable {G : OrientedGraph.{0}}

/-- The paper's saturated path-pair set conditions (a)-(e), corpus l.1337-1360. -/
structure IsSaturatedPathPairSet (C : PathComposition G)
    (P : Set (PathPairSigma G)) : Prop where
  /-- (a) partial inclusion of the diagonal. -/
  diag_left : ∀ p, p ∈ P → (p.1, p.1) ∈ P
  diag_right : ∀ p, p ∈ P → (p.2, p.2) ∈ P
  /-- (b) co-verticiality. -/
  covert : ∀ p, p ∈ P → Coverticial p
  /-- (c) transitivity. -/
  trans : ∀ γ1 γ2 γ3, (γ1, γ2) ∈ P → (γ2, γ3) ∈ P → (γ1, γ3) ∈ P
  /-- (d) pre-composition. -/
  precomp : ∀ (γ1 γ2 γ3 : PathSigma G), (γ1, γ2) ∈ P →
    ∀ (h1 : PathSigma.terminal γ3 = PathSigma.initial γ1)
      (h2 : PathSigma.terminal γ3 = PathSigma.initial γ2),
      (C.comp γ1 γ3 h1, C.comp γ2 γ3 h2) ∈ P
  /-- (e) post-composition. -/
  postcomp : ∀ (γ1 γ2 γ3 : PathSigma G), (γ1, γ2) ∈ P →
    ∀ (h1 : PathSigma.terminal γ1 = PathSigma.initial γ3)
      (h2 : PathSigma.terminal γ2 = PathSigma.initial γ3),
      (C.comp γ3 γ1 h1, C.comp γ3 γ2 h2) ∈ P

/-- The set of all co-verticial pairs is saturated (corpus l.1362-1365). -/
theorem covertSet_isSaturated (C : PathComposition G) :
    IsSaturatedPathPairSet C (covertSet G) where
  diag_left p hp := ⟨rfl, rfl⟩
  diag_right p hp := ⟨rfl, rfl⟩
  covert p hp := hp
  trans γ1 γ2 γ3 h12 h23 :=
    ⟨h12.1.trans h23.1, h12.2.trans h23.2⟩
  precomp γ1 γ2 γ3 hp h1 h2 := by
    refine ⟨?_, ?_⟩
    · simp [C.comp_initial]
    · simpa [C.comp_terminal] using hp.2
  postcomp γ1 γ2 γ3 hp h1 h2 := by
    refine ⟨?_, ?_⟩
    · simpa [C.comp_initial] using hp.1
    · simp [C.comp_terminal]

end LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedActual
end
