/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A878: ROUTES 14 chain 2 - holomorphic-structure family container (interface only) -/

/- DESIGN (not Lean objects from the paper; all fields are data/Props, no theorem claimed):
* `Family v` : type of holomorphic structures compatible with the single analytic data at v;
* `ordH : Family v -> Real` : pilot valuation in a structure;
* `PossibleImageShellVolume : (a b : Real) -> Real` : shell volume of the union
  `P(v,j) = union over structures of (Theta value acting on the log-shell region)`, as a
  function of the allowed ord_h interval [a,b] (data function; no formula asserted);
* `GlobalConstraint (a b : Real) : Prop` : the Step (xii) rigidity restricting the interval;
* criteria:
  - `NoConstraintTooBig` : without G the union is too large / volume bound lost;
  - `ConstraintTooStrong` : with G the q-pilot member leaves the family;
  - `MiddleAlive` : an intermediate constraint keeps the q-pilot member AND the bound.
No experiment executed: no numeric interval or volume is asserted here. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Chain2ContainerInterfaceActual

structure Chain2LocalData where
  structureCount : ℕ
  ordH : ℕ → ℝ
  possibleImageShellVolume : ℝ → ℝ → ℝ
  globalConstraint : ℝ → ℝ → Prop
  qPilotOrd : ℝ

def NoConstraintTooBig (D : Chain2LocalData) : Prop :=
  ∀ a b : ℝ, a < b → D.possibleImageShellVolume a b < D.possibleImageShellVolume a (b + 1)

def ConstraintTooStrong (D : Chain2LocalData) : Prop :=
  ∀ a b : ℝ, D.globalConstraint a b → ¬ (a ≤ D.qPilotOrd ∧ D.qPilotOrd ≤ b)

def MiddleAlive (D : Chain2LocalData) : Prop :=
  ∃ a b : ℝ, D.globalConstraint a b ∧ a ≤ D.qPilotOrd ∧ D.qPilotOrd ≤ b

/-- Decision predicate: chain 2 survives iff an intermediate constraint exists. -/
def Chain2Survives (D : Chain2LocalData) : Prop := MiddleAlive D

def chain2Rows : List (String × String × String) :=
  [ ("holomorphic structure family h(v)", "field holomorphicStructures + ordH", "DATA (design)") ,
    ("possible image P(v,j)", "shell volume as function of [a,b]", "DATA function (not computed)") ,
    ("global constraint G (Step xii)", "globalConstraint : Real -> Real -> Prop", "DATA (design)") ,
    ("no G => bound lost", "NoConstraintTooBig", "CRITERION (not evaluated)") ,
    ("G too strong => q-pilot excluded", "ConstraintTooStrong", "CRITERION (not evaluated)") ,
    ("middle case => chain alive", "MiddleAlive / Chain2Survives", "CRITERION (not evaluated)") ,
    ("local experiment (fixed bad place)", "volume vs interval, then width of G", "NOT EXECUTED") ]

theorem chain2Rows_length : chain2Rows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Chain2ContainerInterfaceActual
