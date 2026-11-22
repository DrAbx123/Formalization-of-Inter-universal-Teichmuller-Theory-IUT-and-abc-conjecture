import LeanFormal.IUT.ABCBridge.Statement
import tmp.sheaf.xif.paper.Mzk1FinalBoundarySzpiroActual
import Mathlib.Tactic

/-!
# A806 Szpiro upper-bound proposition shape (shehdd)

Shape of the Szpiro upper bound used by the final boundary:

  `SzpiroUpperBound C := ∀ a b c, IsABCTriple a b c →
      Real.log (c : ℝ) ≤ 6 * Real.log (radical (a*b*c) : ℝ) + C`

(`a+b=c` is a field of `IsABCTriple`; `c` is the height; `radical (a*b*c)` the radical).
Proved here (pure real arithmetic, no claim that the bound holds):
* `szpiroUpperBound_iff_epsilon`: the `(1/6)`-form
  `(1/6)·log c ≤ log rad + C/6`;
* `szpiroUpperBound_iff_forall_shape`: per-triple `Szpiro6Shape C (log c) (log rad) 0`
  (`Mzk1FinalBoundarySzpiroActual.Szpiro6Shape`);
* `szpiro6Shape_iff_sixth` re-export in the triple form.

PENDING (not proved here): the upper bound itself, and its exact equivalence with
`LeanFormal.IUT.ABCConjecture` (the paper's Szpiro/ABC equivalence is a separate
estimate; the direction `ABC ⇒ Szpiro` is standard but not formalized here).
No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1SzpiroUpperBoundShapeShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1FinalBoundarySzpiroActual
open scoped BigOperators

/-- Explicit Szpiro upper bound (shape only, constant `C` explicit). -/
def SzpiroUpperBound (C : ℝ) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    Real.log ((c : Nat) : ℝ) ≤
      6 * Real.log (((radical (a * b * c) : Nat) : ℝ)) + C

/-- The `(1/6)`-normalized ε-form (with `ε = 0` absorbed into `C`). -/
def SzpiroUpperBoundSixth (C : ℝ) : Prop :=
  ∀ a b c : Nat, IsABCTriple a b c →
    (1 / 6) * Real.log ((c : Nat) : ℝ) ≤
      Real.log (((radical (a * b * c) : Nat) : ℝ)) + C / 6

/-- Equivalence of the two shapes (pure arithmetic on each triple). -/
theorem szpiroUpperBound_iff_epsilon :
    SzpiroUpperBound C ↔ SzpiroUpperBoundSixth C := by
  unfold SzpiroUpperBound SzpiroUpperBoundSixth
  constructor
  · intro h a b c htri
    have h1 := h a b c htri
    nlinarith
  · intro h a b c htri
    have h1 := h a b c htri
    nlinarith

/-- Per-triple form with the boundary `Szpiro6Shape`: `log c ≤ 6·(log rad + 0) + C`. -/
theorem szpiroUpperBound_iff_forall_shape :
    SzpiroUpperBound C ↔
      ∀ a b c : Nat, IsABCTriple a b c →
        Szpiro6Shape (Real.log ((c : Nat) : ℝ))
          (Real.log (((radical (a * b * c) : Nat) : ℝ))) C := by
  unfold SzpiroUpperBound Szpiro6Shape
  constructor <;> intro h a b c htri
  · simpa using h a b c htri
  · simpa using h a b c htri

/-- The `(1/6)`-form of `Szpiro6Shape` (re-export, per triple). -/
theorem szpiro6Shape_iff_sixth_triple (C : ℝ) (a b c : Nat) (htri : IsABCTriple a b c) :
    Szpiro6Shape (Real.log ((c : Nat) : ℝ))
        (Real.log (((radical (a * b * c) : Nat) : ℝ))) C ↔
      (1 / 6) * Real.log ((c : Nat) : ℝ) ≤
        Real.log (((radical (a * b * c) : Nat) : ℝ)) + C / 6 :=
  szpiro6Shape_iff_epsilon (Real.log ((c : Nat) : ℝ))
    (Real.log (((radical (a * b * c) : Nat) : ℝ))) C

structure SzpiroShapeRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def szpiroShapeRows : List SzpiroShapeRow :=
  [ ⟨"SzpiroUpperBound", "∀ ABC triples, log c <= 6 log rad(abc) + C", "DEF (explicit C)"⟩
  , ⟨"epsilon form", "SzpiroUpperBound <-> (1/6)log c <= log rad + C/6", "PROVED"⟩
  , ⟨"Szpiro6Shape form", "SzpiroUpperBound <-> per-triple Szpiro6Shape C (log c) (log rad) 0", "PROVED"⟩
  , ⟨"ABC/Szpiro equivalence", "SzpiroUpperBound <-> ABCConjecture (paper estimate)", "PENDING"⟩
  , ⟨"upper bound itself", "inhabit SzpiroUpperBound C for some C", "PENDING (open ABC-strength input)"⟩
  , ⟨"scope", "shape only; no retracted use; no fake bound", "INTEGRITY"⟩
  ]

theorem szpiroShapeRows_length : szpiroShapeRows.length = 6 := rfl

theorem szpiroShapeRows_has_pending :
    szpiroShapeRows.any (fun r => r.status = "PENDING (open ABC-strength input)") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1SzpiroUpperBoundShapeShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1SzpiroUpperBoundShapeShaActual.szpiroUpperBound_iff_epsilon
#print axioms LeanFormal.IUT.XiFPaper.Mzk1SzpiroUpperBoundShapeShaActual.szpiroUpperBound_iff_forall_shape
#print axioms LeanFormal.IUT.XiFPaper.Mzk1SzpiroUpperBoundShapeShaActual.szpiro6Shape_iff_sixth_triple
