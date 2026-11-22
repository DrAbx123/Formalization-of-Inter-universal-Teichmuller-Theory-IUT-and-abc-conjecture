import tmp.sheaf.xif.paper.AbsTopIII05Section0ObjectsActual
import tmp.sheaf.xif.paper.Mzk1Prop58iiDiagramActual

/-!
# Mzk1P58iiCor55RowsActual — typed Cor-5.5 auxiliary ordered-set model (L, L-dagger)

STEP 0 prior-art: AbsTopIII05Section0ObjectsActual (Cor55L = Z, Cor55Ldagger = WithBot Z,
cor55_square_lt/cor55_L_embeds), Mzk1Prop58iiDiagramActual (cor55DiagramRows) -> REUSE;
this file bundles the Cor-5.5 auxiliary ordered set data as a typed structure and shows the
concrete instance is inhabited.

No axiom/sorry; registry frozen 14041.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P58iiCor55RowsActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramActual

/-- The typed auxiliary ordered-set model of Cor 5.5: L (countably ordered set determined by
the first row) and L-dagger (L with a formal symbol square appended below all L). -/
structure Cor55DaggerModel where
  /-- the countably ordered set L (in the tree model: Z). -/
  L : Type
  /-- L with the formal symbol square appended below every element. -/
  Ldagger : Type
  /-- the linear order on L-dagger. -/
  instLinear : LinearOrder Ldagger
  /-- the formal symbol square. -/
  square : Ldagger
  /-- square is below every element of L-dagger. -/
  square_le : ∀ x : Ldagger, square ≤ x
  /-- the inclusion of L into L-dagger. -/
  embed : L → Ldagger
  /-- every embedded element lies strictly above square. -/
  square_lt_embed : ∀ x : L, square < embed x

/-- The concrete Cor-5.5 auxiliary ordered-set model (L = Z, L-dagger = WithBot Z). -/
def cor55DaggerModelConcrete : Cor55DaggerModel where
  L := Cor55L
  Ldagger := Cor55Ldagger
  instLinear := cor55_Ldagger_linearOrder
  square := ⊥
  square_le := cor55_square_lt
  embed := WithBot.some
  square_lt_embed := cor55_L_embeds

/-- The typed Cor-5.5 auxiliary model is inhabited. -/
theorem cor55DaggerModel_nonempty : Nonempty Cor55DaggerModel :=
  ⟨cor55DaggerModelConcrete⟩

/-- The Cor-5.5 auxiliary model rows: (item, content, status). -/
def cor55AuxRows : List (String × String × String) :=
  [ ("L as countably ordered set", "Cor55L = Z", "CONSTRUCTED"),
    ("L-dagger = L with formal symbol square", "Cor55Ldagger = WithBot Z", "CONSTRUCTED"),
    ("square below every element", "cor55_square_lt", "PROVED"),
    ("L embeds strictly above square", "cor55_L_embeds", "PROVED"),
    ("typed auxiliary model", "Cor55DaggerModel + cor55DaggerModelConcrete", "CONSTRUCTED/INHABITED"),
    ("seven-row D^bullet diagram", "cor55DiagramRows (P58) + this auxiliary model", "DATA ROWS (construction NAMED)") ]

/-- The Cor-5.5 auxiliary row record has six rows. -/
theorem cor55AuxRows_length : cor55AuxRows.length = 6 := rfl

#check Cor55DaggerModel
#check cor55DaggerModelConcrete
#check cor55DaggerModel_nonempty
#check cor55AuxRows_length

end LeanFormal.IUT.XiFPaper.Mzk1P58iiCor55RowsActual
end
