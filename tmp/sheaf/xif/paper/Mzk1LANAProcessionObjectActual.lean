import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# LANA Procession object (IUT I Def 4.10 / IUT III Thm 3.11 input)

Reference object layer over LANA `Procession`, `Hom`, and `Procession.map`.
No definition is rewritten; the file records the mapped-procession object
and its component equality. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LANAProcessionObjectActual

universe u v u' v'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {n : Nat}

/-- The LANA procession input object of Theorem 3.11(i). -/
abbrev ProcessionInput (C : Type u) [Category.{v} C] (n : Nat) := Procession C n

/-- Image of a procession under a functor, using LANA's `Procession.map`. -/
def mappedProcession (F : C ⥤ D) (P : Procession C n) : Procession D n :=
  (Procession.map F).obj P

theorem mappedProcession_obj (F : C ⥤ D) (P : Procession C n)
    (j : Fin n) (t : Fin (j + 1)) :
    (mappedProcession F P).obj j t = F.obj (P.obj j t) :=
  rfl

theorem mappedProcession_id (P : Procession C n) :
    mappedProcession (𝟭 C) P = P := by
  cases P
  rfl

theorem mappedProcession_comp (F : C ⥤ D) {E : Type*} [Category E]
    (G : D ⥤ E) (P : Procession C n) :
    mappedProcession (F ⋙ G) P = mappedProcession G (mappedProcession F P) := by
  cases P
  rfl

theorem procession_input_groupoid (C : Type u) [Category.{v} C] (n : Nat) :
    Groupoid (ProcessionInput C n) :=
  inferInstance

end LeanFormal.IUT.XiFPaper.Mzk1LANAProcessionObjectActual

end
