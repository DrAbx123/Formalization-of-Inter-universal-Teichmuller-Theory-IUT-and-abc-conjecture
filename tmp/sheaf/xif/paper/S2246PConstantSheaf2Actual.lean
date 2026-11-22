import tmp.sheaf.xif.paper.S2239PConstantSheafActual
import Mathlib.CategoryTheory.Sites.LeftExact

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2239PConstantSheafActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2246PConstantSheaf2Actual

variable (S : Iut.SchemeOverField S1726K)

/-- The universe-lifted Type-valued sheafification is available from Mathlib's
plus construction. -/
def S2246HasWeakSheafifyUp : Prop :=
  Nonempty (HasWeakSheafify ((Iut.SchemeOverField.etaleTopology S1726K).over S) (Type 1))

/-- Actual instance for the lifted universe. -/
theorem S2246HasWeakSheafifyUp_actual : S2246HasWeakSheafifyUp S :=
  ⟨inferInstance⟩

/-- The lifted constant sign group sheaf. -/
noncomputable def S2246P :
    Sheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) (Type 1) :=
  (constantSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) (Type 1)).obj
    (ULift.{1, 0} Iut.SignGroup)

/-- Its underlying presheaf. -/
noncomputable abbrev S2246P_presheaf :
    ((Over S)ᵒᵖ ⥤ Type 1) :=
  (S2246P S).1

/-- The lifted constant sign group sheaf is actual a sheaf. -/
theorem S2246P_isSheaf :
    Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S)
      (S2246P_presheaf S) :=
  (S2246P S).2

/-- The exact bridge still missing: descending the lifted Type 1 constant sheaf
to Type 0. -/
def S2246Type0Bridge : Prop :=
  Nonempty (HasWeakSheafify ((Iut.SchemeOverField.etaleTopology S1726K).over S) Type)

/-- The minimal first missing for the original Type 0 P. -/
def S2246FirstMissing : Prop := S2246Type0Bridge S

#print axioms S2246HasWeakSheafifyUp_actual
#print axioms S2246P_isSheaf

end LeanFormal.IUT.XiFPaper.S2246PConstantSheaf2Actual

end
