import tmp.sheaf.xif.paper.S2192QHomSheavesActual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2192QHomSheavesActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2206PConstantSheafActual

variable (S : Iut.SchemeOverField S1726K)

/-- The literal constant presheaf of the sign group on the slice site. -/
noncomputable def S2206P0 : ((Over S)ᵒᵖ ⥤ Type) where
  obj _ := Iut.SignGroup
  map _ := ↾ (fun x : Iut.SignGroup => x)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The exact sheaf property missing for the literal constant sign group
presheaf. -/
def S2206P0Sheaf : Prop :=
  Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) (S2206P0 S)

/-- The exact first missing for the P half: either the literal constant
presheaf is a sheaf, or the constant-sheaf/sheafification API is available. -/
def S2206PFirstMissing : Prop :=
  S2206P0Sheaf S ∨ S2192HasWeakSheafify S

/-- R is the actual representable morphism sheaf from S2192. -/
noncomputable abbrev S2206R : ((Over S)ᵒᵖ ⥤ Type) := S2192R S

/-- R is actual a sheaf. -/
theorem S2206R_isSheaf :
    Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S)
      (S2206R S) :=
  S2192R_isSheaf S

/-- The P/R package, conditional on the P sheaf property. -/
structure S2206HomSheaves (hP : S2206P0Sheaf S) where
  P : ((Over S)ᵒᵖ ⥤ Type)
  R : ((Over S)ᵒᵖ ⥤ Type)
  hP' : Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) P
  hR : Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology S1726K).over S) R

/-- Conditional P/R package with actual P0 and actual R. -/
noncomputable def S2206HomSheaves_actual (hP : S2206P0Sheaf S) :
    S2206HomSheaves S hP where
  P := S2206P0 S
  R := S2206R S
  hP' := hP
  hR := S2206R_isSheaf S

/-- The P sheaf property is exactly the remaining input for the literal
constant presheaf model. -/
def S2206FirstMissing : Prop := S2206P0Sheaf S

#print axioms S2206R_isSheaf
#print axioms S2206HomSheaves_actual

end LeanFormal.IUT.XiFPaper.S2206PConstantSheafActual

end
