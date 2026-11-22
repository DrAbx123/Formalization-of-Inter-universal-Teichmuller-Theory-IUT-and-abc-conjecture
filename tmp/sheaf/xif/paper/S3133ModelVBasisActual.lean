import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample

/-!
# Frozen model place basis (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: lattice placeToMod wiring
(S3137ModelPlaceToModConstructionActual), abc model theta-pilot/wrapper,
qpilot task-72 model assembly.

Frozen base data for the from-scratch Example 3.6/Gaussian model: the place
index set is the sum of one nonarchimedean place (the concrete five place) and
one archimedean place; vFive and vInf are the two distinguished places.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133ModelVBasisActual

/-- The model place index set: nonarchimedean part (five place) sum
archimedean part. -/
abbrev S3135ModelPlace : Type := Sum (Fin 1) (Fin 1)

/-- The model place index. -/
abbrev S3135ModelV : Type := S3135ModelPlace

/-- The distinguished nonarchimedean model place. -/
def vFive : S3135ModelV := Sum.inl 0

/-- The distinguished archimedean model place. -/
def vInf : S3135ModelV := Sum.inr 0

/-- The two distinguished model places are distinct. -/
theorem vFive_ne_vInf : vFive ≠ vInf := by
  decide

end LeanFormal.IUT.XiFPaper.S3133ModelVBasisActual
