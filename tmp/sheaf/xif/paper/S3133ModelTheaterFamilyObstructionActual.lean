import tmp.sheaf.xif.paper.S3133ModelHodgeTheaterActual
import tmp.sheaf.xif.paper.S3137ModelTheaterSkeletonActual

/-!
# Model theater-family obstruction (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: qpilot in-model R1 composition,
lattice theater-family skeleton, mainline/lattice model-route record.

FORMAL OBSTRUCTION (recorded): the model theater family cannot be the CONSTANT
theater (modelHodgeTheater l data) over the index Int x Int, because the family
field "distinct" requires the theater map to be injective, while two distinct
indices would have equal theaters.  This file proves the negation explicitly, so
the model-route residual is precisely "an index-dependent model theater family
with refl-compatible links and arithmetic alignment" (a model-construction input,
not a paper-faithfulness residual).
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3133ModelTheaterFamilyObstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S3133ModelVBasisActual
open LeanFormal.IUT.XiFPaper.S3133ModelHodgeTheaterActual
open LeanFormal.IUT.XiFPaper.S3137ModelTheaterSkeletonActual

/-- The two model indices (0,0) and (1,0) are distinct. -/
theorem modelIndex_zero_ne_one :
    (ULift.up ((0, 0) : ModelIndex) : ULift.{0} ModelIndex) ≠
      ULift.up ((1, 0) : ModelIndex) := by
  intro h
  exact absurd (congrArg ULift.down h) (by
    intro h'
    exact absurd (congrArg Prod.fst h') (by norm_num))

/-- The CONSTANT model theater is NOT injective over Int x Int: the model
theater family must be index-dependent. -/
theorem modelConstantTheater_not_injective
    (l : PrimeGeFive) (data : LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual.S3135ModelValueData) :
    ¬ Function.Injective
      (fun (_ : ULift.{0} ModelIndex) => modelHodgeTheater l data) := by
  intro hInj
  exact modelIndex_zero_ne_one
    (hInj (by rfl : modelHodgeTheater l data = modelHodgeTheater l data))

end LeanFormal.IUT.XiFPaper.S3133ModelTheaterFamilyObstructionActual
