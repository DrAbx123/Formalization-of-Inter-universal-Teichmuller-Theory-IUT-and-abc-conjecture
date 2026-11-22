import tmp.sheaf.xif.paper.S3135ModelValueDataActual
import tmp.sheaf.xif.paper.S3133ModelVBasisActual
import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore

/-!
# Model FPrimeStrip for the from-scratch model (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: qpilot model assembly
(modelHodgeTheater/modelOriginalInput), abc R_model, lattice skeleton wiring.

Builds the model prime strip from abc's constructed value package
S3135ModelValueData: the datum group Pi/G is trivial (model-local units), proj
is the trivial epimorphism, the action is trivial, and Mon/degree come from the
value package by definition (no cross-monoid assumed equalities).
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133ModelFPrimeStripActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3133ModelVBasisActual
open LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual

/-- The model F-prime-strip: trivial Pi/G datum, value monoid and degree supplied
by the constructed model value data. -/
noncomputable def modelFPrimeStrip (data : S3135ModelValueData) :
    FPrimeStrip S3135ModelV where
  Pi := fun _ => Unit
  groupPi := fun _ => inferInstance
  G := fun _ => Unit
  groupG := fun _ => inferInstance
  proj := fun _ => 1
  proj_surjective := fun _ => fun x => ⟨1, Subsingleton.elim _ _⟩
  Mon := fun _ => data.Mon
  commMonoidMon := fun _ => data.commMonoid
  action := fun _ => 1
  degree := fun _ => data.degree

/-- The model prime strip's degree is the value package's degree (rfl). -/
theorem modelFPrimeStrip_degree (data : S3135ModelValueData) :
    (modelFPrimeStrip data).degree = fun _ => data.degree :=
  rfl

/-- The model prime strip's value monoid is the value package's monoid (rfl). -/
theorem modelFPrimeStrip_Mon (data : S3135ModelValueData) :
    (modelFPrimeStrip data).Mon = fun _ => data.Mon :=
  rfl

end LeanFormal.IUT.XiFPaper.S3133ModelFPrimeStripActual
