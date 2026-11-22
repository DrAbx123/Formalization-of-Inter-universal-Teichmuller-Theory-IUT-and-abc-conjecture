import LeanFormal.IUT.Audit.Status

/-! # S3153: remaining model-inputs watch (i)-(iv)

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (remaining input, owner, current state) rows. -/
def S3153ModelInputsWatch : List (String × String × String) := [
  ("(i) index-dependent injective theater family", "qpilot+lattice", "dispatched constructive route: proj_k on Z x Z, links via GL2(Z); lattice obstruction modelIndex_not_subsingleton to resolve"),
  ("(ii) clause-slot providers", "qpilot/stage4", "torsion/orbicurve/sections/cusp providers per S3136ModelSourceClauseInventoryActual; model data, not paper-faithfulness residuals"),
  ("(iii) bundled source wiring", "qpilot", "modelSource31Data + placeToMod bundled record (frozen SourceDefinition31Data lacks placeToMod field)"),
  ("(iv) full R1 composition", "qpilot", "assemble R1 = M0/M3 proved + M1/M2b discharged with (i)-(iii); current S3133ModelR1Status covers only M1+M2b") ]

theorem S3153ModelInputsWatch_length : S3153ModelInputsWatch.length = 4 := rfl

/-- Model-inputs watch record. -/
def S3153ModelInputsWatchRecord : Obligation :=
  { id := "IUT.project.model-inputs-watch-iii"
    source := "qpilot/lattice task reports; third-reopen audit"
    status := VerificationStatus.interface
    note :=
      "REMAINING MODEL INPUTS (must be green/CITABLE before GO): (i) index-dependent injective "
      ++ "theater family with distinctness+alignment (constructive proj_k route); (ii) clause-slot "
      ++ "providers as model data; (iii) bundled modelSource31Data+placeToMod wiring; (iv) full R1 "
      ++ "composition theorem. Nothing here is a paper-faithfulness residual; they are model "
      ++ "construction duties."
    dependsOn := [ "S3153GoReadinessCriteria" ] }

#check S3153ModelInputsWatchRecord
#check S3153ModelInputsWatch_length

end LeanFormal.IUT.Audit
