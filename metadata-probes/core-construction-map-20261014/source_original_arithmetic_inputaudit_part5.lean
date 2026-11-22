/-
  Owned audit probe #6 for source_original_arithmetic_input-v1
  (run core-construction-map-20261014, agent dsh_original_input_owner).

  Types only: is the Definition 3.1 orbicurve/torsion data tied to the arithmetic
  curve, or an independent abstract carrier?  No bodies.
-/

import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.InitialThetaInputCore
import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary

set_option linter.unusedVariables false

namespace LeanFormal.IUT.AuditProbe6

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

#check @PuncturedEllipticCurve
#check @PuncturedEllipticCurve.curve
#check @PuncturedEllipticCurve.base
#check @SourceOrbicurveClause.cover
#check @SourceOrbicurveClause.puncturedCurve
#check @SourceExactSequenceClause
#check @SourceExactSequenceClause.injection
#check @SourceExactSequenceClause.projection
#check @SourceExactSequenceClause.sectionMap
#check @SourceTorsionClause.representationCarrier
#check @SourceTorsionClause.representationGroup
#check @SourceSectionClause.valuationCarrier
#check @SourceSectionClause.modifiedValuationCarrier

/-- Print names of declarations whose name mentions `SourceDefinition31Data` and
`orb`/`curve`/`arithmetic` to expose any linkage lemma. -/
#eval show Lean.Meta.MetaM Unit from do
  let env ← Lean.getEnv
  let mut out : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    let s := n.toString
    if s.contains "SourceDefinition31Data" &&
        (s.contains "orb" || s.contains "curve" || s.contains "arithmetic") then
      out := out.push n
  for n in out.qsort (fun a b => a.toString < b.toString) do
    IO.println s!"LINK {n}"

end LeanFormal.IUT.AuditProbe6
