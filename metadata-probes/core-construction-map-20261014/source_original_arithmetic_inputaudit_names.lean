/-
  Owned audit probe #4 for source_original_arithmetic_input-v1
  (run core-construction-map-20261014, agent dsh_original_input_owner).

  Environment name queries only (no source reads, no bodies).
-/

import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.InitialThetaInputCore
import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary

open Lean Meta

namespace LeanFormal.IUT.AuditProbe4

/-- Print the declaration names in the environment whose name contains `Input`
and whose name mentions `Theorem311`. -/
#eval show MetaM Unit from do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.contains "Theorem311" && n.toString.contains "Input" then
      out := out.push n
  for n in out.qsort (fun a b => a.toString < b.toString) do
    IO.println s!"DECL {n}"

/-- Print the declaration names for `InitialThetaArithmeticData` and `SourceDefinition31Data`
projections. -/
#eval show MetaM Unit from do
  let env ← getEnv
  let mut out : Array Name := #[]
  for (n, _) in env.constants.toList do
    let s := n.toString
    if s.contains "InitialThetaArithmeticData" || s.contains "SourceDefinition31Data" then
      out := out.push n
  for n in out.qsort (fun a b => a.toString < b.toString) do
    IO.println s!"ARITH {n}"

end LeanFormal.IUT.AuditProbe4
