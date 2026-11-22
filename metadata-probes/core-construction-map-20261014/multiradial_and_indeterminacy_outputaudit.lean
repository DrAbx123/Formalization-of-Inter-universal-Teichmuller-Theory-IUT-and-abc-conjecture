/-
  OWNED PROBE (read_write, owner dsh_multiradial_output_owner), iteration 5
  run: core-construction-map-20261014
  purpose: finish bounded name-resolution with full Theorem311 namespace
  qualification, so absence of a multiradial output object is not inferred from
  an unqualified-name artifact. No bodies/paths printed.
-/
import Lean
import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.IUTIII.Theorem311.Obligations
import LeanFormal.IUT.IUTIII.Theorem311.Output.MultiradialAlgorithm
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind1
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind2
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind3
import LeanFormal.IUT.IUTIII.Theorem311.MultiradialOutputKernel
import LeanFormal.IUT.IUTIII.Theorem311.MultiradialProfileKernel

open Lean Elab Command

def candidateNames : List Name :=
  [ `LeanFormal.IUT.IUTIII.Theorem311.MultiradialOutput
  , `LeanFormal.IUT.IUTIII.Theorem311.multiradialOutput
  , `LeanFormal.IUT.IUTIII.Theorem311.MultiradialProfile
  , `LeanFormal.IUT.IUTIII.Theorem311.multiradialProfile
  , `LeanFormal.IUT.IUTIII.Theorem311.MultiradialOutputKernel
  , `LeanFormal.IUT.IUTIII.Theorem311.MultiradialProfileKernel
  , `LeanFormal.IUT.IUTIII.Theorem311.Output
  , `LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
  ]

elab "#resolve2" : command => do
  let env ← Lean.getEnv
  for n in candidateNames do
    match env.find? n with
    | none => logInfo s!"RESOLVES no  {n}"
    | some ci =>
      let kind : String :=
        match ci with
        | .axiomInfo _ => "axiomInfo"
        | .defnInfo d => if d.value.isSorry then "defnInfo(hassorry)" else "defnInfo"
        | .thmInfo t => if t.value.isSorry then "thmInfo(hassorry)" else "thmInfo"
        | .opaqueInfo _ => "opaqueInfo"
        | .quotInfo _ => "quotInfo"
        | .inductInfo _ => "inductInfo"
        | .ctorInfo _ => "ctorInfo"
        | .recInfo _ => "recInfo"
      let modName : String :=
        match env.getModuleFor? n with
        | some m => m.toString
        | none => "<none>"
      logInfo s!"RESOLVES yes {n} kind={kind} module={modName}"

#resolve2
