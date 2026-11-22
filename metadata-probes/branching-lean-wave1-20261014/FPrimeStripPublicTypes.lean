/-
  Public-type reflection probe for the F/D prime-strip interface consumed by
  SourcePacketDegreeLedger.  This file prints only compiler public metadata:
  full types, universe parameters, argument structure, declaration kind,
  declaration module and axiom scope names.  No declaration value, proof body,
  implementation or dependency source is printed or read.
-/

import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2OriginalArrows
import LeanFormal.IUT.IUTI.HodgeTheater.LinkVolumeTransport
import Lean

set_option pp.all true
set_option pp.universes true
set_option pp.explicit true
set_option maxHeartbeats 0

open Lean Elab Command Term Meta

elab "#declmeta " t:term : command => do
  let e ← liftTermElabM <| elabTerm t none
  let e ← liftTermElabM <| instantiateMVars e
  let some nm := e.getAppFn.constName?
    | throwError "not a constant: {t}"
  if nm == ``sorryAx then
    throwError "no declaration resolved for {t}"
  let env ← getEnv
  let some ci := env.find? nm
    | throwError "missing constant {nm}"
  let kind := match ci with
    | .axiomInfo _  => "axiom"
    | .defnInfo _   => "def"
    | .thmInfo _    => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _   => "quot"
    | .inductInfo _ => "inductive"
    | .ctorInfo _   => "constructor"
    | .recInfo _    => "recursor"
  let modName := match env.getModuleIdxFor? nm with
    | some i => (env.header.moduleNames[i]!).toString
    | none   => "<no-module>"
  logInfo m!"DECLMETA name={nm} kind={kind} module={modName} levelParams={ci.levelParams}"

#check LeanFormal.IUT.FPrimeStrip
#check LeanFormal.IUT.DPrimeStrip
#check LeanFormal.IUT.FPrimeStripEquiv
#check @LeanFormal.IUT.FPrimeStrip.toD
#check @LeanFormal.IUT.FPrimeStrip.toDPrimeStrip
#check @LeanFormal.IUT.FPrimeStrip.Mon
#check @LeanFormal.IUT.DPrimeStrip.Pi
#check @LeanFormal.IUT.FPrimeStrip.action
#check @LeanFormal.IUT.FPrimeStrip.degree
#check @LeanFormal.IUT.FPrimeStrip.totalDegree
#check @LeanFormal.IUT.FPrimeStripEquiv.isoPi
#check @LeanFormal.IUT.FPrimeStripEquiv.isoMon
#check @LeanFormal.IUT.FPrimeStripEquiv.isoG

#declmeta LeanFormal.IUT.FPrimeStrip
#declmeta LeanFormal.IUT.DPrimeStrip
#declmeta LeanFormal.IUT.FPrimeStripEquiv
#declmeta LeanFormal.IUT.FPrimeStrip.toD
#declmeta LeanFormal.IUT.FPrimeStrip.toDPrimeStrip
#declmeta LeanFormal.IUT.FPrimeStrip.Mon
#declmeta LeanFormal.IUT.DPrimeStrip.Pi
#declmeta LeanFormal.IUT.FPrimeStrip.action
#declmeta LeanFormal.IUT.FPrimeStrip.degree
#declmeta LeanFormal.IUT.FPrimeStrip.totalDegree
#declmeta LeanFormal.IUT.FPrimeStripEquiv.isoPi
#declmeta LeanFormal.IUT.FPrimeStripEquiv.isoMon
#declmeta LeanFormal.IUT.FPrimeStripEquiv.isoG

#print axioms LeanFormal.IUT.FPrimeStrip.action
#print axioms LeanFormal.IUT.FPrimeStripEquiv.isoPi
#print axioms LeanFormal.IUT.FPrimeStripEquiv.isoMon
