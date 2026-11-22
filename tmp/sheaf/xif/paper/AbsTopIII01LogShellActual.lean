import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: logShellScale|principalUnitLogShell|integralLogShell|SourceLogShellCarrier -> hits LeanFormal/IUT/IUTII/Kummer/SourceLocalLogShellDatum.lean:32 sourceLogShellStar_eq_logShellScale; SourceLogShellCarrier.lean:176/182/186/190 -> REUSE (re-export only; no re-proof).

# [AbsTopIII] 01: Def 5.6 / Prop 5.8 (v) concrete log-shell dictionary (C items)

Corpus: papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt.
- Def 5.6 (log-shells, p-adic side): tree anchor integralLogShell +
  SourceLocalLogShellDatum:32 sourceLogShellStar_eq_logShellScale.
- Prop 5.8 (v) (Psi_cns + direct factors + ±1 actions): elementary part =
  log-shell additive closure and invariant-unit landing (SourceLogShellCarrier:176/182/186/190).
All reused from the tree; no re-proof.  Deep reconstruction (Prop 5.8 (i),(ii))
is NOT claimed here (see AbsTopIII05ReconstructionInputsActual).
-/

namespace LeanFormal.IUT.XiFPaper.AbsTopIII01LogShellActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT

/-- source factor p* = actual local log-shell scale (Def 5.6 dictionary; reuse). -/
theorem absTopIII_sourceLogShellStar_eq_logShellScale {p : Nat} (hp : p.Prime) :
    sourceLogShellStar p = logShellScale p :=
  sourceLogShellStar_eq_logShellScale hp

/-- Concrete log-shell contains 0 (elementary; reuse). -/
theorem absTopIII_logShell_zero_mem (D : SourceLogShellDatum) :
    (0 : D.K) ∈ D.logShell :=
  zero_mem_logShell D

/-- Concrete log-shell closed under addition (elementary; reuse). -/
theorem absTopIII_logShell_add_mem (D : SourceLogShellDatum) {x y : D.K}
    (hx : x ∈ D.logShell) (hy : y ∈ D.logShell) : x + y ∈ D.logShell :=
  add_mem_logShell D hx hy

/-- Invariant units land in the concrete log-shell (principal-unit and ±1 action shape; reuse). -/
theorem absTopIII_invariant_unitLog_mem_logShell (D : SourceLogShellDatum)
    {u : D.Units} (hu : u ∈ D.invariants) :
    (D.logMap u).toAdd ∈ D.logShell :=
  invariant_unitLog_mem_logShell D hu

/-- Dictionary record: [AbsTopIII] log-shell item -> concrete tree anchor. -/
structure AbsTopIIILogShellAnchor where
  item : String
  corpus : String
  tree : List String

/-- The log-shell dictionary (Def 5.6; Prop 5.8 (v) elementary part). -/
def AbsTopIIILogShellAnchors : List AbsTopIIILogShellAnchor :=
  [ { item := "Def 5.6 log-shells (p-adic)",
      corpus := "AbsTopIII corpus ~5284 (Def 5.6)",
      tree := ["Foundations/LocalFields integralLogShell", "SourceLogShellDatum",
        "SourceLocalLogShellDatum:32 sourceLogShellStar_eq_logShellScale"] }
  , { item := "Prop 5.8 (v) direct factors / ±1 actions (elementary part)",
      corpus := "AbsTopIII corpus ~8100-8200 (Prop 5.8(v))",
      tree := ["SourceLogShellCarrier:176 invariant_unitLog_mem_preLogShell",
        "SourceLogShellCarrier:182 invariant_unitLog_mem_logShell",
        "SourceLogShellCarrier:186 zero_mem_logShell",
        "SourceLogShellCarrier:190 add_mem_logShell",
        "SourceLogShellActionCompatibility:87/127/145 (actions preserve logShell)"] } ]

/-- The log-shell dictionary has two entries. -/
theorem AbsTopIIILogShellAnchors_length : AbsTopIIILogShellAnchors.length = 2 := rfl

#check absTopIII_sourceLogShellStar_eq_logShellScale
#check absTopIII_logShell_zero_mem
#check absTopIII_logShell_add_mem
#check absTopIII_invariant_unitLog_mem_logShell
#check AbsTopIIILogShellAnchors
#check AbsTopIIILogShellAnchors_length

end LeanFormal.IUT.XiFPaper.AbsTopIII01LogShellActual