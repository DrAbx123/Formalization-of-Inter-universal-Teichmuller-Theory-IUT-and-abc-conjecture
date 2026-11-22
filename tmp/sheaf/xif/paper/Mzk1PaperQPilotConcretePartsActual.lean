/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.PaperQPilotObject
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import Mathlib.Tactic
/-! # GAP: concrete PaperQPilotObject parts vs PaperQPilotObjectActual fields -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotConcretePartsActual
open LeanFormal.IUT LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
universe ua uv upi umon ui uL uC uG
variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
structure ConcretePaperQPilotParts
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) where
  strip : FPrimeStrip V
  strip_eq : strip = O.strip
  oneColumn : SourceOneColumnArithmeticHolomorphicStructure V
  oneColumn_eq : oneColumn = O.oneColumn
  logKummer : SourceKummerArrow G envStrip O.strip
  logKummer_eq : logKummer = O.logKummer
theorem concreteParts_strip (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (D : ConcretePaperQPilotParts O) : D.strip = O.strip := D.strip_eq
def rows : List String := ["strip (FPrimeStrip)", "oneColumn (match)", "logKummer (SourceKummerArrow)", "PActual.line.C2 requires SourceLogKummerData (TYPE MISMATCH)"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotConcretePartsActual
end