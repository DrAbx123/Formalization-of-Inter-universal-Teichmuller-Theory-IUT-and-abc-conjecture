import tmp.sheaf.xif.paper.S1976AbstractDaggerFActionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1962R1AbstractActionActual
open LeanFormal.IUT.XiFPaper.S1976AbstractDaggerFActionActual

namespace S1976Consumer

example :
    ¬ ∀ F : FPrimeStrip.{0, 0, 0} PUnit,
      R1AbstractActionOnDaggerFMissing F PUnit.unit :=
  no_uniform_construction

example {V : Type} (F : FPrimeStrip.{0, 0, 0} V) (v : V) :
    R1AbstractActionOnDaggerFMissing F v ↔
      DaggerFActionSourceCondition F v :=
  R1AbstractActionOnDaggerFMissing_iff_sourceCondition F v

example (v : FinitePrimePlace 2 7) :
    R1AbstractActionOnDaggerFMissing
      (LeanFormal.IUT.XiFPaper.S1962R1AbstractActionActual.localFPrimeStrip v) PUnit.unit :=
  localGvAction_missing v

example (v : FinitePrimePlace 2 7) :
    (localGvActionOfDescends v).action =
      (LeanFormal.IUT.XiFPaper.S1962R1AbstractActionActual.localFPrimeStrip v).action PUnit.unit :=
  localGvAction_action v

example :
    ¬ R1AbstractActionOnDaggerFMissing
      nondescendingFPrimeStrip PUnit.unit :=
  nondescendingFPrimeStrip_noAction

example :
    ∃ F G : FPrimeStrip.{0, 0, 0} PUnit,
      F.toDPrimeStrip = G.toDPrimeStrip ∧
      F.Mon = G.Mon ∧
      R1AbstractActionOnDaggerFMissing F PUnit.unit ∧
      ¬ R1AbstractActionOnDaggerFMissing G PUnit.unit :=
  action_not_determined_by_DPrimeStrip

end S1976Consumer