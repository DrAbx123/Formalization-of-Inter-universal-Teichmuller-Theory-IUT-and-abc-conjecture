import tmp.sheaf.xif.paper.EtTh11ThetaRealizationRowsActual
import tmp.sheaf.xif.paper.Mzk1EtThRealizationConsumerActual
import tmp.sheaf.xif.paper.Mzk1EtThRow6RealizationActual
import tmp.sheaf.xif.paper.Mzk1KummerThetaInterfaceActual

/-!
# Mzk1EtThRealizationRowsSummaryActual — EtTh realization rows 1-7 with their current
formalized anchors (asset-first summary)

STEP 0 prior-art: EtTh11ThetaRealizationRowsActual (7 rows: 4 A-class proved/reused,
3 class-B named), Mzk1EtThRealizationConsumerActual (conditional realization bundle),
Mzk1EtThRow6RealizationActual (carrier-level row-6 package), Mzk1KummerThetaInterfaceActual
(Kummer/theta interface for the theta-side anchors) -> REUSE; no new deep mathematics.

WHAT THIS FILE DOES:
* gives one structured row per EtTh realization row: (row number, class, formalized anchor,
  status), with the exact declarations/files for the A-class rows and the carrier-level
  partial anchors for the three class-B rows;
* proves the row count and records the named status of the class-B rows (no closure claim).
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1EtThRealizationRowsSummaryActual

open LeanFormal.IUT.XiFPaper.EtTh11ThetaRealizationRowsActual
open LeanFormal.IUT.XiFPaper.Mzk1EtThRealizationConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1EtThRow6RealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerThetaInterfaceActual

/-- One EtTh realization row with its formalized anchor and status. -/
structure EtThRealizationRowStatus where
  row : Fin 7
  /-- A-class (proved/reused) or B-class (named paper input). -/
  klass : String
  /-- the formalized anchor declarations/files. -/
  anchor : String
  /-- proved / conditional / named. -/
  status : String

/-- The seven EtTh realization rows with anchors: rows 1-4 A-class (proved/reused),
rows 5-7 class-B named (with carrier-level partial anchors recorded). -/
def etthRealizationRowStatus : List EtThRealizationRowStatus :=
  [ ⟨⟨0, by omega⟩, "A", "etTh11_thetaPowerKernel_mono (EtTh11)", "PROVED"⟩
  , ⟨⟨1, by omega⟩, "A", "etTh11_ellipticPowerKernel_mono (EtTh11)", "PROVED"⟩
  , ⟨⟨2, by omega⟩, "A", "modL projections surjectivity (EtaleThetaQuotient:93-140, re-exported EtTh11)", "PROVED/REUSED"⟩
  , ⟨⟨3, by omega⟩, "A", "thetaCenter_le_center (EtaleThetaQuotient:142-150, EtTh08 re-export)", "PROVED/REUSED"⟩
  , ⟨⟨4, by omega⟩, "B", "geometric realization of the theta groups: NAMED; carrier-level ThetaQuotientInterface/KummerLayerInterface (IKT) + P58R package", "NAMED (partial carriers)"⟩
  , ⟨⟨5, by omega⟩, "B", "Frobenioid-theoretic manifestation: NAMED; EtTh05 boundary + Example36<->EtTh bundle (X1) + row-6 carrier (P58R)", "NAMED (partial carrier)"⟩
  , ⟨⟨6, by omega⟩, "B", "actual theta transformation on realized object: NAMED; needs the realized object first", "NAMED"⟩ ]

/-- The summary has exactly the seven EtTh realization rows. -/
theorem etthRealizationRowStatus_length : etthRealizationRowStatus.length = 7 := rfl

/-- Rows 1-4 are the A-class (proved/reused) rows. -/
theorem etthRealizationRowStatus_A_rows :
    (etthRealizationRowStatus.filter (fun r => r.klass == "A")).length = 4 := rfl

/-- Rows 5-7 are the class-B named rows. -/
theorem etthRealizationRowStatus_B_rows :
    (etthRealizationRowStatus.filter (fun r => r.klass == "B")).length = 3 := rfl

/-- Summary rows: (item, anchor asset, status). -/
def etthRealizationSummaryRows : List (String × String × String) :=
  [ ("EtTh realization rows 1-4 (A-class)", "EtTh11 rows + EtaleThetaQuotient (power kernels/projections/center)", "PROVED/REUSED"),
    ("EtTh realization row 5 (geometric realization)", "NAMED + carrier-level IKT (Kummer/theta interface) + P58R (row-6 carrier)", "CONDITIONAL (carrier-level only)"),
    ("EtTh realization row 6 (Frobenioid manifestation)", "NAMED + EtTh05 boundary + X1 (Example36<->EtTh) + P58R", "CONDITIONAL (carrier-level only)"),
    ("EtTh realization row 7 (actual theta transformation)", "NAMED (needs realized object)", "NAMED") ]

/-- The summary row record has four rows. -/
theorem etthRealizationSummaryRows_length : etthRealizationSummaryRows.length = 4 := rfl

#check EtThRealizationRowStatus
#check etthRealizationRowStatus_length
#check etthRealizationRowStatus_A_rows
#check etthRealizationRowStatus_B_rows
#check etthRealizationSummaryRows_length

end LeanFormal.IUT.XiFPaper.Mzk1EtThRealizationRowsSummaryActual
end
