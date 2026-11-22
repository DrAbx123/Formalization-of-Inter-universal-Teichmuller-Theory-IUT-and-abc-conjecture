/-! # IUTExternalEtThStatementsActual — E3 [EtTh] thetalogs statements index

STEP 0 prior-art: our EtTh00-07 files exist in tmp/sheaf/xif/paper (some green per
shehdd audit: EtTh00/01/02/05 CITABLE; EtTh03 green after fix; EtTh04 green after
eta fix; EtTh06/07 status to be confirmed).  Ported assets not needed.

CORPUS: Mochizuki, 'The Etale Theta Function and its Frobenioid-theoretic
Manifestations' ([EtTh]); [IUTchII] theta values.

LABEL: class-D statement index (proved:=false rows); file statuses recorded honestly;
no paper theorem claimed in this file. -/

namespace LeanFormal.IUT.XiFPaper.IUTExternalEtThStatementsActual

structure IUTExternalEtThRow where
  file : String
  topic : String
  status : String
  proved : Bool

def iutExternalEtThStatements : List IUTExternalEtThRow :=
  [ ⟨"EtTh00Stage0LedgerActual", "stage0 ledger", "CITABLE (shehdd audit)", false⟩,
    ⟨"EtTh01OddThetaSeriesActual", "odd theta series", "CITABLE (shehdd audit)", false⟩,
    ⟨"EtTh01StatementActual", "statement layer", "checker pending", false⟩,
    ⟨"EtTh02DeepInputsActual", "deep inputs", "CITABLE (shehdd audit)", false⟩,
    ⟨"EtTh02ShiftLawActual", "shift law", "checker pending (missing olean seen earlier)", false⟩,
    ⟨"EtTh03EtaleThetaGroupActual", "etale theta group", "GREEN after fix (fresh checker pending)", false⟩,
    ⟨"EtTh03TreeReuseActual", "tree reuse", "checker pending", false⟩,
    ⟨"EtTh04QPilotDataActual", "q-pilot data", "CITABLE 4193B (shehdd audit)", false⟩,
    ⟨"EtTh04RouteWiringActual", "route wiring", "checker pending", false⟩,
    ⟨"EtTh05FrobenioidBoundaryActual", "frobenioid boundary", "CITABLE (shehdd audit)", false⟩,
    ⟨"EtTh05PaperInputsActual", "paper inputs", "checker pending", false⟩,
    ⟨"EtTh06ThetaQuotientActual", "theta quotient", "checker pending", false⟩,
    ⟨"EtTh06ThetaGroupObjectActual", "theta group object", "checker pending", false⟩,
    ⟨"EtTh07ThetaFunctionValuesActual", "theta values", "checker pending", false⟩ ]

theorem iutExternalEtThStatements_length : iutExternalEtThStatements.length = 14 := rfl

#check iutExternalEtThStatements_length

end LeanFormal.IUT.XiFPaper.IUTExternalEtThStatementsActual