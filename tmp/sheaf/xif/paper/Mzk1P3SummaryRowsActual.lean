import tmp.sheaf.xif.paper.Mzk1P3MassIdentificationActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P3SummaryRowsActual
def p3Rows : List (String × String) :=
  [ ("Mzk1P3TensorCoreActual", "field product + finrank sum (no C3)"),
    ("Mzk1P3NetGainLogActual", "net = log massL - log massQ + C"),
    ("Mzk1P3NetGainSourceGapActual", "source comparison boundary + negative example"),
    ("Mzk1P3NetGainP2Actual", "P2 R1.3 correction; nonneg base preserved"),
    ("Mzk1P3MassIdentificationActual", "native block mass identification reduced to P2 coefficient identity") ]
theorem p3Rows_length : p3Rows.length = 5 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P3SummaryRowsActual