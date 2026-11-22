import tmp.sheaf.xif.paper.Mzk1P3TensorCoreActual
import tmp.sheaf.xif.paper.Mzk1P2TensorDetFactorActual
/-! P2 tensor-product isometry attempt: exact status -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P2TensorProductIsometryActual
def isometryAttemptRows : List String :=
  [ "B2 field product equivalence (green)",
    "no canonical isometry tensor <-> Pi product",
    "det factor would require arbitrary p-adic Haar det law" ]
theorem isometryAttemptRows_length : isometryAttemptRows.length = 3 := rfl
def isometryMissing : List String :=
  [ "canonical isometry tensor block -> product carrier",
    "log-volume transport under the B2 algebra equivalence" ]
theorem isometryMissing_length : isometryMissing.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1P2TensorProductIsometryActual
end
