import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P5SourceColumnsActual
/-- Source-column donors and the exact missing actual finite source image.
No inhabitant is asserted. -/
def sourceColumnDonors : List String :=
  [ "SourceColumnCarrierIdentification.coreColumnRealization",
    "SourceColumnCarrierIdentification.columnRealization_all_package",
    "Mzk1P5PacketTableActual.gamma_subset_hull" ]
theorem sourceColumnDonors_length : sourceColumnDonors.length = 3 := rfl
/-- Exact missing source-column object: a finite set of actual source vectors
with tensor-factor coordinates and valuations. -/
structure MissingSourceColumns where
  sourceVectors : Type
  tensorFactorCoordinate : sourceVectors → Type
  valuation : sourceVectors → Real
#check MissingSourceColumns
end LeanFormal.IUT.XiFPaper.Mzk1P5SourceColumnsActual
end