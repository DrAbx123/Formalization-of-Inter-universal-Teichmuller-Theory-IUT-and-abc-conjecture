import tmp.sheaf.xif.paper.Mzk1G1FermatCoverActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCurveProjActual
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveProjActual
/-- Projective base point is in the Fermat cover for positive exponent. -/
theorem fermatCover_base_mem (n : Nat) (hn : 0 < n) :
    projFermatBase ∈ projFermatCurve n :=
  projFermatBase_mem hn
/-- Assembly: cover data and projective base point. -/
theorem fermatCover_assembly (n : Nat) (hn : 0 < n) :
    (fermatCoverData ℚ hn).basePoint = fermatBasePoint ℚ n hn ∧
      projFermatBase ∈ projFermatCurve n :=
  ⟨rfl, projFermatBase_mem hn⟩
#print axioms fermatCover_assembly
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverAssemblyActual
end