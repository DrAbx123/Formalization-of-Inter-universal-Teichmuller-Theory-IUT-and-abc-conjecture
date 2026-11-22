import tmp.sheaf.xif.paper.S2020DicksonActionActual
import tmp.sheaf.xif.paper.S2020DicksonTransvectionActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual
import tmp.sheaf.xif.paper.S2009DicksonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2364D5GroupRouteActual

open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open Matrix

/-- Cycle type (10,2) implies 10 divides the subgroup order, hence 5 divides
it. -/
theorem S2364FiveDvdOfCycleType102
    (H : Subgroup GL2) (h102 : HasCycleType102 H) :
    5 ∣ Nat.card H := by
  obtain ⟨h, hh, hc⟩ := h102
  exact dvd_trans (by norm_num : 5 ∣ 10)
    (ten_dvd_natCard_of_mem_cycleType102 hh hc)

/-- Pair transitivity plus 5 dividing the order gives the SL2 image
containment. -/
theorem S2364SL2Image_le_of_fiveDvd_and_transitive
    (H : Subgroup GL2) (htrans : PairTransitive H)
    (h5 : 5 ∣ Nat.card H) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K5)) ≤ H := by
  have hle := sl_le_of_five_dvd H htrans h5
  rwa [closure_trv_eq_map, closure_sl_eq_top] at hle

/-- Cycle type and pair transitivity give the SL2 image containment. -/
theorem S2364SL2Image_le_of_cycleType_and_transitive
    (H : Subgroup GL2) (h102 : HasCycleType102 H)
    (htrans : PairTransitive H) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K5)) ≤ H :=
  S2364SL2Image_le_of_fiveDvd_and_transitive H htrans
    (S2364FiveDvdOfCycleType102 H h102)

/-- At the actual basis, the two hypotheses give the S1725 image tail. -/
theorem S2364RangeImageTail_of_hypotheses
    (b : S1725TorsionBasis S1987Five)
    (h102 : HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range)
    (htrans : PairTransitive
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range) :
    S1725ImageTail S1987Five b :=
  S2364SL2Image_le_of_cycleType_and_transitive _ h102 htrans

/-- Conditional D5 target from the two actual range hypotheses. -/
theorem S2364D5LargeImageFive_of_hypotheses
    (b : S1725TorsionBasis S1987Five)
    (h102 : HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range)
    (htrans : PairTransitive
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range) :
    S1987D5LargeImageFive :=
  (S1987D5LargeImageFive_iff_tail b).mpr
    (S2364RangeImageTail_of_hypotheses b h102 htrans)

/-- Exact first missing: the two actual range hypotheses at the selected
basis. -/
def S2364ExactFirstMissing : Prop :=
  HasCycleType102
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range ∧
  PairTransitive
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range

/-- Conditional D5 target from the exact missing conjunction. -/
theorem S2364D5LargeImageFive_of_exactFirstMissing
    (h : S2364ExactFirstMissing) : S1987D5LargeImageFive :=
  S2364D5LargeImageFive_of_hypotheses S1982Basis h.1 h.2

end LeanFormal.IUT.XiFPaper.S2364D5GroupRouteActual

end
