import tmp.sheaf.xif.paper.Mzk1Example36EtThCorrespondenceActual
import tmp.sheaf.xif.paper.Mzk1EtThRealizationRowsSummaryActual

/-!
# Mzk1Example36ConsumerChainActual — consumer theorems for the Example36<->EtTh
correspondence chain (real content: composed projections of proved assets)

Reuses proved assets Mzk1Example36EtThCorrespondenceActual (EXIT0/CITABLE) and
Mzk1EtThRealizationRowsSummaryActual (EXIT0). No new axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Example36ConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Example36EtThCorrespondenceActual
open LeanFormal.IUT.XiFPaper.Mzk1EtThRealizationRowsSummaryActual

/-- Consumer: the concrete analytic theta q-parameter is gaussianFiveThetaQ (inside (0,1)). -/
theorem consumer_example36_q (l : PrimeGeFive) :
    (example36EtThCorrespondence l).thetaCarrier.q = gaussianFiveThetaQ ∧
      (0 < (example36EtThCorrespondence l).thetaCarrier.q ∧
        (example36EtThCorrespondence l).thetaCarrier.q < 1) := by
  refine ⟨etthExample36_concrete_q, ?_⟩
  exact ⟨(example36EtThCorrespondence l).thetaCarrier.q_pos,
    (example36EtThCorrespondence l).thetaCarrier.q_lt_one⟩

/-- Consumer: analytic q-expansion agrees with the Gaussian kernel value. -/
theorem consumer_example36_kernel (t : AnalyticThetaCarrier) (n : ℤ) :
    analyticThetaQExpansion t n = realThetaValue t.q n :=
  (etthExample36_qExpansion_eq_kernel t n)

/-- Consumer: the correspondence bundle is nonempty for every l >= 5. -/
theorem consumer_example36_nonempty (l : PrimeGeFive) :
    Nonempty (Example36EtThCorrespondence l) :=
  example36EtThCorrespondence_nonempty l

/-- Consumer: the EtTh realization row record has its seven rows (from ETR). -/
theorem consumer_example36_row_count : etthRealizationRowStatus.length = 7 :=
  etthRealizationRowStatus_length

/-- Consumer rows: (consumer theorem, consumed asset, status). -/
def example36ConsumerRows : List (String × String × String) :=
  [ ("concrete q = gaussianFiveThetaQ in (0,1)", "consumer_example36_q", "PROVED (composed projections)"),
    ("q-expansion = Gaussian kernel", "consumer_example36_kernel", "PROVED (X1)"),
    ("correspondence nonempty", "consumer_example36_nonempty", "PROVED (X1)"),
    ("row count", "consumer_example36_row_count", "PROVED (ETR)"),
    ("class-B rows 5-7", "not asserted here", "NAMED") ]

theorem example36ConsumerRows_length : example36ConsumerRows.length = 5 := rfl

#check consumer_example36_q
#check consumer_example36_kernel
#check consumer_example36_nonempty
#check consumer_example36_row_count
#check example36ConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Example36ConsumerChainActual
end
