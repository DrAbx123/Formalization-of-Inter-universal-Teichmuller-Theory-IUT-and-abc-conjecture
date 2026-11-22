import tmp.sheaf.xif.paper.Mzk1AbsTopIII05RefinedConcreteActual

/-!
# Mzk1RefinedConcreteConsumerActual — consumer theorems for the concrete D1-D4
instantiations (Mzk1AbsTopIII05RefinedConcreteActual, EXIT0). Composed projections only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1RefinedConcreteConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1AbsTopIII05RefinedConcreteActual
open LeanFormal.IUT.XiFPaper

/-- Consumer: the calibration datum has concrete refined deep inputs (f,e,m arbitrary). -/
theorem consumer_calibration_refined (f e m : ℕ) :
    Nonempty (RefinedDeepInputs sourceLogShellCalibrationDatum.K sourceLogShellCalibrationDatum.K) :=
  refinedDeepInputsConcrete_calibration f e m

/-- Consumer: the concrete oriented-graph data's combinatorial data holds. -/
theorem consumer_D4_combinatorial : concreteD4.combinatorialData :=
  concreteD4_combinatorialData

/-- Consumer: the refined-concrete row record has five rows. -/
theorem consumer_rows_length : refinedConcreteRows.length = 5 :=
  refinedConcreteRows_length

/-- Consumer: concrete D1 for any datum (f,e,m) -/
theorem consumer_concreteD1 (D : SourceLogShellDatum) (f e m : ℕ) :
    Prop58iLocalFieldReconstruction D.K :=
  concreteD1 D f e m

#check consumer_calibration_refined
#check consumer_D4_combinatorial
#check consumer_rows_length
#check consumer_concreteD1

end LeanFormal.IUT.XiFPaper.Mzk1RefinedConcreteConsumerActual
end
