import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31ArithmeticCompatibilitySlots

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1342D9PlaceSectionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual

/-- D9 place/section-related actual item: the section compatibility slot for
the actual S1280 selection is proved canonically from the source place-selection
lemmas. -/
theorem s1342SectionCompatibility_actual (l : PrimeGeFive) :
    ArithmeticSectionCompatibility (S1280Selection l) :=
  arithmeticSectionCompatibility_canonical (S1280Selection l)

/-- D9 reduction compatibility for the actual S1280 reduction cards,
conditional on the actual bad-place q-parameter cards. -/
theorem s1342ReductionCompatibility_of_Q (l : PrimeGeFive)
    (Q : BadPlaceQParameterCards (S1280Selection l)) :
    ArithmeticReductionCompatibility (S1280Selection l)
      (S1280ReductionCards l) Q :=
  arithmeticReductionCompatibility_of_supply (S1280Selection l)
    (S1280ReductionCards l) Q

/-- Exact first field for the place/reduction-related D9 item: the actual
bad-place q-parameter cards. -/
abbrev S1342ReductionFirstField (l : PrimeGeFive) : Type :=
  BadPlaceQParameterCards (S1280Selection l)

end LeanFormal.IUT.XiFPaper.S1342D9PlaceSectionActual

end
