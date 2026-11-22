import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Namespace probe for the Haar-uniqueness glue tool (task-64). -/

open MeasureTheory Measure

#check Measure.ext_of_integral_eq_on_compactlySupported
#check Measure.ext_of_integral_eq_on_compactlySupported_nnreal
#check Measure.addHaarScalarFactor
#check integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport
#check Measure.integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport
#check isAddLeftInvariant_eq_smul_of_innerRegular
