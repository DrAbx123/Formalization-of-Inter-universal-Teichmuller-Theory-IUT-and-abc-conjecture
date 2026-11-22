import tmp.sheaf.xif.paper.S21dSourceTheaterCorrectionActual
import tmp.sheaf.n8.closure.C10BridgeProof

/-! # S21e: actual field comparison from a C10 native donor

A C10 NativeOriginalInputDonors D supplies the actual arithmetic equality

  D.initial.arithmetic = X.S.arithmetic.

Hence the source contract I = nativeOriginalInputOfDonors X D has
I.initial.arithmetic = X.S.arithmetic.  This gives an actual field embedding
from I.Fmod to X.S.F (the base field embedding), and the exact donor-built
field comparison.  The reverse map X.S.F -> I.Fmod and the F-place/Fmod place
map are recorded as the exact remaining orientation gap: the source tower is
Fmod -> F, not F -> Fmod.

No fake map/sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S21eSourceTheaterFieldComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S21dSourceTheaterCorrectionActual

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable (D : NativeOriginalInputDonors (X := X))

/-- The donor-built source contract. -/
abbrev comparedI : OriginalInput l (NativePlaces X.S) :=
  nativeOriginalInputOfDonors (X := X) D

/-- Actual arithmetic equality supplied by the C10 donor. -/
theorem compared_arithmetic_eq :
    (comparedI (X := X) D).initial.arithmetic = X.S.arithmetic :=
  D.initial_arithmetic

/-- Actual Fmod equality supplied by the donor. -/
theorem compared_fmod_eq :
    (comparedI (X := X) D).initial.arithmetic.Fmod = X.S.arithmetic.Fmod :=
  congrArg (fun A : InitialThetaArithmeticData l => A.Fmod)
    (compared_arithmetic_eq (X := X) D)

/-- Actual base-field comparison function I.Fmod -> X.S.F, obtained from the
donor arithmetic equality and the source algebra embedding Fmod -> F. -/
noncomputable def comparedFieldEmbedding :
    (comparedI (X := X) D).initial.arithmetic.Fmod → X.S.arithmetic.F :=
  fun x =>
    algebraMap X.S.arithmetic.Fmod X.S.arithmetic.F
      ((compared_fmod_eq (X := X) D).symm ▸ x)

/-- The actual donor comparison data: arithmetic/Fmod equality and the actual
base-field comparison function. -/
structure DonorFieldComparisonData where
  arithmetic_eq : (comparedI (X := X) D).initial.arithmetic = X.S.arithmetic
  fmod_eq : (comparedI (X := X) D).initial.arithmetic.Fmod =
    X.S.arithmetic.Fmod
  fieldEmbedding : (comparedI (X := X) D).initial.arithmetic.Fmod → X.S.arithmetic.F
  fieldEmbedding_eq : fieldEmbedding = comparedFieldEmbedding (X := X) D

/-- The actual donor field comparison data. -/
noncomputable def donorFieldComparisonData :
    DonorFieldComparisonData (X := X) D where
  arithmetic_eq := compared_arithmetic_eq (X := X) D
  fmod_eq := compared_fmod_eq (X := X) D
  fieldEmbedding := comparedFieldEmbedding (X := X) D
  fieldEmbedding_eq := rfl

/-- Exact orientation gap: the S21d field comparison requires a map
X.S.arithmetic.F -> I.Fmod, but the source supplies only Fmod -> F. -/
def SourceTheaterReverseFieldMapGap : Prop :=
  Nonempty (X.S.arithmetic.F →+* (comparedI (X := X) D).initial.arithmetic.Fmod)

end LeanFormal.IUT.XiFPaper.S21eSourceTheaterFieldComparisonActual

end
