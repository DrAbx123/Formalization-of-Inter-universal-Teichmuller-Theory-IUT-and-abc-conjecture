import tmp.sheaf.n8.closure.PaperToCurrentDonorsConstructed
import tmp.sheaf.n8.closure.C7NormalizedDivisors

/-!
# C7 paper q law

Paper q endpoint from the same bad moduli place:
  p0 = chosen bad finite place of Fmod (ClauseB.bad_nonempty)
  QPaper = log ||qParameter p0|| = log(exp(-order)) = -order.

Normalized C6 paper data:
  hNorm = c6NormalizedTheta.toReal
  rNorm = c6NormalizedRegionVolume.toReal
  A = rNorm, Z = hNorm.

Then hNorm - QPaper = Z - A iff QPaper = rNorm.  No arbitrary A/Z.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.PaperInitialThetaData
open LeanFormal.IUT.N8Closure.PaperToCurrentDonorsConstructed
open LeanFormal.IUT.N8Closure.C7NormalizedDivisors
open LeanFormal.IUT.N8Closure.PaperC6RegionConstructed2

namespace LeanFormal.IUT.N8Closure.C7PaperQLaw

noncomputable def paperBad {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    PaperBadPlaces S :=
  ⟨p0 S, p0_mem S⟩

/-- Paper q endpoint from the chosen bad moduli place. -/
noncomputable def QPaper {l : PrimeGeFive} (S : SourceInitialThetaData l) : Real :=
  Real.log (paperQParameter S (paperBad S))

/-- The paper q endpoint is exactly minus the ClauseB q order. -/
theorem QPaper_eq_neg_order {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    QPaper S = -((paperQCandidate S (paperBad S)).order : Real) := by
  unfold QPaper paperQParameter
  rw [Real.log_exp]

/-- Paper q endpoint is negative. -/
theorem QPaper_neg {l : PrimeGeFive} (S : SourceInitialThetaData l) :
    QPaper S < 0 := by
  rw [QPaper_eq_neg_order]
  have hpos : 0 < ((paperQCandidate S (paperBad S)).order : Real) := by
    exact_mod_cast (paperQCandidate S (paperBad S)).order_pos
  linarith

/-- Normalized paper law with A=rNorm, Z=hNorm. -/
def C7PaperQLawProp {l : PrimeGeFive} (S : SourceInitialThetaData l) : Prop :=
  hNorm S - QPaper S = Z S - A S

/-- The paper law is exactly QPaper = rNorm. -/
theorem c7PaperQLaw_iff_QPaper_eq_rNorm {l : PrimeGeFive}
    (S : SourceInitialThetaData l) :
    C7PaperQLawProp S ↔ QPaper S = rNorm S := by
  unfold C7PaperQLawProp Z A
  constructor <;> intro hh <;> linarith

/-- Exact remaining paper q identification target. -/
def MissingPaperQNormalization {l : PrimeGeFive}
    (S : SourceInitialThetaData l) : Prop := QPaper S = rNorm S

end LeanFormal.IUT.N8Closure.C7PaperQLaw
