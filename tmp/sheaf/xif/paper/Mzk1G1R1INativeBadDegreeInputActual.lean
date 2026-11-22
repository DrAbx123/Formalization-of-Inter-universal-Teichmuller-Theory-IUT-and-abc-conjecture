/- R1-I native bad weight: explicit relative-degree input (NO donor in tree).

Exact missing lemma (reported, not asserted):
  localCompletionDegree T.arithmetic (nativeBadToKPlace T b) = 2 * l.value
Equivalently Module.finrank (Fmod_v) (K_w) = 2*l for the actual 2l-th Kummer root
completion. Audit donor Mzk1G1F2ThetaELeTwoLAuditActual states this degree input is
missing (ThetaRelativeDegreeInput); Mzk1P1FinitePlaceFvActual only gives
localCompletionDegree = relativeCompletionDegree under FINITE/AGREE, not the value.
-/
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.Mzk1G1F2ThetaELeTwoLAuditActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R1INativeBadDegreeInputActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Explicit R1-I input: the relative completion degree at the native bad K-place is 2l. -/
def NativeBadRelativeDegreeInput : Prop :=
  localCompletionDegree T.arithmetic (nativeBadToKPlace T b) = 2 * l.value

/-- hW reduction from the explicit relative-degree input: the normalized local weight is
(2l)⁻¹. -/
theorem nativeBadLocalWeight_eq_inv_two_l_of_input
    (H : NativeBadRelativeDegreeInput (T := T) (b := b)) :
    nativeBadLocalWeight T b = ((2 * (l.value : ℝ)) : ℝ)⁻¹ := by
  rw [nativeBadLocalWeight_eq_inv, H]
  push_cast
  ring

#print axioms nativeBadLocalWeight_eq_inv_two_l_of_input
end LeanFormal.IUT.XiFPaper.Mzk1G1R1INativeBadDegreeInputActual
