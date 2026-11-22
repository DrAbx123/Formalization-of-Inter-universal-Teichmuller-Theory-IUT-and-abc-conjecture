import tmp.sheaf.xif.paper.S3133S3131GaussianModelMapMinimalActual
import tmp.sheaf.xif.paper.S3133S3131GaussianModelComponentsActual

/-!
# M2 base-q reduction: bad places above 5 => norm 1/5 under the base-q identification

COMPONENT, not a paper object.  Named consumers: task-45 M2 residual, lattice R1,
mainline M2.

Source: IUT I, Example 3.2, (iv) (q_v parameters); IUT I, Definition 3.1, (b),
(c) (bad place selection, residue-characteristic condition p_v = 5); IUT III,
Definition 3.8, (i), p. 112-113 (q-pilot data).

What is PROVED here:
* for any native T whose arithmetic is the concrete Gaussian arithmetic
  (S3133GaussianModelArithmeticMatch T), the two fields F and Fmod coincide
  (both GaussianField), so there is NO field-degree descent obstruction
  F -> Fmod in the Gaussian model;
* M2 shrunk (S3133GaussianQParameterMatchAtBase) follows from an explicit
  base-q identification: at every bad place above 5, some FinitePlaceQCandidate
  at the actual lifted F-place has norm 1/5 and equals the clause-B q
  (this is exactly the paper Tate q identification, IUT I Definition 3.1(b),
  Example 3.2(iv), the D4 boundary).

What remains exact Missing: an ACTUAL Gaussian base-q donor whose norm is 1/5.
The tree's concrete Gaussian q candidate S2684GaussianFiveQCandidate (norm 1/5
at concreteGaussianFivePlace) is not compiled (no olean), and the compiled S1280
data only gives the REAL proxy qParameter = (1/5)^order of the assembled
Definition 3.1 reduction clause.  Hence M2's value part is the genuine source
missing "Tate q identification" (D4) plus the base-q donor construction; no
contract change and no fake candidate are used here.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133M2BaseQReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelComponentsActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelMapMinimalActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- For the Gaussian model arithmetic, the fields F and Fmod coincide: there is
no field-degree descent obstruction F -> Fmod in the Gaussian model. -/
theorem S3133GaussianArithmetic_F_eq_Fmod
    (h : S3133GaussianModelArithmeticMatch T) :
    T.arithmetic.F = T.arithmetic.Fmod := by
  unfold S3133GaussianModelArithmeticMatch at h
  rw [h]
  rfl

/-- M2 shrunk exact Prop restated for immediate consumption. -/
theorem S3133GaussianQParameterMatchAtBase_defining :
    S3133GaussianQParameterMatchAtBase T ↔
      ∀ b : Bad (nativePlaceSelection T),
        (completionRationalPrime (nativeBadToFPlace T b)).val = 5 →
          ‖(qVFamily T b).q‖ = ((5 : Real)⁻¹) :=
  Iff.rfl

/-- M2 reduction: the Gaussian value at bad places above 5 follows from an
explicit base-q identification at the actual lifted F-place: a candidate with
clock norm 1/5 which is literally the clause-B q.  This isolates the remaining
missing datum to the Tate q identification (D4) / base-q donor. -/
theorem S3133GaussianQParameterMatchAtBase_of_baseQIdentification
    (h : ∀ b : Bad (nativePlaceSelection T),
      (completionRationalPrime (nativeBadToFPlace T b)).val = 5 →
        ∃ x : FinitePlaceQCandidate ((nativeBadLift T).lift b),
          ‖x.q‖ = ((5 : Real)⁻¹) ∧ x.q = (qVFamily T b).q) :
    S3133GaussianQParameterMatchAtBase T := by
  intro b h5
  obtain ⟨x, hxnorm, hxq⟩ := h b h5
  rw [← hxq]
  exact hxnorm

/-- Exact missing datum for M2's base-q value part: an actual Gaussian base-q
donor (a FinitePlaceQCandidate at the Fmod place above 5 with norm 1/5) together
with its descent identification to the clause-B q.  The structure is not
inhabited here. -/
structure S3133GaussianBaseQDescentMissing
    (T : SourceNativeInitialThetaData.{0} l) where
  /-- the base Fmod place above 5 -/
  basePlace : NumberField.FinitePlace T.arithmetic.Fmod
  basePlace_above_five : (completionRationalPrime basePlace).val = 5
  /-- the missing base q candidate -/
  q : FinitePlaceQCandidate basePlace
  q_norm : ‖q.q‖ = ((5 : Real)⁻¹)
  /-- exact missing: identification of this base q with the clause-B q at the
  lifted F-place (paper Tate q identification, D4 boundary) -/
  clauseB_descent : Prop

/-- The existence of the missing Gaussian base-q/descent datum. -/
def S3133GaussianBaseQDescentMissingData : Prop :=
  Nonempty (S3133GaussianBaseQDescentMissing T)

end LeanFormal.IUT.XiFPaper.S3133M2BaseQReductionActual
