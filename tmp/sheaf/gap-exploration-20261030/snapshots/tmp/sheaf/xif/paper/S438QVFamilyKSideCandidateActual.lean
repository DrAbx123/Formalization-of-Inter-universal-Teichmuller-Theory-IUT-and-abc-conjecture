import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.S342QVFamilyRootImpossibleActual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameterRamification
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces

-- S438: actual K-side qVFamily candidate via completionMap along A.F -> A.K;
-- no arbitrary badPlaceQCandidate, no root fabricated.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S342QVFamilyRootImpossibleActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- A chosen K-place above the actual F-place of qVFamily.
noncomputable def qVFamilyKLift (b : Bad (nativePlaceSelection T)) :
    NumberField.FinitePlace T.arithmetic.K :=
  Classical.choose (NumberFieldFinitePlace.comap_surjective
    (k := T.arithmetic.F) (K := T.arithmetic.K) ((nativeBadLift T).lift b))

theorem qVFamilyKLift_comap :
    NumberFieldFinitePlace.comap (k := T.arithmetic.F) (qVFamilyKLift T b) =
      (nativeBadLift T).lift b :=
  Classical.choose_spec (NumberFieldFinitePlace.comap_surjective
    (k := T.arithmetic.F) (K := T.arithmetic.K) ((nativeBadLift T).lift b))

-- qVFamily transported to the chosen K-place (cast along the comap equality).
noncomputable def qVFamilyKParameter :
    FinitePlaceQCandidate
      (NumberFieldFinitePlace.comap (k := T.arithmetic.F) (qVFamilyKLift T b)) :=
  (qVFamilyKLift_comap T b).symm ▸ qVFamily T b

-- Actual K-side q candidate: completionMap of the F-side qVFamily.
noncomputable def qVFamilyK :
    FinitePlaceQCandidate (qVFamilyKLift T b) :=
  FinitePlaceQCandidate.map (k := T.arithmetic.F) (qVFamilyKLift T b)
    (qVFamilyKParameter T b)

theorem order_cast {p q : NumberField.FinitePlace T.arithmetic.F}
    (h : p = q) (x : FinitePlaceQCandidate p) :
    (h ▸ x).order = x.order := by
  cases h
  rfl

-- Exact order law: order at K-place = ramification index e times F-order.
theorem qVFamilyK_order_comap :
    (qVFamilyK T b).order =
      (NumberFieldFinitePlace.comap (k := T.arithmetic.F) (qVFamilyKLift T b)).maximalIdeal.asIdeal.ramificationIdx'
        (qVFamilyKLift T b).maximalIdeal.asIdeal *
        (qVFamily T b).order := by
  unfold qVFamilyK
  have hcast : (qVFamilyKParameter T b).order = (qVFamily T b).order := by
    unfold qVFamilyKParameter
    exact order_cast T (qVFamilyKLift_comap T b).symm (qVFamily T b)
  have h := FinitePlaceQCandidate.order_map (k := T.arithmetic.F)
    (place := qVFamilyKLift T b) (parameter := qVFamilyKParameter T b)
  simpa [hcast] using h

theorem qVFamilyK_ramificationIdx_eq :
    (NumberFieldFinitePlace.comap (k := T.arithmetic.F) (qVFamilyKLift T b)).maximalIdeal.asIdeal.ramificationIdx'
        (qVFamilyKLift T b).maximalIdeal.asIdeal =
      ((nativeBadLift T).lift b).maximalIdeal.asIdeal.ramificationIdx'
        (qVFamilyKLift T b).maximalIdeal.asIdeal := by
  rw [qVFamilyKLift_comap]

theorem qVFamilyK_order :
    (qVFamilyK T b).order =
      ((nativeBadLift T).lift b).maximalIdeal.asIdeal.ramificationIdx'
        (qVFamilyKLift T b).maximalIdeal.asIdeal *
        (qVFamily T b).order := by
  rw [qVFamilyK_order_comap T b, qVFamilyK_ramificationIdx_eq T b]
-- The F-side order remains coprime to l (paper Definition 3.1(c)).
theorem qVFamilyK_order_factor_coprime_source :
    Nat.Coprime (qVFamily T b).order l.value :=
  qVFamily_order_coprime T b

-- Exact missing: a 2l-th root in the K-completion; no construction/fake.
structure KSideTwoLRootData where
  root : Completion (qVFamilyKLift T b)
  root_pow : root ^ (2 * l.value) = (qVFamilyK T b).q
  class_well_defined : Prop

def KSideTwoLRootDataRequired : Prop :=
  Nonempty (KSideTwoLRootData T b)

#check qVFamilyKLift
#check qVFamilyKLift_comap
#check qVFamilyKParameter
#check qVFamilyK
#check qVFamilyK_order
#check KSideTwoLRootData

end LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual

end