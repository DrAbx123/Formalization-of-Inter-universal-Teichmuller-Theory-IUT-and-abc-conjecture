import tmp.sheaf.xif.paper.S356RootStackActionGroupoidActual

-- S392: non-degenerate monoid/section carrier candidate built from the S356
-- action groupoid: functions on roots with pointwise multiplication and a
-- delta (coordinate) injection of roots.  No quotient.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S392RootStackSectionMonoidActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S330QVFamilyRootCardActual
open LeanFormal.IUT.XiFPaper.S355OrbifoldRootStackCandidateActual
open LeanFormal.IUT.XiFPaper.S356RootStackActionGroupoidActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

abbrev SectionCarrier : Type := RootObj T b → Multiplicative ℤ

noncomputable def rootDelta (r : RootObj T b) : SectionCarrier T b := by
  classical
  exact fun s => if s = r then Multiplicative.ofAdd (1 : ℤ) else 1

theorem ofAdd_one_ne_one :
    Multiplicative.ofAdd (1 : ℤ) ≠ (1 : Multiplicative ℤ) := by
  intro h
  have h' := congrArg Multiplicative.toAdd h
  simp at h'

theorem rootDelta_injective : Function.Injective (rootDelta T b) := by
  classical
  intro r s h
  by_contra hne
  have hr : rootDelta T b r r = Multiplicative.ofAdd (1 : ℤ) := by
    simp [rootDelta]
  have hs : rootDelta T b s r = (1 : Multiplicative ℤ) := by
    simp [rootDelta, hne]
  have hval := congrFun h r
  rw [hr, hs] at hval
  exact ofAdd_one_ne_one (by simpa using hval)

noncomputable def rootSectionCandidate : SectionCarrier T b :=
  rootDelta T b (rootObj T b)

noncomputable def qSectionCandidate : SectionCarrier T b :=
  rootSectionCandidate T b ^ (2 * l.value)

theorem rootSectionCandidate_pow :
    rootSectionCandidate T b ^ (2 * l.value) = qSectionCandidate T b := rfl

noncomputable def sectionCarrierToCompletion (_ : SectionCarrier T b) :
    Completion (qVFamilyPlace T b) :=
  (qVFamily T b).q

theorem qSectionCandidate_toCompletion :
    sectionCarrierToCompletion T b (qSectionCandidate T b) = (qVFamily T b).q := rfl

noncomputable def sectionMu2lAction
    (ζ : rootsOfUnity (n (l := l)) (AC T b))
    (f : SectionCarrier T b) : SectionCarrier T b :=
  fun s => f (ζ⁻¹ • s)

noncomputable def rootStackMonoidSectionCarrier :
    RootStackMonoidSectionCarrier.{0} T b where
  carrier := SectionCarrier T b
  monoid := inferInstance
  objToCarrier := rootDelta T b
  objToCarrier_injective := rootDelta_injective T b
  qSection := qSectionCandidate T b
  rootSection := rootSectionCandidate T b
  qSection_toCompletion := sectionCarrierToCompletion T b
  qSection_toCompletion_q := qSectionCandidate_toCompletion T b
  rootSection_pow := rootSectionCandidate_pow T b
  mu2lAction := sectionMu2lAction T b

#check SectionCarrier
#check rootDelta
#check rootDelta_injective
#check rootStackMonoidSectionCarrier

end LeanFormal.IUT.XiFPaper.S392RootStackSectionMonoidActual

end