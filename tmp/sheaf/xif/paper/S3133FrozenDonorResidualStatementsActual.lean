import tmp.sheaf.xif.paper.S3133M1IndexIdentificationActual
import tmp.sheaf.xif.paper.S3133GaussianM2MissingActual
import tmp.sheaf.xif.paper.S3133M2bAttackActual

/-!
# Frozen-donor R1 residual statements (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: mainline/lattice FINAL-STATUS,
shehdd reopen checklist.

EXACT frozen-donor residual statements (class B/C per citation audit):
* M1 (class C source datum, IUT I Def 3.1(b),(e), V_mod_bijection/index side):
  S3133FrozenDonorIndexIdentification := C3.tensorIndex = Bad (nativePlaceSelection T)
  together with the place-compatibility
  S3133FrozenDonorPlaceCompatibility := forall b, placeTransport (nativeBadToFPlace T b)
  = (C3.tensorPlaces (e b) (C3.tensorTuple (e b))).val for the canonical index
  equivalence e induced by the identification;
* M2b (class B/C convention link, IUT III:10350; IUT I Def 3.1(b)/Ex 3.2(iv)):
  S3133FrozenDonorM2bResidual := S3133GaussianClauseBDescent T, with the exact
  Tate-q identification spec S3133M2bTateQIdentification and the proved reduction
  from the spec.
This file records these as the canonical named residual statements and proves
the reductions to the existing S3133M1Remaining / clause-B descent.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133FrozenDonorResidualStatementsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S3133S3131PlaceIndexComparisonActual
open LeanFormal.IUT.XiFPaper.S3133M1InjectionReductionActual
open LeanFormal.IUT.XiFPaper.S3133M1ConcretePrimeMatchActual
open LeanFormal.IUT.XiFPaper.S3133M1IndexIdentificationActual
open LeanFormal.IUT.XiFPaper.S3133GaussianM2MissingActual
open LeanFormal.IUT.XiFPaper.S3133M2bAttackActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Frozen-donor M1 index identification statement (class C). -/
abbrev S3133FrozenDonorIndexIdentification : Prop :=
  C3.tensorIndex = S3133ConcreteTensorIndex T

/-- Frozen-donor M1 place-compatibility statement (class C, transport side). -/
abbrev S3133FrozenDonorPlaceCompatibility
    (h : S3133M1IndexIdentification T C3)
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod) : Prop :=
  S3133M1PlaceCompatibility T C3 h placeTransport

/-- Frozen-donor M2b residual statement (class B/C convention link). -/
abbrev S3133FrozenDonorM2bResidual : Prop := S3133GaussianClauseBDescent T

/-- The frozen-donor R1 residual as an exact conjunction: index identification
+ place compatibility + clause-B Tate-q descent. -/
def S3133FrozenDonorR1Residual
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod) : Prop :=
  (∃ h : S3133M1IndexIdentification T C3,
      S3133M1PlaceCompatibility T C3 h placeTransport) ∧
    S3133GaussianClauseBDescent T

/-- The frozen-donor R1 residual reduces to the existing minimal residual
(M1Remaining) plus the clause-B descent. -/
theorem S3133FrozenDonorR1Residual_to_minimal
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod)
    (h : S3133FrozenDonorR1Residual T C3 placeTransport) :
    S3133M1Remaining T C3 placeTransport ∧ S3133GaussianClauseBDescent T := by
  obtain ⟨⟨hidx, hplace⟩, hm2b⟩ := h
  exact ⟨S3133M1Remaining_of_placeCompatibility T C3 hidx placeTransport hplace, hm2b⟩

/-- The exact Tate-q identification spec reduces to the frozen-donor M2b
residual. -/
theorem S3133FrozenDonorM2bResidual_of_tateQ
    (S : S3133M2bTateQIdentification T) :
    S3133GaussianClauseBDescent T :=
  S3133GaussianClauseBDescent_of_tateQIdentification T S

end LeanFormal.IUT.XiFPaper.S3133FrozenDonorResidualStatementsActual
