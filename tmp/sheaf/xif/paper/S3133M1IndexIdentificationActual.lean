import tmp.sheaf.xif.paper.S3133M1ConcretePrimeMatchActual
import tmp.sheaf.xif.paper.S3133M1InjectionReductionActual

/-!
# M1 index-identification reduction (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: mainline/lattice in-model R1
record, shehdd 3rd-reopen checklist.

On the CONCRETE donor (tensorIndex := Bad, refl equivalence) the index side of
M1 is the explicit identification C3.tensorIndex = Bad (nativePlaceSelection T)
(the V_mod_bijection/index side, IUT I Def 3.1(b),(e), class C source datum).
Given that identification, the canonical bad-index equivalence is Equiv.cast of
it, and M1's remaining content reduces to the PLACE-COMPATIBILITY of the
transport (the C3 tensor places at the canonical index).  This file proves the
sufficient direction: place-compatibility for the canonical index equivalence
gives S3133M1Remaining; combined with the previous file's prime match, the
concrete-donor M1 residual is exactly that place-compatibility field.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133M1IndexIdentificationActual

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

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Concrete-donor index identification: the C3 tensor index is the Bad index
set (the V_mod_bijection/index side of M1). -/
structure S3133M1IndexIdentification where
  index_eq : C3.tensorIndex = S3133ConcreteTensorIndex T

/-- The canonical bad-index equivalence induced by the index identification. -/
def S3133M1CanonicalIndexEquiv (h : S3133M1IndexIdentification T C3) :
    Bad (nativePlaceSelection T) ≃ C3.tensorIndex :=
  Equiv.cast h.index_eq.symm

/-- M1 place-compatibility for the canonical index equivalence. -/
def S3133M1PlaceCompatibility
    (h : S3133M1IndexIdentification T C3)
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod) : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    placeTransport (nativeBadToFPlace T b) =
      (C3.tensorPlaces (S3133M1CanonicalIndexEquiv T C3 h b)
        (C3.tensorTuple (S3133M1CanonicalIndexEquiv T C3 h b))).val

/-- Place-compatibility plus the index identification gives M1's remaining
residual exactly (the index side is discharged by the identification). -/
theorem S3133M1Remaining_of_placeCompatibility
    (h : S3133M1IndexIdentification T C3)
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod)
    (hplace : S3133M1PlaceCompatibility T C3 h placeTransport) :
    S3133M1Remaining T C3 placeTransport :=
  ⟨⟨S3133M1CanonicalIndexEquiv T C3 h, hplace⟩⟩

end LeanFormal.IUT.XiFPaper.S3133M1IndexIdentificationActual
