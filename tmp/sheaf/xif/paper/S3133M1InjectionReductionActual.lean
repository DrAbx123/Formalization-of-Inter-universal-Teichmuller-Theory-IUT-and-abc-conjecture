import tmp.sheaf.xif.paper.S3133BadToAllPlaceIndexInjectionActual
import tmp.sheaf.xif.paper.S3133S3131PlaceIndexComparisonActual

/-!
# M1 residual reduction: the bad->all-place injection is constructible from the
# two index bijections (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: mainline task-20 M1, lattice
S3137 R1, hull bad/all-place compatibility.

Source: IUT III, Theorem 3.11, pp. 160-162; IUT IV, Theorem 1.10 proof,
pp. 26-27; IUT I, Definition 3.1, (b), (e) (source place selection/provenance).

Residual reduction.  The bad->all-place index INJECTION is not itself missing:
given the bad-only tensor index equivalence e : Bad (nativePlaceSelection T) ≃
C3.tensorIndex and an all-place index equivalence indexEquiv : V ≃
C3.tensorIndex, the map badToV := indexEquiv.symm ∘ e is injective and satisfies
the index agreement by construction.  Hence the exact M1 missing content is the
pair (e, place-compatible all-place transport): the genuine source
placeToMod/provenance data that OriginalInput does not expose
(SourceInitialThetaData place-to-moduli data has no projection in the frozen
OriginalInput contract; no contract change is made).

No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133M1InjectionReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S3133S3131PlaceIndexComparisonActual
open LeanFormal.IUT.XiFPaper.S3133BadToAllPlaceIndexInjectionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The bad-to-all-place injection is CONSTRUCTIBLE from the two index
bijections: badToV := indexEquiv.symm ∘ e.  It is injective and its index
agreement is definitional. -/
noncomputable def S3133BadToAllPlaceIndexInjection_of_bijections
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (indexEquiv : V ≃ C3.tensorIndex) :
    S3133BadToAllPlaceIndexInjection T C3 e indexEquiv where
  badToV := fun b => indexEquiv.symm (e b)
  badToV_injective := fun b b' h =>
    e.injective (indexEquiv.symm.injective h)
  index_agree := fun b => by
    show indexEquiv (indexEquiv.symm (e b)) = e b
    exact indexEquiv.apply_symm_apply (e b)

/-- Consequence: the injection residual Prop is constructible once the bad-only
index equivalence e is supplied (for any all-place index equivalence). -/
theorem S3133BadToAllPlaceIndexInjection_of_indexEquivalence
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (indexEquiv : V ≃ C3.tensorIndex) :
    S3133BadToAllPlaceIndexInjectionData T C3 e indexEquiv :=
  ⟨S3133BadToAllPlaceIndexInjection_of_bijections T C3 e indexEquiv⟩

/-- Exact M1 residual, SHRUNK: the remaining missing content is the bad-only
tensor index equivalence e together with a place-compatible all-place transport.
The injection/index part is proved constructible above; the genuine source
missing is the place provenance (placeToMod) that the frozen OriginalInput
contract does not expose. -/
def S3133M1Remaining
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod) : Prop :=
  Nonempty
    ({ e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex //
      ∀ b : Bad (nativePlaceSelection T),
        placeTransport (nativeBadToFPlace T b) =
          (C3.tensorPlaces (e b) (C3.tensorTuple (e b))).val })

/-- If the shrunk M1 residual is supplied, the place match and (with prime
compatibility of the transport) the actual prime-level match follow. -/
theorem S3131BadTensorPrimeMatch_of_M1Remaining
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod)
    (hprimeTransport : ∀ b : Bad (nativePlaceSelection T),
      (completionRationalPrime (placeTransport (nativeBadToFPlace T b))).val =
        (completionRationalPrime (nativeBadToFPlace T b)).val)
    (h : S3133M1Remaining T C3 placeTransport) :
    S3131BadTensorPrimeMatch T C3 := by
  obtain ⟨e, hplace⟩ := h
  exact S3131BadTensorPrimeMatch_of_placeMatch T C3 e placeTransport
    hplace hprimeTransport

end LeanFormal.IUT.XiFPaper.S3133M1InjectionReductionActual
