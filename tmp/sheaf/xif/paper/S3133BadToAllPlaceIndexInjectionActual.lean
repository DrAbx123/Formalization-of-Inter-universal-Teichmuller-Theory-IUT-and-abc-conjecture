import tmp.sheaf.xif.paper.S3133S3131PlaceIndexComparisonActual

/-!
# Bad-to-all-place index injection (component, not a paper object)

COMPONENT, not a paper object.  Named future consumers: hull's S3132 all-place /
bad-place compatibility theorem; the S3130QCLeHCData fixed-C package; lattice's
qTheta comparison (S3137*).

Source: IUT III, Theorem 3.11, pp. 160-162 (the multiradial representation's
prime-strip links); IUT IV, Theorem 1.10 proof, pp. 26-27 (the passage from the
single Stage-2/regional data to the global bad family).

Context (hull, S3132PrimeStripC3AllPlaceComparisonComponent, EXIT=0): the
all-place record PrimeStripC3PlaceComparison trivializes (any V ≃ C3.tensorIndex
yields it, and stripPlace is forced by C3.tensorPlaces).  Therefore a
bad-place/all-place compatibility is not derivable from OriginalInput alone and
must be a named exact residual.  This file provides the structure hull asked for:

* S3133BadToAllPlaceIndexInjection T C3 e indexEquiv: a bad-to-V map, its
  injectivity, and the index agreement indexEquiv (badToV b) = e b;
* the induced tensorPlace agreement (rewrite along the index agreement);
* S3131BadTensorPrimeMatch from S3131BadTensorPlaceMatch plus this injection
  (composition of the already proved placeMatch->primeMatch direction), with the
  prime-compatible transport hypothesis;
* S3133BadToAllPlaceIndexInjectionData: the exact residual Prop (not inhabited),
  recording that the injection/index agreement is NOT derivable from
  OriginalInput (placeToMod provenance is not exposed there).

No injection is assumed; no sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133BadToAllPlaceIndexInjectionActual

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

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Exact named residual data hull consumes: a bad-to-all-place index injection
compatible with the bad-only tensor index equivalence. -/
structure S3133BadToAllPlaceIndexInjection
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (indexEquiv : V ≃ C3.tensorIndex) where
  /-- the bad index mapped into the all-place index -/
  badToV : Bad (nativePlaceSelection T) → V
  /-- the bad index injection is injective -/
  badToV_injective : Function.Injective badToV
  /-- the two index identifications agree on the bad family -/
  index_agree : ∀ b : Bad (nativePlaceSelection T), indexEquiv (badToV b) = e b

/-- The tensorPlace data agrees on the bad family: the bad-only tensorPlace at
e b equals the all-place tensorPlace at indexEquiv (badToV b). -/
theorem S3133BadToAllPlaceIndexInjection_tensorPlaces_agree
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (indexEquiv : V ≃ C3.tensorIndex)
    (h : S3133BadToAllPlaceIndexInjection T C3 e indexEquiv)
    (b : Bad (nativePlaceSelection T)) :
    C3.tensorPlaces (e b) (C3.tensorTuple (e b)) =
      C3.tensorPlaces (indexEquiv (h.badToV b))
        (C3.tensorTuple (indexEquiv (h.badToV b))) := by
  rw [← h.index_agree b]

/-- The composition requested by hull: the bad-to-all-place injection plus the
bad-only tensorPlace match yields the actual prime-level match (via the already
proved placeMatch->primeMatch direction, with a prime-compatible transport). -/
theorem S3131BadTensorPrimeMatch_of_placeMatch_and_injection
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (placeTransport : NumberField.FinitePlace T.arithmetic.F ≃
      NumberField.FinitePlace I.initial.arithmetic.Fmod)
    (hPM : S3131BadTensorPlaceMatch T C3 e placeTransport)
    (indexEquiv : V ≃ C3.tensorIndex)
    (hInj : S3133BadToAllPlaceIndexInjection T C3 e indexEquiv)
    (hprimeTransport : ∀ b : Bad (nativePlaceSelection T),
      (completionRationalPrime (placeTransport (nativeBadToFPlace T b))).val =
        (completionRationalPrime (nativeBadToFPlace T b)).val) :
    S3131BadTensorPrimeMatch T C3 :=
  S3131BadTensorPrimeMatch_of_placeMatch T C3 e placeTransport hPM hprimeTransport

/-- The exact residual Prop: the bad-to-all-place index injection data.  It is
NOT derivable from OriginalInput (which does not expose the placeToMod
provenance V -> Fmod; the all-place record is trivialized, cf. hull's S3132
component).  Not inhabited. -/
def S3133BadToAllPlaceIndexInjectionData
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (indexEquiv : V ≃ C3.tensorIndex) : Prop :=
  Nonempty (S3133BadToAllPlaceIndexInjection T C3 e indexEquiv)

end LeanFormal.IUT.XiFPaper.S3133BadToAllPlaceIndexInjectionActual
