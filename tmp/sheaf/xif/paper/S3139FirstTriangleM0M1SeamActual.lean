/-!
# S3139: cross-stream M0/M1 seam record (first-triangle route residual)

Data-only record of the cross-stream residual names consumed by the
first-triangle route composition (@S3139FirstTriangleRouteCompositionActual@).

* M0/R1 same-C identification F ~ F_mod: owned by mainline R1 (same-C
  cross-carrier model identification; task-20/29/34/45/51 stream).
* M1/R1 place selection: owned by qpilot; exact names
  S3133M1ContractSeparatedMissing (S3133M1ContractObstructionActual) and
  S3133M1Remaining (S3133M1InjectionReductionActual), with the proved
  equivalence S3133M1ContractSeparatedMissing_iff_M1Remaining.  Shape:
  Nonempty { e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex //
    ∀ b, placeTransport (nativeBadToFPlace T b) = (C3.tensorPlaces (e b)
      (C3.tensorTuple (e b))).val }.
* Contract-separated capsule-label link: Capsule j.val <-> Bad/V (not in the
  frozen OriginalInput; extra data field of the fiber assignment).

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.FirstTriangleM0M1SeamActual

/-- The cross-stream seam of the first-triangle route residual. -/
structure SourceM0M1Seam where
  /-- M0/R1: same-C identification F ~ F_mod (mainline). -/
  sameCIdentification : Prop
  /-- M1/R1: place selection (qpilot exact names above). -/
  placeSelection : Prop
  /-- Contract-separated capsule-label link (Capsule j.val <-> Bad / V). -/
  capsuleLabelLink : Prop

/-- The exact constant names recorded for the M1 residual (data only). -/
def s3133M1Names : List (String × String) :=
  [ ("S3133M1ContractSeparatedMissing", "S3133M1ContractObstructionActual"),
    ("S3133M1Remaining", "S3133M1InjectionReductionActual"),
    ("S3133BadToAllPlaceIndexInjection_of_bijections", "S3133M1InjectionReductionActual"),
    ("S3133BadTensorIndexEquivalence", "S3133S3131PlaceIndexComparisonActual") ]

/-- The owner map of the route residual data (data only). -/
def firstTriangleRouteResidualOwners : List (String × String) :=
  [ ("M0.same-C", "mainline R1"),
    ("M1.place-selection", "qpilot (names above)"),
    ("M1.capsule-label-link", "contract-separated extra data (qpilot/lattice)"),
    ("stage4.unit-map", "stage4 S3136LGPGlobalUnitsToLocalUnitsActual") ]

end LeanFormal.IUT.XiFPaper.FirstTriangleM0M1SeamActual
