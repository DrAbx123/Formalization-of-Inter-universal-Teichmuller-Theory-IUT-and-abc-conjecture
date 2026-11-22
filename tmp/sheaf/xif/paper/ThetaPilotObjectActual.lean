import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import tmp.sheaf.xif.SourceXiFConstruction
import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalIdealFamily
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelDivisor

/-!
# Theta-pilot object: actual source value image/hull and missing arithmetic divisor

IUT III, Definition 3.8, (i), and Corollary 3.12, define the Theta-pilot object as
the arithmetic divisor determined by the zero locus of the theta values
q_j^2 (j in F_l^*) at bad places, and consider the holomorphic hull of the
union of its possible multiradial images.

The project constructs the actual source value realization of the theta-pilot
image at each place v:

  possibleThetaPilotImageSet v R n : Set (I.ThetaPilotPoint v)

as the union of the actual theta-pilot points sourceThetaPilotPoint v R n j,
and the actual source holomorphic hull

  sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v).

This file packages those actual sets as a Theta-pilot image/hull object. It does
NOT claim that this value-realized hull is the paper's arithmetic-divisor
Theta-pilot object: the global arithmetic divisor determined by the zero locus
of the theta values requires the source theta functions/line bundle, which are
not in the tree. That missing object is recorded separately, without inequality.

The q-pilot point relation used is only the actual set membership
qPilotPoint ∈ sourceHolomorphicHull, proved from the existing source hull
membership; no log-volume inequality is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.ThetaPilotObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe ua uv upi umon ui uF

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual source value realization of the Theta-pilot image and its
holomorphic hull at a place v and procession n. -/
structure ThetaPilotImageHullAt
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) where
  imageSet : Set (I.ThetaPilotPoint v)
  imageSet_eq : imageSet = I.possibleThetaPilotImageSet v R n
  hull : Set (I.ThetaPilotPoint v)
  hull_eq : hull = (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))
  image_subset_hull : imageSet ⊆ hull
  hull_nonempty : hull.Nonempty

/-- Actual Theta-pilot image/hull object from the source realization. -/
noncomputable def thetaPilotImageHullAt
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    ThetaPilotImageHullAt (I := I) v R n where
  imageSet := I.possibleThetaPilotImageSet v R n
  imageSet_eq := rfl
  hull := I.sourceHolomorphicHull v R n
  hull_eq := rfl
  image_subset_hull := I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n
  hull_nonempty := by
    rcases I.possibleThetaPilotImageSet_nonempty v R n with ⟨x, hx⟩
    exact ⟨x, I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n hx⟩

/-- The actual q-pilot point lies in the actual Theta-pilot hull. -/
theorem qPilotPoint_mem_thetaPilotHull
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceQPilotPoint v R n ∈
      (thetaPilotImageHullAt (I := I) v R n).hull := by
  change I.sourceThetaPilotPoint v R n (oneSignedLabel (l := l)) ∈
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))
  exact I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n
    (oneSignedLabel (l := l))

/-- The actual Theta-pilot image is contained in the actual hull. -/
theorem thetaPilotImage_subset_hull
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (thetaPilotImageHullAt (I := I) v R n).imageSet ⊆
      (thetaPilotImageHullAt (I := I) v R n).hull :=
  (thetaPilotImageHullAt (I := I) v R n).image_subset_hull

/-- Exact missing paper object: the arithmetic divisor determined by the zero
locus of the theta values q_j^2 together with the q-pilot divisor and their
Theta-link relation. No divisor, zero locus, or link is fabricated. -/
structure ThetaPilotArithmeticDivisorData (F : Type uF) [Field F] [NumberField F] where
  thetaDivisor : GlobalIdealFamily F
  qPilotDivisor : GlobalIdealFamily F
  thetaZeroLocusData : Prop
  qPilotZeroLocusData : Prop
  thetaLinkRelation : Prop

/-- Exact missing arithmetic-divisor object for the Theta-pilot. -/
def MissingThetaPilotArithmeticDivisor
    (F : Type uF) [Field F] [NumberField F] : Prop :=
  Nonempty (ThetaPilotArithmeticDivisorData F)

end LeanFormal.IUT.XiFPaper.ThetaPilotObjectActual

end
