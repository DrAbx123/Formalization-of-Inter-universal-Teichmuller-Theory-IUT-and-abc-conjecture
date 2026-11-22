import tmp.sheaf.xif.paper.ThetaPilotObjectActual
import tmp.sheaf.xif.paper.IndeterminaciesActual
import tmp.sheaf.xif.paper.Ind3UpperSemiActual

/-! # Actual Theta-pilot possible-images hull procession log-volume

IUT III, Theorem 3.11 and Corollary 3.12 (iut3.txt lines 10499-10535,
pp. 173-174): -|log(Theta)| is the procession-normalized mono-analytic
log-volume of the holomorphic hull of the union of possible Theta-pilot images,
relative to the relevant Kummer isomorphisms and subject to (Ind1), (Ind2),
(Ind3).

This file constructs the actual hull object from the source value realization:

* the actual possible-image union and its actual holomorphic hull
  (ThetaPilotObjectActual);
* the actual source Kummer realization R;
* the actual Ind1 carrier-permutation fixedness and Ind2 label-permutation
  fixedness of the possible-image union (IndeterminaciesActual);
* the actual Ind3 upper-semi comparison data (Ind3UpperSemiActual);
* the actual source set volume of the hull and its real log;

and forms the actual procession average over the actual ThetaPilotCarrier
stages and the sum over a finite bad-place set.

The source paper's procession label set is F_l^x; this file uses the project's
actual ThetaPilotCarrier stages and records that label-normalization difference
explicitly.  It does not replace the hull by a raw theta-value sum and does not
fake an inequality.

No sorry, axiom, True, or PUnit is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ThetaPilotHullProcessionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull
open LeanFormal.IUT.XiFPaper.ThetaPilotObjectActual
open LeanFormal.IUT.XiFPaper.Ind3UpperSemiActual
open MeasureTheory

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- The actual possible-image union at (v,R,n). -/
abbrev thetaPilotImageSet : Set (I.ThetaPilotPoint v) :=
  I.possibleThetaPilotImageSet v R n

/-- The actual holomorphic hull of the possible-image union at (v,R,n). -/
abbrev thetaPilotHull : Submonoid (I.ThetaPilotPoint v) :=
  I.sourceHolomorphicHull v R n

/-- The actual source volume of the hull. -/
noncomputable def thetaPilotHullVolume : ENNReal :=
  I.sourceSetVolume v (thetaPilotHull (I := I) v R n : Set (I.ThetaPilotPoint v))

/-- The actual real log of the hull volume. -/
noncomputable def thetaPilotHullLogVolume : Real :=
  (thetaPilotHullVolume (I := I) v R n).toReal

/-- The actual signed hull log-volume (paper sign -|log Theta| at this stage). -/
noncomputable def thetaPilotSignedHullLogVolume : Real :=
  -thetaPilotHullLogVolume (I := I) v R n

/-- Actual hull data at (v,R,n): image union, hull, volume, Kummer realization,
Ind1/Ind2 fixedness, and Ind3 upper-semi data. -/
structure ActualThetaPilotHullData where
  imageSet : Set (I.ThetaPilotPoint v)
  imageSet_eq : imageSet = thetaPilotImageSet (I := I) v R n
  hull : Submonoid (I.ThetaPilotPoint v)
  hull_eq : hull = thetaPilotHull (I := I) v R n
  image_subset_hull : imageSet ⊆ (hull : Set (I.ThetaPilotPoint v))
  kummer : I.SourceImageRealization v
  kummer_eq : kummer = R
  ind1_fixed : forall σ : Equiv.Perm (ThetaPilotCarrier l),
    I.carrierRegionAction v σ imageSet = imageSet
  ind2_fixed : forall τ : Equiv.Perm (SignedLabel l.value),
    I.labelRegionAction v τ imageSet = imageSet
  ind3 : ActualInd3UpperSemiData (I := I) v
  volume : ENNReal
  volume_eq : volume = thetaPilotHullVolume (I := I) v R n
  logVolume : Real
  logVolume_eq : logVolume = thetaPilotHullLogVolume (I := I) v R n

/-- The actual Theta-pilot hull data. -/
noncomputable def actualThetaPilotHullData :
    ActualThetaPilotHullData (I := I) v R n where
  imageSet := thetaPilotImageSet (I := I) v R n
  imageSet_eq := rfl
  hull := thetaPilotHull (I := I) v R n
  hull_eq := rfl
  image_subset_hull := I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n
  kummer := R
  kummer_eq := rfl
  ind1_fixed := fun σ =>
    I.possibleThetaPilotImageSet_carrierPerm_fixed v R n σ
  ind2_fixed := fun τ =>
    I.possibleThetaPilotImageSet_labelPerm_fixed v R n τ
  ind3 := actualInd3UpperSemiData (I := I) v
  volume := thetaPilotHullVolume (I := I) v R n
  volume_eq := rfl
  logVolume := thetaPilotHullLogVolume (I := I) v R n
  logVolume_eq := rfl

/-- The actual procession average over the project's ThetaPilotCarrier stages
of the signed hull log-volume. -/
noncomputable def localThetaPilotHullProcessionLogVolume : Real :=
  (Fintype.card (ThetaPilotCarrier l) : Real)⁻¹ *
    ∑ n : ThetaPilotCarrier l,
      thetaPilotSignedHullLogVolume (I := I) v R n

/-- The actual global candidate: sum over a supplied finite bad-place set of
the local procession averages. -/
noncomputable def globalThetaPilotHullProcessionLogVolume
    (S : Finset V) (R : (v : V) -> I.SourceImageRealization v) : Real :=
  ∑ v in S, localThetaPilotHullProcessionLogVolume (I := I) v (R v)

/-- The actual hull data is the package used by the procession candidate. -/
theorem globalThetaPilotHullProcessionLogVolume_eq_sum
    (S : Finset V) (R : (v : V) -> I.SourceImageRealization v) :
    globalThetaPilotHullProcessionLogVolume (I := I) S R =
      ∑ v in S, (Fintype.card (ThetaPilotCarrier l) : Real)⁻¹ *
        ∑ n : ThetaPilotCarrier l,
          thetaPilotSignedHullLogVolume (I := I) v (R v) n := rfl

end LeanFormal.IUT.XiFPaper.ThetaPilotHullProcessionActual

end
