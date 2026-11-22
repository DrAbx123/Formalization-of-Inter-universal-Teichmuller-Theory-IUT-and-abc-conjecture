import tmp.sheaf.xif.paper.LiteralIQCarrierConstructionActual
import tmp.sheaf.xif.paper.ThetaHullActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Literal IQ-carrier holomorphic hull operation

IUT III, Remark 3.9.5, (i), (ii), pp. 158-160: for a possible-image union P,
the holomorphic hull is the least subset of the form lambda * O (components of
lambda nonzero) containing P, equivalently the intersection of all such H
containing P.

This file constructs, on the actual completion-packet IQ ambient carrier
LiteralIQAmbient of LiteralIQCarrierConstructionActual:

* the actual scaled region literalIQScaledRegion lam O;
* the actual nonzero scaling set;
* the literal lambda-O hull operation as the intersection of all scaled
  unit-region candidates containing the supplied image set;
* the actual containment P subset literalIQHolomorphicHull P, for any supplied
  subset P of the actual ambient carrier.

The possible Theta-pilot image set itself is not fabricated: the paper's
n,circ U_{j,vQ} is a subset of the literal carrier obtained from the
D-prime/F-prime-strip capsule and its log-shells. The exact missing source fields
are recorded below.

## Exact missing fields
* D-prime-strip capsule / F-prime-strip data and the log-shell lattice I(D_v)
  (IUT III, Proposition 3.2, (i), (ii), pp. 97-99);
* identification of the actual completion-packet places C3.tensorPlaces with
  those capsule log-shells (IUT III, Theorem 3.11, pp. 160-162; IUT IV,
  Theorem 1.10 proof, pp. 26-27);
* the actual possible-image inclusion n,circ U_{j,vQ} subset LiteralIQAmbient
  from the Theta-pilot object;
* compactness of 1,circ U_{j,vQ} and of its hull (IUT III, Step (xi-d),
  pp. 174-175);
* the Kummer isomorphisms/log-Kummer data used to compare the images
  (IUT III, Theorem 3.11, (ii)).

No arbitrary image set is chosen; the hull operation is constructed for any
supplied subset, and its containment is proved. No True/PUnit, axiom, or sorry
is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.LiteralIQHolomorphicHullActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction
open LeanFormal.IUT.Theorem311Source

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-- The actual ambient completion-packet tensor at level j. -/
abbrev HullAmbient (j : Nat) : Type :=
  LiteralIQAmbient (C3 := C3) j

/-- The actual unit region O of the completion-packet tensor. -/
def hullUnitRegion (j : Nat) : Set (HullAmbient (C3 := C3) j) :=
  literalIQUnitRegion (C3 := C3) j

/-- The actual nonzero scalings of the ambient completion-packet tensor. -/
def hullNonzeroScalings (j : Nat) : Set (HullAmbient (C3 := C3) j) :=
  {x | x ≠ 0}

/-- The literal lambda * O region: componentwise multiplication of the unit
region by a nonzero ambient scaling. -/
def literalIQScaledRegion (j : Nat)
    (lam : HullAmbient (C3 := C3) j) :
    Set (HullAmbient (C3 := C3) j) :=
  {x | ∃ o ∈ hullUnitRegion (C3 := C3) j, x = lam * o}

/-- Candidate hulls: the lambda * O regions with nonzero scaling that contain
the supplied image set P. -/
def literalIQCandidateHulls (j : Nat)
    (P : Set (HullAmbient (C3 := C3) j)) :
    Set (Set (HullAmbient (C3 := C3) j)) :=
  {H | (∃ lam ∈ hullNonzeroScalings (C3 := C3) j,
      H = literalIQScaledRegion (C3 := C3) j lam) ∧ P ⊆ H}

/-- The literal lambda-O holomorphic hull operation of Remark 3.9.5. It is the
intersection of all nonzero-scaled unit-region candidates containing P. -/
def literalIQHolomorphicHull (j : Nat)
    (P : Set (HullAmbient (C3 := C3) j)) :
    Set (HullAmbient (C3 := C3) j) :=
  ⋂ H ∈ literalIQCandidateHulls (C3 := C3) j P, H

/-- The actual containment of the image set in its literal lambda-O hull. -/
theorem literalIQImage_subset_holomorphicHull (j : Nat)
    (P : Set (HullAmbient (C3 := C3) j)) :
    P ⊆ literalIQHolomorphicHull (C3 := C3) j P := by
  intro x hx
  unfold literalIQHolomorphicHull
  simp only [Set.mem_iInter]
  intro H hH
  exact hH.2 hx

/-- A candidate hull belongs to the literal hull family exactly when it is a
nonzero-scaled unit region containing P. -/
theorem mem_literalIQCandidateHulls_iff (j : Nat)
    (P : Set (HullAmbient (C3 := C3) j))
    (H : Set (HullAmbient (C3 := C3) j)) :
    H ∈ literalIQCandidateHulls (C3 := C3) j P ↔
      (∃ lam ∈ hullNonzeroScalings (C3 := C3) j,
        H = literalIQScaledRegion (C3 := C3) j lam) ∧ P ⊆ H :=
  Iff.rfl

/-- Exact missing D-prime/F-prime-strip capsule and log-shell data: a source map
from the Theta-pilot carrier to the actual completion-packet ambient carrier. -/
structure MissingLiteralIQCapsuleLogShell where
  j : Nat
  source_image : Set (HullAmbient (C3 := C3) j)
  source_image_nonempty : source_image.Nonempty
  source_identification : Prop

/-- Exact missing object package for the literal holomorphic hull: images,
capsule/log-shell identification, and compactness. -/
structure MissingLiteralIQHolomorphicHullData where
  capsule : MissingLiteralIQCapsuleLogShell (C3 := C3)
  hull_compact : IsCompact
    (literalIQHolomorphicHull (C3 := C3) capsule.j capsule.source_image)

/-- The exact missing object is not asserted; this records the data needed. -/
def LiteralIQHolomorphicHullMissing : Prop :=
  Nonempty (MissingLiteralIQHolomorphicHullData (C3 := C3))

end LeanFormal.IUT.XiFPaper.LiteralIQHolomorphicHullActual

end
