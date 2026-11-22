import tmp.sheaf.xif.paper.Indet01FirstTriangleIndActual
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind1QuotientTransport
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind2AlienCopySeparation
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Indet02: BPS -> multiradial representation, up to (Ind1),(Ind2), (Ind3) one-sided

Paper: the passage to the multiradial representation is obtained by admitting the
three indeterminacies (IUT III 653-679; MHYY §4, first triangle).  The production
generic kernel already proves that the formal quotient absorbs the (Ind1) and
(Ind2) actions (MultiradialOutputKernel.Core.generatedQuotientMap_ind1/_ind2) and
that on the proved finite instance the indeterminacy class is a complete
invariant of the vertical level (SourceFiniteMultiradial.quotientClass_eq_iff_level_eq).
(Ind3) is one-sided (upper-semi) and is NOT quotiented (no reverse dominance).

This file exposes the exact up-to statement used by the first triangle:
the BPS -> multiradial representation map is well defined up to (Ind1),(Ind2),
and (Ind3) only raises the level (one-sided).

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Indet02BPSMultiradialUpToActual

open LeanFormal.IUT
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.MultiradialKernel.Core
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.SourceFiniteMultiradial
open LeanFormal.IUT.Ind3UpperSemi
open LeanFormal.IUT.XiFPaper.Indet01FirstTriangleIndActual

universe u

/-- The BPS -> multiradial representation map, taken up to (Ind1) and (Ind2):
the formal quotient of the multiradial kernel. -/
def bpsToMultiradial (l : PrimeGeFive) :
    ProcessionChoice l → GeneratedQuotient (core l) :=
  generatedQuotientMap (core l)

/-- (Ind1) acts trivially on the multiradial-representation class. -/
theorem bpsToMultiradial_ind1 (l : PrimeGeFive) (g : finiteLabel l)
    (c : ProcessionChoice l) :
    bpsToMultiradial l (firstTriangleInd1 l g c) = bpsToMultiradial l c :=
  generatedQuotientMap_ind1 (core l) g c

/-- (Ind2) acts trivially on the multiradial-representation class. -/
theorem bpsToMultiradial_ind2 (l : PrimeGeFive) (g : finiteLabel l)
    (c : ProcessionChoice l) :
    bpsToMultiradial l (firstTriangleInd2 l g c) = bpsToMultiradial l c :=
  generatedQuotientMap_ind2 (core l) g c

/-- Equality of multiradial-representation classes is exactly equality of the
vertical level on the proved finite instance (up to (Ind1),(Ind2)). -/
theorem bpsToMultiradial_eq_iff_level (l : PrimeGeFive)
    {a b : ProcessionChoice l} :
    bpsToMultiradial l a = bpsToMultiradial l b ↔
      a.upperSemiLevel = b.upperSemiLevel :=
  quotientClass_eq_iff_level_eq l

/-- (Ind3) dominance: b is an (Ind3) lift of a. -/
def Ind3Dominates (l : PrimeGeFive) (a b : ProcessionChoice l) : Prop :=
  ∃ n : Nat, b = ProcessionChoice.ind3Lift n a

/-- (Ind3) dominance raises the level (one-sided; no symmetry). -/
theorem Ind3Dominates.level_le {l : PrimeGeFive} {a b : ProcessionChoice l}
    (h : Ind3Dominates l a b) : a.upperSemiLevel ≤ b.upperSemiLevel := by
  rcases h with ⟨n, rfl⟩
  exact Nat.le_add_right a.upperSemiLevel n

/-- (Ind3) upper-semi at the level of possible images (reused finite profile law). -/
theorem firstTriangleInd3_possibleImage_upper (l : PrimeGeFive) (n : Nat)
    (c : ProcessionChoice l) (z : Real) (hz : z ∈ (profile l).possibleImage c) :
    ∃ w, w ∈ (profile l).possibleImage (firstTriangleInd3 l n c) ∧ z ≤ w :=
  (profile l).possibleImage_ind3 n c z hz

/-- A multiradial representation prescribed only up to (Ind1),(Ind2): a
representative of the BPS, whose class is the invariant object. -/
structure SourceMltRepUpTo (l : PrimeGeFive) where
  /-- a chosen BPS/procession representative -/
  representative : ProcessionChoice l

/-- The invariant class of a multiradial representation. -/
def SourceMltRepUpTo.repClass {l : PrimeGeFive} (x : SourceMltRepUpTo l) :
    GeneratedQuotient (core l) :=
  bpsToMultiradial l x.representative

/-- The class is independent of the representative up to (Ind1),(Ind2). -/
theorem SourceMltRepUpTo.repClass_congr {l : PrimeGeFive}
    (x y : SourceMltRepUpTo l)
    (h : bpsToMultiradial l x.representative = bpsToMultiradial l y.representative) :
    x.repClass = y.repClass :=
  h

/-- The up-to statement: two multiradial representations are equal as such iff
their representatives have the same level (the (Ind3) direction is one-sided). -/
theorem SourceMltRepUpTo.repClass_eq_iff_level {l : PrimeGeFive}
    (x y : SourceMltRepUpTo l) :
    x.repClass = y.repClass ↔
      x.representative.upperSemiLevel = y.representative.upperSemiLevel :=
  bpsToMultiradial_eq_iff_level l

/-- The full poly-isomorphism / 0-column gluing anchor: the passage from the BPS
to the multiradial representation in the first triangle is an arbitrary
indeterminate isomorphism glued to the 0-column, formalized in this tree by the
certified C3 convention identification (cross-reference to mainline A35). -/
def firstTrianglePolyIsoAnchors : List (String × String) :=
  [ ("BPS glued to the underlying BPS of the Theta-pilot at (0,0) via a full poly-isomorphism",
      "MHYY Formalization of IUT (2026-04) §4, lines 472-501"),
    ("formal C3 convention identification (polyIso vs procession convention)",
      "S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds"),
    ("generic quotient absorbs (Ind1)/(Ind2)", "MultiradialOutputKernel.Core.generatedQuotientMap_ind1/_ind2"),
    ("class = same vertical level (finite instance)", "SourceFiniteMultiradial.quotientClass_eq_iff_level_eq"),
    ("(Ind3) one-sided upper-semi", "Ind3UpperSemiConstruction.outputImageFamily_upper") ]

end LeanFormal.IUT.XiFPaper.Indet02BPSMultiradialUpToActual

end
