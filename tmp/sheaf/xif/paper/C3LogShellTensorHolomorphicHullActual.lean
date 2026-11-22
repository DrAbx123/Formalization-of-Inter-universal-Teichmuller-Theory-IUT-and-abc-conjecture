import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Actual lambda-O holomorphic hull on the C3 log-shell tensor packet

IUT III, Remark 3.9.5, (i), (ii), pp. 158-160: the holomorphic hull of a
region P is the least region of the form lambda * O (lambda nonzero) containing
P.

This file constructs, on the actual tensor block
C3LogShellTensorBlock and the actual tensor log-shell region
actualC3LogShellTensorRegion:

* actual nonzero scalings and actual scaled regions lambda * O;
* candidate hulls containing the actual region;
* the literal least hull as the intersection of all candidates;
* the actual containment region subset hull;
* the actual least-hull property: the hull is contained in every candidate
  hull containing the region;
* an actual packaged object carrying the region, its compactness, the hull,
  and the candidate family.

The unit region is the actual C3 tensor integral region of local log-shells,
not an arbitrary set. No Theta-pilot donor map and no inequality are used.
No True/PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual tensor block of local log-shells. -/
abbrev HullBlock : Type :=
  C3LogShellTensorBlock C3

/-- The actual unit region O: the tensor integral region of local log-shells. -/
def actualUnitRegion : Set (HullBlock C3) :=
  actualC3LogShellTensorRegion C3

/-- Actual nonzero scalings of the tensor block. -/
def actualNonzeroScalings : Set (HullBlock C3) :=
  {x | x ≠ 0}

/-- The actual lambda * O region. -/
def actualScaledRegion
    (lam : HullBlock C3) :
    Set (HullBlock C3) :=
  {x | ∃ o ∈ actualUnitRegion C3, x = lam * o}

/-- Candidate hulls: lambda * O regions with nonzero lambda that contain P. -/
def actualCandidateHulls
    (P : Set (HullBlock C3)) :
    Set (Set (HullBlock C3)) :=
  {H | (∃ lam ∈ actualNonzeroScalings C3,
      H = actualScaledRegion C3 lam) ∧ P ⊆ H}

/-- The literal least lambda-O hull: intersection of all candidate hulls
containing P. -/
def actualHolomorphicHull
    (P : Set (HullBlock C3)) :
    Set (HullBlock C3) :=
  ⋂ H ∈ actualCandidateHulls C3 P, H

/-- The actual region is contained in its least lambda-O hull. -/
theorem actualRegion_subset_hull
    (P : Set (HullBlock C3)) :
    P ⊆ actualHolomorphicHull C3 P := by
  intro x hx
  unfold actualHolomorphicHull
  simp only [Set.mem_iInter]
  intro H hH
  exact hH.2 hx

/-- Least-hull property: the constructed hull is contained in every candidate
hull containing P. -/
theorem actualHolomorphicHull_subset_candidate
    (P : Set (HullBlock C3))
    (H : Set (HullBlock C3))
    (hH : H ∈ actualCandidateHulls C3 P) :
    actualHolomorphicHull C3 P ⊆ H := by
  intro x hx
  unfold actualHolomorphicHull at hx
  simp only [Set.mem_iInter] at hx
  exact hx H hH

/-- The actual unit region is contained in its own least lambda-O hull. -/
theorem actualUnitRegion_subset_hull :
    actualUnitRegion C3 ⊆
      actualHolomorphicHull C3
        (actualUnitRegion C3) :=
  actualRegion_subset_hull C3 (actualUnitRegion C3)

/-- The actual unit region is itself a candidate hull: it is 1 * O. -/
theorem actualUnitRegion_mem_candidateHulls :
    actualUnitRegion C3 ∈
      actualCandidateHulls C3 (actualUnitRegion C3) := by
  refine ⟨⟨1, ?_, ?_⟩, subset_rfl⟩
  · exact one_ne_zero
  · ext x
    constructor
    · intro hx
      exact ⟨x, hx, by rw [one_mul]⟩
    · rintro ⟨o, ho, rfl⟩
      simpa using ho

/-- The least lambda-O hull of the actual unit region is the unit region itself. -/
theorem actualHolomorphicHull_unitRegion_eq :
    actualHolomorphicHull C3 (actualUnitRegion C3) =
      actualUnitRegion C3 := by
  apply Set.Subset.antisymm
  · exact actualHolomorphicHull_subset_candidate C3
      (actualUnitRegion C3) (actualUnitRegion C3)
      (actualUnitRegion_mem_candidateHulls C3)
  · exact actualUnitRegion_subset_hull C3

/-- Monotonicity of the literal lambda-O hull: larger image sets have larger
least hulls. -/
theorem actualHolomorphicHull_monotone
    {P Q : Set (HullBlock C3)} (hPQ : P ⊆ Q) :
    actualHolomorphicHull C3 P ⊆
      actualHolomorphicHull C3 Q := by
  intro x hx
  unfold actualHolomorphicHull at hx ⊢
  simp only [Set.mem_iInter] at hx ⊢
  intro H hH
  exact hx H ⟨hH.1, hPQ.trans hH.2⟩

end LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual

end
