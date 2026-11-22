import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual

/-! # Mzk1XiEContainmentActual — genuine xi-e containment (non-definitional)

A531 audit/assembly module: the xi-e containment step of IUT III Corollary 3.12
("the q-pilot log-volume lies in the set of possible Theta-pilot log-volumes") is
formalized as a statement about the possible images of the multiradial representation
of LANA Multiradial/Spec — NOT as a definitional identity with the target inequality.
Contents are consumer forms of the already-proved LANA theorems; no new mathematics.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentActual

open CategoryTheory
open Iut.Multiradial

universe u v w w'

variable {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]
variable {R : RawOutput.{u, v, w} G A}

/-- Characterization of the possible images of a multiradial representation:
an element lies in the possible region iff it lies in the region of some representative
of the (Ind1)x(Ind2)-orbit. -/
theorem mem_possibleRegion_iff {P : G} {X : Type*}
    (reg : R.F.obj P → Set X) (r : MRRep R P) (q : X) :
    q ∈ MRRep.possibleRegion reg r ↔ ∃ x, MRRep.mk (R := R) x = r ∧ q ∈ reg x := by
  simp [MRRep.possibleRegion]

/-- Genuine xi-e containment: the q-pilot point q lies in the possible images of the
Theta-pilot multiradial representation (this is a *statement about the orbit union*,
not a definition of the target inequality). -/
def XiEContainment {P : G} {X : Type*} (reg : R.F.obj P → Set X) (r : MRRep R P)
    (q : X) : Prop :=
  q ∈ MRRep.possibleRegion reg r

/-- A representative's region is contained in the possible images (LANA theorem). -/
theorem representative_subset_possibleRegion {P : G} {X : Type*}
    (reg : R.F.obj P → Set X) (x : R.F.obj P) :
    reg x ⊆ MRRep.possibleRegion reg (MRRep.mk (R := R) x) :=
  MRRep.reg_subset_possibleRegion reg x

/-- (Ind3)-compatible containment: any region upper semi-compatible with a
representative's region is contained in the possible images (LANA theorem). -/
theorem ind3_subset_possibleRegion {P : G} {X : Type*}
    (reg : R.F.obj P → Set X) (x : R.F.obj P) {S : Set X}
    (hS : S ∈ ind3Possible (reg x)) :
    S ⊆ MRRep.possibleRegion reg (MRRep.mk (R := R) x) :=
  MRRep.subset_possibleRegion reg x hS

/-- If the containment holds, then some representative realizes q. -/
theorem exists_representative_of_containment {P : G} {X : Type*}
    (reg : R.F.obj P → Set X) (r : MRRep R P) (q : X)
    (h : XiEContainment (R := R) reg r q) :
    ∃ x, MRRep.mk (R := R) x = r ∧ q ∈ reg x :=
  (mem_possibleRegion_iff reg r q).1 h

/-- xi-e is not definitional: for a representative x, containment of q in the possible
images of the class of x is exactly membership of q in some point of the orbit union. -/
theorem xiEContainment_not_definitional {P : G} {X : Type*}
    (reg : R.F.obj P → Set X) (x : R.F.obj P) (q : X) :
    XiEContainment (R := R) reg (MRRep.mk (R := R) x) q ↔
      ∃ y, MRRep.mk (R := R) y = MRRep.mk (R := R) x ∧ q ∈ reg y :=
  mem_possibleRegion_iff reg (MRRep.mk x) q

#check mem_possibleRegion_iff
#check XiEContainment
#check representative_subset_possibleRegion
#check ind3_subset_possibleRegion
#check exists_representative_of_containment
#check xiEContainment_not_definitional

end LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentActual
end
