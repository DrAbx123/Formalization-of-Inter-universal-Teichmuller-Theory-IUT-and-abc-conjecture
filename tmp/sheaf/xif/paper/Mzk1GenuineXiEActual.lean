import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual

/-! # Genuine xi-e containment via the LANA possible-region object -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GenuineXiEActual

open CategoryTheory Iut.Multiradial

variable {G : Type*} [Groupoid G] {A : Type*} [Group A]
variable {R : RawOutput G A} {P : G} {X : Type*}

/-- Genuine xi-e containment predicate: the Ind3-region is contained in the
actual possible-region union of the multiradial representation. -/
def XiEContains (reg : R.F.obj P → Set X) (x : R.F.obj P) (S : Set X) : Prop :=
  S ≤ MRRep.possibleRegion reg (MRRep.mk x)

/-- LANA real containment: every Ind3 possible image is contained in the possible
region (this is the non-definitional xi-e set containment). -/
theorem xiE_containment_of_ind3 (reg : R.F.obj P → Set X) (x : R.F.obj P)
    {S : Set X} (hS : S ∈ ind3Possible (reg x)) :
    XiEContains reg x S :=
  MRRep.subset_possibleRegion reg x hS

/-- The representative region itself lies in the possible region. -/
theorem xiE_representative_subset (reg : R.F.obj P → Set X) (x : R.F.obj P) :
    XiEContains reg x (reg x) :=
  MRRep.reg_subset_possibleRegion reg x

end LeanFormal.IUT.XiFPaper.Mzk1GenuineXiEActual
