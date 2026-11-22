import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual

/-! # Mzk1MRSpecConsumerGlueActual — consumer forms of the LANA multiradial rep objects

Small reference/glue module (no new mathematics): consumes the already-proved Theorem 3.11
objects of the LANA `Multiradial/Spec` card (`RawOutput`, `MRRep`, `possibleRegion`,
`IsFunctorialAlg`, procession transport) in the forms used by the IUT III Corollary 3.12
route.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1MRSpecConsumerGlueActual

open CategoryTheory
open Iut.Multiradial

universe u v w w'

variable {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]
variable {R : RawOutput.{u, v, w} G A}

/-- Representative-level transport of the multiradial representation. -/
theorem transport_mk_apply {P Q : G} (f : P ⟶ Q) (x : R.F.obj P) :
    MRRep.transport f (MRRep.mk (R := R) x) =
      MRRep.mk (R := R) (R.F.map f x) :=
  MRRep.transport_mk (R := R) f x

/-- Transport along a composite is the composite of transports. -/
theorem transport_comp_apply {P Q S : G} (f : P ⟶ Q) (g : Q ⟶ S)
    (r : MRRep R P) :
    MRRep.transport (f ≫ g) r = MRRep.transport g (MRRep.transport f r) :=
  MRRep.transport_comp (R := R) f g r

/-- The region of a representative is contained in the possible region of its class. -/
theorem possibleRegion_reg_subset {P : G} {X : Type*}
    (reg : R.F.obj P → Set X) (x : R.F.obj P) :
    reg x ⊆ MRRep.possibleRegion (R := R) reg (MRRep.mk (R := R) x) :=
  MRRep.reg_subset_possibleRegion (R := R) reg x

/-- For a functorial algorithm, all isomorphisms of inputs induce the same transport:
the (Ind1)-invariance of Theorem 3.11(i). -/
theorem functorial_transport_eq {alg : ∀ P, MRRep R P}
    (h : IsFunctorialAlg R alg) {P Q : G} (f g : P ⟶ Q) :
    MRRep.transport f (alg P) = MRRep.transport g (alg P) := by
  rw [h f, h g]

/-- A section of the raw-output functor gives a functorial algorithm. -/
theorem functorial_of_section (s : R.F.sections) :
    IsFunctorialAlg R (fun P => MRRep.mk (s.val P)) :=
  IsFunctorialAlg.of_section (R := R) s

/-- Poly-isomorphism compatibility: two members of the same poly-isomorphism induce the
same representation transport. -/
theorem polyIso_transport_eq {alg : ∀ P, MRRep R P}
    (h : IsFunctorialAlg R alg) {P Q : G} {Φ : Set (P ⟶ Q)} {f g : P ⟶ Q}
    (hf : f ∈ Φ) (hg : g ∈ Φ) :
    MRRep.transport (R := R) f = MRRep.transport g :=
  (h.polyIso_compat Φ).2 f hf g hg

/-- The transport equivalence acts by transport. -/
theorem transportEquiv_apply {P Q : G} (f : P ⟶ Q) (r : MRRep R P) :
    MRRep.transportEquiv f r = MRRep.transport f r := rfl

#check transport_mk_apply
#check transport_comp_apply
#check possibleRegion_reg_subset
#check functorial_transport_eq
#check functorial_of_section
#check polyIso_transport_eq

end LeanFormal.IUT.XiFPaper.Mzk1MRSpecConsumerGlueActual
end
