/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual

/-!
# Mzk1MRRepObjectActual — LANA Multiradial MRRep/RawOutput/possibleRegion object (3.11)

A516: reference object from LANA latest `Iut/Multiradial/Spec.lean`, the
formal reading of IUT III Theorem 3.11(i): a raw output functor with (Ind2)-action
(`RawOutput`), the (Ind1)×(Ind2)-orbit type (`MRRep`), the possible-image union
(`MRRep.possibleRegion`), transport along input isomorphisms (`MRRep.transport`),
and the functorial-algorithm shape (`IsFunctorialAlg`, `Thm311iShape`).

Everything is stated for an arbitrary input groupoid and raw output (as in LANA);
the concrete IUT input groupoid is the procession groupoid of `Procession C n`
(see `Mzk1ProcessionInd23ObjectActual`). No new axiom, no comparison. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1MRRepObjectActual

open CategoryTheory
open Iut.Multiradial
universe u v w w'

variable {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]

/-- The multiradial-representation object: raw output + an input + its MRRep class. -/
structure MRRepObject where
  raw : RawOutput G A
  input : G
  rep : MRRep raw input

/-- The object given by a representative `x` of the raw output. -/
def mrRepObject (raw : RawOutput G A) (P : G) (x : raw.F.obj P) :
    MRRepObject (G := G) (A := A) where
  raw := raw
  input := P
  rep := MRRep.mk x

/-- `_constructed`: the object's class is `MRRep.mk x`. -/
theorem mrRepObject_constructed (raw : RawOutput G A) (P : G) (x : raw.F.obj P) :
    (mrRepObject raw P x).rep = MRRep.mk x := rfl

/-- The orbit quotient is exhausted by representatives. -/
theorem mrRep_exists_representative (raw : RawOutput G A) (P : G) (r : MRRep raw P) :
    ∃ x : raw.F.obj P, MRRep.mk x = r := MRRep.exists_mk r

/-- The region of a representative is contained in the possible images. -/
theorem mrRep_reg_subset_possibleRegion (raw : RawOutput G A) (P : G)
    {X : Type*} (reg : raw.F.obj P → Set X) (x : raw.F.obj P) :
    reg x ⊆ MRRep.possibleRegion reg (MRRep.mk (R := raw) x) :=
  MRRep.reg_subset_possibleRegion reg x

/-- Transport of MRRep classes along an input isomorphism. -/
def mrRep_transport (raw : RawOutput G A) {P Q : G} (f : P ⟶ Q) :
    MRRep raw P → MRRep raw Q := MRRep.transport f

/-- Transport of a representative. -/
theorem mrRep_transport_mk (raw : RawOutput G A) {P Q : G} (f : P ⟶ Q)
    (x : raw.F.obj P) :
    MRRep.transport f (MRRep.mk (R := raw) x) = MRRep.mk (raw.F.map f x) :=
  MRRep.transport_mk f x

/-- The functorial-algorithm shape of Theorem 3.11(i). -/
def mrRep_thm311iShape (raw : RawOutput G A) (alg : ∀ P, MRRep raw P)
    (P : ℤ → G) (Φ : ∀ n n' : ℤ, Set (P n ⟶ P n')) : Prop :=
  Thm311iShape raw alg P Φ

/-- Functoriality implies the poly-isomorphism compatibility shape. -/
theorem mrRep_thm311iShape_of_isFunctorial (raw : RawOutput G A)
    {alg : ∀ P, MRRep raw P} (h : IsFunctorialAlg raw alg)
    (P : ℤ → G) (Φ : ∀ n n' : ℤ, Set (P n ⟶ P n')) :
    mrRep_thm311iShape raw alg P Φ :=
  thm311iShape_of_isFunctorial h P Φ

#check mrRepObject_constructed
#check mrRep_reg_subset_possibleRegion
#check mrRep_thm311iShape

end LeanFormal.IUT.XiFPaper.Mzk1MRRepObjectActual
end
