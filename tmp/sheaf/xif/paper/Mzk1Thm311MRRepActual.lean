import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import Mathlib.CategoryTheory.Groupoid

open CategoryTheory

/-! Mainline (A516-1): Theorem 3.11 multiradial objects, referenced from the real LANA-latest
`Iut/Multiradial/Spec.lean` file: the raw output of a multiradial algorithm (`RawOutput` with
the (Ind2)-action, Theorem 3.11(i)(a),(b),(c)), the multiradial representation `MRRep` (the
(Ind1)×(Ind2)-orbit), the transport along isomorphisms of inputs (`transport`,
`transportEquiv`, `transport_eq_transport`), the possible images (`possibleRegion`,
`reg_subset_possibleRegion`, `MRRep.subset_possibleRegion`), the functoriality predicate
`IsFunctorialAlg`, and the Theorem 3.11(i) shape `Thm311iShape`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm311MRRepActual

open CategoryTheory
open Iut.Multiradial

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

universe u v w w'

section Objects

variable {G : Type u} [Groupoid G] {A : Type w'} [Group A]

/-- **O3 raw output object**: a multiradial algorithm's raw output (Theorem 3.11(i)) — a
  functor on the groupoid of inputs with the commuting (Ind2)-action. -/
structure RawOutputObject {G : Type u} [Groupoid G] {A : Type w'} [Group A] where
  /-- The LANA raw output structure. -/
  raw : Iut.Multiradial.RawOutput G A
  /-- The input object (a procession `Prc(n,∘D^⊢_T)`). -/
  input : G

/-- **O3 multiradial representation object**: the raw output together with the functorial
  algorithm assignment `alg` (Theorem 3.11(i), the multiradial representation `n,∘R^LGP`). -/
structure MultiradialRepresentationObject {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A] where
  /-- The LANA raw output structure. -/
  raw : Iut.Multiradial.RawOutput G A
  /-- The input object. -/
  input : G
  /-- The assignment of multiradial representations. -/
  alg : ∀ P, Iut.Multiradial.MRRep raw P

/-- The multiradial representation at the object's input. -/
def MultiradialRepresentationObject.atInput
    (O : MultiradialRepresentationObject (G := G) (A := A)) := Iut.Multiradial.MRRep O.raw O.input

/-- The representation of a raw-output representative. -/
def mrRepMk (O : MultiradialRepresentationObject (G := G) (A := A))
    (x : O.raw.F.obj O.input) : O.atInput :=
  Iut.Multiradial.MRRep.mk x

/-- Two representatives give the same multiradial representation iff they differ by an
  (Ind1)×(Ind2)-element (LANA real lemma). -/
theorem mrRep_mk_eq_mk_iff (O : MultiradialRepresentationObject (G := G) (A := A))
    (x y : O.raw.F.obj O.input) :
    mrRepMk O x = mrRepMk O y ↔
      ∃ (σ : Aut O.input) (a : A), y = σ • (a • x) :=
  Iut.Multiradial.MRRep.mk_eq_mk_iff x y

/-- Transport of multiradial representations along an isomorphism of inputs. -/
def mrRepTransport (O : MultiradialRepresentationObject (G := G) (A := A))
    {P Q : G} (f : P ⟶ Q) (r : Iut.Multiradial.MRRep O.raw P) :
    Iut.Multiradial.MRRep O.raw Q :=
  Iut.Multiradial.MRRep.transport f r

/-- **(Ind1) independence**: any two isomorphisms of inputs induce the same transport of
  multiradial representations (LANA real theorem). -/
theorem mrRep_transport_eq_transport (O : MultiradialRepresentationObject (G := G) (A := A))
    {P Q : G} (f g : P ⟶ Q) :
    mrRepTransport O f = mrRepTransport O g :=
  Iut.Multiradial.MRRep.transport_eq_transport (R := O.raw) f g

/-- Transport is a bijection of representation types (LANA real def). -/
def mrRepTransportEquiv (O : MultiradialRepresentationObject (G := G) (A := A))
    {P Q : G} (f : P ⟶ Q) :
    Iut.Multiradial.MRRep O.raw P ≃ Iut.Multiradial.MRRep O.raw Q :=
  Iut.Multiradial.MRRep.transportEquiv f

/-- **Possible images** of a multiradial representation (union over the orbit). -/
def mrRepPossibleRegion (O : MultiradialRepresentationObject (G := G) (A := A))
    {X : Type*} (reg : O.raw.F.obj O.input → Set X)
    (r : Iut.Multiradial.MRRep O.raw O.input) : Set X :=
  Iut.Multiradial.MRRep.possibleRegion reg r

/-- A representative's region is contained in the possible images (LANA real lemma). -/
theorem mrRep_reg_subset_possibleRegion (O : MultiradialRepresentationObject (G := G) (A := A))
    {X : Type*} (reg : O.raw.F.obj O.input → Set X) (x : O.raw.F.obj O.input) :
    reg x ⊆ mrRepPossibleRegion O reg (mrRepMk O x) :=
  Iut.Multiradial.MRRep.reg_subset_possibleRegion reg x

/-- **(Ind3) does not enlarge the possible images**: a region upper semi-compatible with a
  representative's region is contained in the possible images (LANA real theorem). -/
theorem mrRep_subset_possibleRegion (O : MultiradialRepresentationObject (G := G) (A := A))
    {X : Type*} (reg : O.raw.F.obj O.input → Set X) (x : O.raw.F.obj O.input)
    {S : Set X} (hS : S ∈ Iut.Multiradial.ind3Possible (reg x)) :
    S ⊆ mrRepPossibleRegion O reg (mrRepMk O x) :=
  Iut.Multiradial.MRRep.subset_possibleRegion reg x hS

/-- **Functoriality** (IUT III Theorem 3.11(i); LANA real predicate). -/
def IsFunctorialMultiradialAlgorithm (O : MultiradialRepresentationObject (G := G) (A := A)) :
    Prop :=
  Iut.Multiradial.IsFunctorialAlg O.raw O.alg

/-- **Theorem 3.11(i) shape** (LANA real def): functoriality plus compatibility of the
  étale-picture permutation symmetries. -/
def Thm311iShape (O : MultiradialRepresentationObject (G := G) (A := A))
    (P : ℤ → G) (Φ : ∀ n n' : ℤ, Set (P n ⟶ P n')) : Prop :=
  Iut.Multiradial.Thm311iShape O.raw O.alg P Φ

/-- Functoriality implies the Theorem 3.11(i) shape (LANA real theorem). -/
theorem thm311iShape_of_isFunctorial (O : MultiradialRepresentationObject (G := G) (A := A))
    (h : IsFunctorialMultiradialAlgorithm O) (P : ℤ → G)
    (Φ : ∀ n n' : ℤ, Set (P n ⟶ P n')) : Thm311iShape O P Φ :=
  Iut.Multiradial.thm311iShape_of_isFunctorial h P Φ

end Objects

end

end LeanFormal.IUT.XiFPaper.Mzk1Thm311MRRepActual