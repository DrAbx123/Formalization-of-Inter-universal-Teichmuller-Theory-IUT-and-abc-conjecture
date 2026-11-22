import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import tmp.sheaf.xif.paper.RefGogopexRealLineCopyActual

/-! Mainline (A517-8): the Theorem 3.11 multiradial/pilot object layer built on the GREEN
self-contained copies: `RefLANAMultiradialSpecActual` (RawOutput, MRRep, transport,
possibleRegion, IsFunctorialAlg, Thm311iShape) and `RefGogopexRealLineCopyActual` (the
real-line copies and their transports of the algorithmic outputs).  The pilots are compared
as points of these real lines through the transport data. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1RefMultiradialPilotsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

universe u v w w'

/-! ## 1. Multiradial representation objects (green copy) -/

section Multiradial

variable {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]

/-- **O3 object** (green copy): the raw output of the multiradial algorithm. -/
abbrev Thm311RawOutput := Iut.Multiradial.RawOutput G A

/-- **O3 object** (green copy): the multiradial representation at the input `P`. -/
abbrev Thm311MRRep (R : Thm311RawOutput (G := G) (A := A)) (P : G) :=
  Iut.Multiradial.MRRep R P

/-- The representation of a raw-output representative. -/
def thm311MRRepMk (R : Thm311RawOutput (G := G) (A := A)) {P : G}
    (x : R.F.obj P) : Iut.Multiradial.MRRep R P :=
  Iut.Multiradial.MRRep.mk x

/-- **Ind1 independence**: any two isomorphisms of inputs give the same transport of
  representations (green copy). -/
theorem thm311MRRep_transport_eq_transport (R : Thm311RawOutput (G := G) (A := A))
    {P Q : G} (f g : P ⟶ Q) :
    Iut.Multiradial.MRRep.transport (R := R) f =
      Iut.Multiradial.MRRep.transport (R := R) g :=
  Iut.Multiradial.MRRep.transport_eq_transport (R := R) f g

/-- Transport is a bijection of representation types (green copy). -/
def thm311MRRep_transportEquiv (R : Thm311RawOutput (G := G) (A := A)) {P Q : G}
    (f : P ⟶ Q) : Iut.Multiradial.MRRep R P ≃ Iut.Multiradial.MRRep R Q :=
  Iut.Multiradial.MRRep.transportEquiv f

/-- The possible images of a multiradial representation (green copy). -/
def thm311MRRep_possibleRegion (R : Thm311RawOutput (G := G) (A := A)) {P : G} {X : Type*}
    (reg : R.F.obj P → Set X) (r : Iut.Multiradial.MRRep R P) : Set X :=
  Iut.Multiradial.MRRep.possibleRegion reg r

/-- **Functoriality** of a multiradial algorithm (green copy). -/
def Thm311IsFunctorialAlg (R : Thm311RawOutput (G := G) (A := A))
    (alg : ∀ P, Iut.Multiradial.MRRep R P) : Prop :=
  Iut.Multiradial.IsFunctorialAlg R alg

/-- **Theorem 3.11(i) shape** (green copy). -/
def Thm311Shape (R : Thm311RawOutput (G := G) (A := A))
    (alg : ∀ P, Iut.Multiradial.MRRep R P) (P : ℤ → G)
    (Φ : ∀ n n' : ℤ, Set (P n ⟶ P n')) : Prop :=
  Iut.Multiradial.Thm311iShape R alg P Φ

/-- Functoriality implies the Theorem 3.11(i) shape (green copy). -/
theorem thm311Shape_of_isFunctorial (R : Thm311RawOutput (G := G) (A := A))
    {alg : ∀ P, Iut.Multiradial.MRRep R P} (h : Iut.Multiradial.IsFunctorialAlg R alg)
    (P : ℤ → G) (Φ : ∀ n n' : ℤ, Set (P n ⟶ P n')) : Thm311Shape R alg P Φ :=
  Iut.Multiradial.thm311iShape_of_isFunctorial h P Φ

end Multiradial

/-! ## 2. Real-line copies and pilot transports (green copy) -/

section PilotLines

open Iut.RealLineCopy

/-- A real-line copy: the ambient of a pilot log-volume reading. -/
abbrev Thm311RealLineCopy := Copy

/-- A point of a real-line copy. -/
abbrev Thm311RealLinePoint (line : Copy) := Point line

/-- The point of a copy with a given coordinate. -/
def thm311RealLinePoint (line : Copy) (x : ℝ) : Point line :=
  Iut.RealLineCopy.point line x

/-- A positive scale between copies. -/
abbrev Thm311RealLineScale := PositiveScale

/-- A transport between real-line copies (the pilot comparison datum). -/
abbrev Thm311RealLineTransport (source target : Copy) := Transport source target

/-- Transport of a point along a copy-transport. -/
def thm311TransportPoint {source target : Copy} (f : Transport source target)
    (x : Point source) : Point target :=
  Iut.RealLineCopy.Transport.map f x

/-- **Pilot real-line object**: the two copies (q-pilot and Θ-pilot) plus the transport
  between them; the Cor 3.12 comparison is the comparison of transported points. -/
structure Thm311PilotLineObject where
  /-- The q-pilot real-line copy. -/
  qLine : Copy
  /-- The Θ-pilot real-line copy. -/
  thetaLine : Copy
  /-- The transport from the q-line to the Θ-line. -/
  transport : Transport qLine thetaLine

/-- The q-pilot point of the pilot object at coordinate `x = -|log q|`. -/
def Thm311PilotLineObject.qPoint (O : Thm311PilotLineObject) (x : ℝ) : Point O.qLine :=
  Iut.Gogopex.point O.qLine x

/-- The Θ-pilot point transported from the q-line. -/
def Thm311PilotLineObject.thetaPoint (O : Thm311PilotLineObject) (x : ℝ) :
    Point O.thetaLine :=
  Iut.Gogopex.map O.transport (O.qPoint x)

end PilotLines

end

end LeanFormal.IUT.XiFPaper.Mzk1RefMultiradialPilotsActual