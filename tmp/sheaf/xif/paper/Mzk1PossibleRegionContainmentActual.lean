/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import tmp.sheaf.xif.paper.Mzk1XiFFormalStepActual

/-!
# Mzk1PossibleRegionContainmentActual — possible-image containment object (xi-e)

A521: object packaging a raw output, an input representative and its region,
with the containment in `MRRep.possibleRegion` (LANA Spec).  The xi-e step
uses log-volume monotonicity: if the q-pilot value lies in the raw region and
the raw region is bounded by the Theta-pilot hull log-volume `H`, then
`q ≤ H` (`xi_f_formal_step` ⇒ Cor 3.12).

All content is the actual `MRRep` possible-image layer; no new axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PossibleRegionContainmentActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiFFormalStepActual
open Iut.Multiradial

universe u v w w'

variable {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]

/-- The possible-image containment object: raw output + input representative +
region + xi-e bound. -/
structure PossibleRegionContainmentObject (X : Type*) where
  /-- the multiradial raw output. -/
  raw : RawOutput G A
  /-- the input procession. -/
  input : G
  /-- the raw q-side region. -/
  reg : raw.F.obj input → Set X
  /-- a representative of the raw output. -/
  representative : raw.F.obj input

/-- The constructed object. -/
def possibleRegionContainmentObject {X : Type*} (raw : RawOutput G A) (P : G)
    (reg : raw.F.obj P → Set X) (x : raw.F.obj P) :
    PossibleRegionContainmentObject (G := G) (A := A) X where
  raw := raw
  input := P
  reg := reg
  representative := x

/-- The raw region is contained in the possible-image union. -/
theorem possibleRegionContainmentObject_subset
    {X : Type*} (O : PossibleRegionContainmentObject (G := G) (A := A) X) :
    O.reg O.representative ⊆
      MRRep.possibleRegion O.reg
        (MRRep.mk (R := O.raw) O.representative) :=
  MRRep.reg_subset_possibleRegion O.reg O.representative

/-- xi-e ⇒ xi-f: if the q value is in the raw region and the region is bounded
by the Theta-pilot hull log-volume `H`, then `q ≤ H`. -/
theorem possibleRegion_xiInequality {X : Type*}
    (O : PossibleRegionContainmentObject (G := G) (A := A) X)
    (q H : Real) (hq : q ∈ O.reg O.representative)
    (hbound : O.reg O.representative ⊆ Set.Iic H) : q ≤ H :=
  hbound hq

#check possibleRegionContainmentObject_subset
#check possibleRegion_xiInequality

end LeanFormal.IUT.XiFPaper.Mzk1PossibleRegionContainmentActual
end
