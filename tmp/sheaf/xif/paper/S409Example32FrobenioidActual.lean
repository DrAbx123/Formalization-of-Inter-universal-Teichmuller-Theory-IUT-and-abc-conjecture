import tmp.sheaf.xif.paper.DvTriangleFieldCoversActual
import Iut.Foundations.SourceModelFrobenioidPresentation
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

/-!
# S409: Example 3.2 Frobenioid presentation — exact obstruction

The S398 candidate `DvTriangleFieldCover K` is an actual category of
connected finite etale `K`-algebras.  Two obstructions prevent a direct
`SourceModelFrobenioid.Carrier.frobenioidPresentation` call:

1. Universe/size mismatch: `DvTriangleFieldCover K` has objects in Type (u+1)
   and `Category.{u, u+1}` hom-types, while `DivisorialMonoidOn` requires
   `D : Type u` with `Category.{u}` (same universe for objects and morphisms).
2. The rational-function group, the divisor map `L^× → N · log(q_v)` built from
   `FinitePlaceQCandidate q_v`, and its naturality require a normalized
   valuation/ramification of q_v on each finite etale cover; the abstract
   finite etale algebras in the repo carry no such valued structure.

The paper base `B(K)^0` is also opposite to the algebra category, so a
size-aligned small model plus valuation data must be supplied.  No fake
Frobenioid presentation is constructed here.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S409Example32FrobenioidActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.DvTriangleFieldCoversActual

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- S398 algebra category. -/
abbrev Example32AlgebraBase : Type (u + 1) :=
  DvTriangleFieldCover K

/-- Paper base category `B(K)^0`: opposite of the algebra category. -/
abbrev Example32Base : Type (u + 1) :=
  (DvTriangleFieldCover K)ᵒᵖ

/-- Exact missing q_v valuation/ramification data needed for the divisor map
`L^× → N · log(q_v)` on every finite etale cover. -/
structure Example32QValDivisorData
    (place : NumberField.FinitePlace K) where
  q : FinitePlaceQCandidate place
  normalizedValuation : Prop
  ramificationNormalization : Prop
  divisorNaturality : Prop

def Example32QValDivisorDataRequired
    (place : NumberField.FinitePlace K) : Prop :=
  Nonempty (Example32QValDivisorData K place)

/-- Exact missing size-aligned model and rational-function/divisor data for an
actual Example 3.2 `FrobenioidPresentation`. -/
structure Example32FrobenioidPresentationData (K : Type u) [Field K] where
  smallBase : Type u
  [categorySmallBase : Category.{u} smallBase]
  baseEquivalence : Prop
  phi : Prop
  rationalFunctions : Prop
  divisor : Prop
  divisorNaturality : Prop
  baseTotallyEpimorphic : Prop

def Example32FrobenioidPresentationDataRequired : Prop :=
  Nonempty (Example32FrobenioidPresentationData K)

end LeanFormal.IUT.XiFPaper.S409Example32FrobenioidActual
end
