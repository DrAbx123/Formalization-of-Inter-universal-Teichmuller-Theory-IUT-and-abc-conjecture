import Iut.Foundations.SourceModelFrobenioidAxioms
import tmp.sheaf.xif.paper.DvTriangleFieldCoversActual

/-! # Carrier FrobenioidPresentation and Example 3.2 exact missing data

SourceModelFrobenioid.Carrier.frobenioidAxioms already proves all Definition
1.3 axiom groups from Phi/data.  We package it into a FrobenioidPresentation.

For Example 3.2 on DvTriangleFieldCover K, the remaining exact missing data are
the size-aligned base category equivalence and the actual Phi/rational-function
/divisor data (q_v normalized valuation).  No fake Phi or presentation is
constructed for the field category. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.SourceModelCarrierFrobenioidPresentationActual

open CategoryTheory
open Iut
open Iut.SourceModelFrobenioid
open Iut.SourceModelFrobenioid.Carrier

universe u

variable {D : Type u} [Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : DivisorialMonoidOn D IsFSM}
variable {data : Input Phi}

/-- Actual Carrier FrobenioidPresentation from the model axioms. -/
noncomputable def carrierFrobenioidPresentation [IsConnected D]
    (baseTotallyEpimorphic : ∀ {X Y : D} (f : X ⟶ Y), Epi f) :
    FrobenioidPresentation where
  carrier := Cat.of (Carrier Phi data)
  baseCategory := Cat.of D
  isFSM := IsFSM
  preFrobenioid := preFrobenioid Phi data
  carrierConnected := isConnected Phi data
  baseConnected := (inferInstance : IsConnected D)
  carrierTotallyEpimorphic := fun {X Y : Carrier Phi data} (f : X ⟶ Y) =>
    @Iut.SourceModelFrobenioid.Carrier.epi D _ IsFSM Phi data baseTotallyEpimorphic X Y f
  baseTotallyEpimorphic := baseTotallyEpimorphic
  axioms := Iut.SourceModelFrobenioid.Carrier.frobenioidAxioms (Phi := Phi) (data := data) baseTotallyEpimorphic

variable (K : Type u) [Field K]

/-- Exact missing Example 3.2 data: size-aligned base category equivalent to
DvTriangleFieldCover K, plus Phi/rationalFunctions/divisor naturality and
base total epimorphicity. -/
structure Example32CarrierPresentationData (K : Type u) [Field K] where
  smallBase : Type u
  [categorySmallBase : Category.{u} smallBase]
  baseEquivalentToDvTriangle : Prop
  phi : Prop
  rationalFunctions : Prop
  divisor : Prop
  divisorNaturality : Prop
  baseTotallyEpimorphic : Prop

attribute [instance] Example32CarrierPresentationData.categorySmallBase

/-- Exact missing datum; no inhabitant is asserted. -/
def Example32CarrierPresentationDataRequired : Prop :=
  Nonempty (Example32CarrierPresentationData K)

end LeanFormal.IUT.XiFPaper.SourceModelCarrierFrobenioidPresentationActual

end
