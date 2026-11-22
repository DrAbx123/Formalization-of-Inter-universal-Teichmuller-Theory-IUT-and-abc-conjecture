/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Iut.Foundations.Orbicurve
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import tmp.sheaf.xif.paper.Mzk1A2InvolutionCandidateActual
import Mathlib.Tactic

/-! # A2 sign action: explicit degenerate `OrbicurveSignAction` construction

For any hyperbolic orbicurve `X` we build the degenerate sign action:
* the constant pseudofunctor `SignActionIndex ⥤ᵖ EtaleStackPseudofunctor F`
  (`obj` constant at `X.stack.fiber`, all maps identities);
* `atBase` the identity bicategory equivalence;
* `inversion` the identity endomorphism and
* coherences from the bicategory unitors (`rightUnitor`/`leftUnitor`).

For the degenerate `xFOfStackPoint A` this yields the `signAction` field of
`SourceSignQuotientData` and the equality
`signAction.inversion = ellipticInvolution` with the involution candidate.
This is a DEGENERATE construction (identity action), not the paper geometry;
quotient witness / groups / scalar extension remain open.  No fake. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open CategoryTheory Bicategory
open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace LeanFormal.IUT.XiFPaper.Mzk1A2SignActionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2GeometricCorePartialActual
open LeanFormal.IUT.XiFPaper.Mzk1A2InvolutionCandidateActual
open Iut

variable {F : Type} [Field F]

/-- Constant pseudofunctor into the etale-stack bicategory. -/
noncomputable def constantDiagram (X : Iut.HyperbolicOrbicurve F) :
    Pseudofunctor Iut.SignActionIndex (Iut.EtaleStackPseudofunctor F) where
  obj := fun _ => X.stack.fiber
  map := fun _ => 𝟙 X.stack.fiber
  map₂ := fun _ => 𝟙 _
  mapId := fun _ => Iso.refl _
  mapComp := fun _ _ => (ρ_ (𝟙 X.stack.fiber)).symm

/-- Identity bicategory equivalence onto the constant diagram value. -/
noncomputable def atBaseCandidate (X : Iut.HyperbolicOrbicurve F) :
    Bicategory.Equivalence
      ((constantDiagram X).obj Iut.signActionObject) X.stack.fiber :=
  Bicategory.Equivalence.id _

/-- Degenerate `OrbicurveSignAction` for any hyperbolic orbicurve. -/
noncomputable def signActionCandidate (X : Iut.HyperbolicOrbicurve F) :
    Iut.OrbicurveSignAction X where
  diagram := constantDiagram X
  atBase := atBaseCandidate X
  inversion := Iut.HyperbolicOrbicurve.Hom.id X
  generator_identification :=
    Pseudofunctor.StrongTrans.rightUnitor (𝟙 X.stack.fiber ≫ 𝟙 X.stack.fiber) ≪≫
      Pseudofunctor.StrongTrans.leftUnitor (𝟙 X.stack.fiber)
  inversionSquared := Pseudofunctor.StrongTrans.leftUnitor (𝟙 X.stack.fiber)

variable {l : PrimeGeFive}

/-- The degenerate sign action on the stack-point orbicurve. -/
noncomputable def signActionOfStackPoint (A : InitialThetaArithmeticData.{0} l) :
    Iut.OrbicurveSignAction (xFOfStackPoint A) :=
  signActionCandidate (xFOfStackPoint A)

/-- Its inversion is the involution candidate. -/
theorem signActionOfStackPoint_inversion_eq (A : InitialThetaArithmeticData.{0} l) :
    (signActionOfStackPoint A).inversion = a2EllipticInvolutionCandidate A := rfl

def signActionRows : List (String × String × String) :=
  [ ("constantDiagram", "constant pseudofunctor SignActionIndex -> EtaleStackPseudofunctor F", "CONSTRUCTED (degenerate)"),
    ("atBaseCandidate", "Bicategory.Equivalence.id onto the constant diagram value", "CONSTRUCTED"),
    ("signActionCandidate", "OrbicurveSignAction via identity inversion + unitor coherences", "CONSTRUCTED (degenerate)"),
    ("signActionOfStackPoint_inversion_eq", "signAction.inversion = ellipticInvolution candidate", "PROVED (rfl)"),
    ("quotientWitness", "OrbicurveSignQuotientWitness universal property", "EXPLICIT REMAINING GAP"),
    ("groups", "OrbicurveFundamentalGroupData / OrbicurveEtaleFundamentalGroup", "EXPLICIT REMAINING GAP"),
    ("scalar stackExtension", "SourceEtaleStackScalarExtension actual result stack", "EXPLICIT REMAINING GAP") ]

theorem signActionRows_length : signActionRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1A2SignActionActual

end