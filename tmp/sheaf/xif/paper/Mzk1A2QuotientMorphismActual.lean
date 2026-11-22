/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2InvolutionCandidateActual
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.Tactic

/-! # A2 quotient morphism: simplified sign action + invariant morphism

For the degenerate stack-point xF the sign action can be chosen with
inversionSquared := Iso.refl (since comp id id is definitionally id for the
point stack).  Then the sign-invariant morphism xF -> xF is the identity map
with invariant := Iso.refl, and its cocycle is rfl.

This closes the quotient field of SourceSignQuotientData (degenerate); the
quotientWitness universal property remains an explicit gap.  No fake. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open CategoryTheory Bicategory
open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace LeanFormal.IUT.XiFPaper.Mzk1A2QuotientMorphismActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2GeometricCorePartialActual
open LeanFormal.IUT.XiFPaper.Mzk1A2InvolutionCandidateActual
open Iut

variable {F : Type} [Field F]

noncomputable def constantDiagram (X : Iut.HyperbolicOrbicurve F) :
    Pseudofunctor Iut.SignActionIndex (Iut.EtaleStackPseudofunctor F) where
  obj := fun _ => X.stack.fiber
  map := fun _ => 𝟙 X.stack.fiber
  map₂ := fun _ => 𝟙 _
  mapId := fun _ => Iso.refl _
  mapComp := fun _ _ => (ρ_ (𝟙 X.stack.fiber)).symm

noncomputable def atBaseCandidate (X : Iut.HyperbolicOrbicurve F) :
    Bicategory.Equivalence ((constantDiagram X).obj Iut.signActionObject) X.stack.fiber :=
  Bicategory.Equivalence.id _

variable {l : PrimeGeFive}

noncomputable def signActionSimplified (A : InitialThetaArithmeticData.{0} l) :
    Iut.OrbicurveSignAction (xFOfStackPoint A) where
  diagram := constantDiagram (xFOfStackPoint A)
  atBase := atBaseCandidate (xFOfStackPoint A)
  inversion := Iut.HyperbolicOrbicurve.Hom.id (xFOfStackPoint A)
  generator_identification :=
    Pseudofunctor.StrongTrans.rightUnitor
        (𝟙 (xFOfStackPoint A).stack.fiber ≫ 𝟙 (xFOfStackPoint A).stack.fiber) ≪≫
      Pseudofunctor.StrongTrans.leftUnitor (𝟙 (xFOfStackPoint A).stack.fiber)
  inversionSquared := CategoryTheory.Iso.refl _

noncomputable def quotientMorphismSimplified (A : InitialThetaArithmeticData.{0} l) :
    Iut.OrbicurveSignInvariantMorphism (signActionSimplified A) (xFOfStackPoint A) where
  map := Iut.HyperbolicOrbicurve.Hom.id (xFOfStackPoint A)
  invariant := CategoryTheory.Iso.refl _
  cocycle := by rfl

def quotientRows : List (String × String × String) :=
  [ ("signActionSimplified", "sign action with inversionSquared := Iso.refl", "CONSTRUCTED (degenerate)"),
    ("quotientMorphismSimplified", "sign-invariant morphism identity, cocycle := rfl", "CONSTRUCTED (degenerate)"),
    ("quotientWitness", "OrbicurveSignQuotientWitness universal property", "EXPLICIT REMAINING GAP"),
    ("groups", "OrbicurveFundamentalGroupData / EtaleFundamentalGroup", "EXPLICIT REMAINING GAP"),
    ("unique_elliptic_involution", "Subsingleton (xF.Hom xF) / classification", "EXPLICIT REMAINING GAP") ]

theorem quotientRows_length : quotientRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1A2QuotientMorphismActual

end