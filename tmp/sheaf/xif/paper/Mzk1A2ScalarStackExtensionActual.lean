/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Iut.Foundations.Orbicurve
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceEtaleStackInstanceSupplyReduction
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.Tactic

/-! # A2 scalar stack extension: the point-stack case

For the constant one-point etale stack, scalar extension from F to K is
free: the base-changed point stack is definitionally the point stack over K,
so SourceEtaleStackScalarExtension is inhabited with
fiberEquivalence := Bicategory.Equivalence.id _.

Degenerate (point-stack) construction only.  No fake. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open CategoryTheory Bicategory
open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace LeanFormal.IUT.XiFPaper.Mzk1A2ScalarStackExtensionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open Iut

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The constant one-point etale stack as an EtaleStackOverField. -/
noncomputable def pointStack (F : Type) [Field F] : EtaleStackOverField F :=
  { fiber := sourceStackPointEtaleFiber F
    isStack := sourceStackPointEtaleFiber_isStack F }

/-- Scalar stack extension of the point stack (degenerate but actual). -/
noncomputable def pointStackScalarExtension :
    SourceEtaleStackScalarExtension F K (pointStack F) where
  result := pointStack K
  fiberEquivalence := Bicategory.Equivalence.id _

def scalarStackRows : List (String × String × String) :=
  [ ("pointStack", "constant one-point etale stack as EtaleStackOverField", "CONSTRUCTED"),
    ("pointStackScalarExtension", "SourceEtaleStackScalarExtension F K (pointStack F)", "CONSTRUCTED (degenerate)"),
    ("quotientWitness", "OrbicurveSignQuotientWitness universal property", "EXPLICIT REMAINING GAP"),
    ("groups", "OrbicurveFundamentalGroupData / OrbicurveEtaleFundamentalGroup", "EXPLICIT REMAINING GAP"),
    ("unique_elliptic_involution", "Subsingleton (xF.Hom xF) / classification", "EXPLICIT REMAINING GAP") ]

theorem scalarStackRows_length : scalarStackRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1A2ScalarStackExtensionActual

end