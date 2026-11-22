/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2GeometricCorePartialActual
import Mathlib.Tactic

/-! # A2 elliptic-involution candidates: identity endomorphism + exact gap

`Iut.HyperbolicOrbicurve.Hom.id` gives an actual endomorphism of the
degenerate `xF`; the squared-iso and uniqueness data are recorded as explicit
Prop gaps (no inhabitant).  The identity candidate is degenerate and is NOT
claimed to be the paper involution; it only shows which fields are free.
No fake. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1A2InvolutionCandidateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open Iut
open LeanFormal.IUT.XiFPaper.Mzk1A2GeometricCorePartialActual

variable {l : PrimeGeFive}

/-- Candidate `ellipticInvolution`: the identity endomorphism (degenerate). -/
noncomputable def a2EllipticInvolutionCandidate
    (A : InitialThetaArithmeticData.{0} l) :
    (xFOfStackPoint A).Hom (xFOfStackPoint A) :=
  HyperbolicOrbicurve.Hom.id (xFOfStackPoint A)

/-- Attempt: use `Iso.refl` for the squared coherence; succeeds only if
`comp id id` is definitionally `id`. -/
noncomputable def a2InvolutionSquaredCandidate
    (A : InitialThetaArithmeticData.{0} l) :
    HyperbolicOrbicurve.Hom.TwoIso
      (HyperbolicOrbicurve.Hom.comp (a2EllipticInvolutionCandidate A)
        (a2EllipticInvolutionCandidate A))
      (HyperbolicOrbicurve.Hom.id (xFOfStackPoint A)) :=
  CategoryTheory.Iso.refl _

/-- Exact gap 1: an invertible modification `edit ∘ edit ~ id`. -/
def a2InvolutionSquaredGap
    (A : InitialThetaArithmeticData.{0} l) : Prop :=
  Nonempty (HyperbolicOrbicurve.Hom.TwoIso
    (HyperbolicOrbicurve.Hom.comp (a2EllipticInvolutionCandidate A)
      (a2EllipticInvolutionCandidate A))
    (HyperbolicOrbicurve.Hom.id (xFOfStackPoint A)))

/-- Exact gap 2: uniqueness of an involution among endomorphisms. -/
def a2InvolutionUniquenessGap
    (A : InitialThetaArithmeticData.{0} l) : Prop :=
  ∀ inv : (xFOfStackPoint A).Hom (xFOfStackPoint A),
    Nonempty (HyperbolicOrbicurve.Hom.TwoIso
      (HyperbolicOrbicurve.Hom.comp inv inv)
      (HyperbolicOrbicurve.Hom.id (xFOfStackPoint A))) →
    inv = a2EllipticInvolutionCandidate A

def a2InvolutionRows : List (String × String × String) :=
  [ ("a2EllipticInvolutionCandidate", "Hom.id xF (degenerate identity candidate)", "DEFINED"),
    ("a2InvolutionSquaredGap", "TwoIso (id∘id) id", "EXPLICIT GAP, NO INHABITANT"),
    ("a2InvolutionUniquenessGap", "uniqueness of involution among endomorphisms", "EXPLICIT GAP, NO INHABITANT") ]

theorem a2InvolutionRows_length : a2InvolutionRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1A2InvolutionCandidateActual

end