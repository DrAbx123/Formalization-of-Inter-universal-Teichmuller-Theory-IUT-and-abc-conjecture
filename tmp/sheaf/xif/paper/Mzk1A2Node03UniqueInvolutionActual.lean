/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03AssemblyConsumerActual
import Mathlib.Tactic

/-! # A2 node03: corrected unique-elliptic-involution field interface -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03UniqueInvolutionActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

variable {A : InitialThetaArithmeticData l}

/-- Corrected uniqueness statement: uniqueness only among non-identity
involutions, avoiding the `inv = id` counterexample from the original
`∀ inv, inv² ≃ id → inv = ellipticInvolution`. -/
structure A2Node03UniqueInvolutionData
    (xF : Iut.HyperbolicOrbicurve A.F) where
  ellipticInvolution : xF.Hom xF
  ellipticInvolution_squared :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp ellipticInvolution ellipticInvolution)
      (Iut.HyperbolicOrbicurve.Hom.id xF)
  unique_nonidentity :
    ∀ (inv : xF.Hom xF),
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id xF) →
      inv ≠ Iut.HyperbolicOrbicurve.Hom.id xF → inv = ellipticInvolution

def A2Node03UniqueInvolutionRequired
    (xF : Iut.HyperbolicOrbicurve A.F) : Prop :=
  Nonempty (A2Node03UniqueInvolutionData (A := A) xF)

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03UniqueInvolutionActual
