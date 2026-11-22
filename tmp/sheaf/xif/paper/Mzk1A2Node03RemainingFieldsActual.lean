/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03UniqueInvolutionActual
import tmp.sheaf.xif.paper.Mzk1A2Node03GroupsExtensionActual
import Mathlib.Tactic

/-! # A2 node03: remaining fields bundle -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03RemainingFieldsActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03UniqueInvolutionActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03GroupsExtensionActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- Remaining node03 fields for a fixed source: corrected unique involution
and groups/K-extension data. -/
structure A2Node03RemainingFieldsData (S : SourceSignQuotientData A) where
  uniqueInvolution : A2Node03UniqueInvolutionData (A := A) S.xF
  groupsExtension : A2Node03GroupsExtensionData (A := A) S.xF S.cF

def A2Node03RemainingFieldsData.correctedUnique
    {S : SourceSignQuotientData A}
    (D : A2Node03RemainingFieldsData S) :
    ∀ (inv : S.xF.Hom S.xF),
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id S.xF) →
      inv ≠ Iut.HyperbolicOrbicurve.Hom.id S.xF →
      inv = D.uniqueInvolution.ellipticInvolution :=
  D.uniqueInvolution.unique_nonidentity

def A2Node03RemainingFieldsRequired
    (S : SourceSignQuotientData A) : Prop :=
  Nonempty (A2Node03RemainingFieldsData S)

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03RemainingFieldsActual
