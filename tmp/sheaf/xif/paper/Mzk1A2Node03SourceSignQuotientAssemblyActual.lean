/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03SourceWitnessConsumerActual
import tmp.sheaf.xif.paper.Mzk1A2Node03GroupsExtensionActual
import Mathlib.Tactic

/-! # A2 node03: exact assembly interface for SourceSignQuotientData -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceSignQuotientAssemblyActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03QuotientStackProducerActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03GroupsExtensionActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- Exact data still needed to assemble a `SourceSignQuotientData`: the
quotient-stack producer and the groups/extension package, attached to the
same source.  No witness is supplied here. -/
structure A2Node03SourceSignQuotientAssemblyData
    (S : SourceSignQuotientData A) where
  producer : A2QuotientStackProducerData S.signAction S.quotient
  groups : A2Node03GroupsExtensionData (A := A) S.xF S.cF

def A2Node03SourceSignQuotientAssemblyRequired
    (S : SourceSignQuotientData A) : Prop :=
  Nonempty (A2Node03SourceSignQuotientAssemblyData S)

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceSignQuotientAssemblyActual
