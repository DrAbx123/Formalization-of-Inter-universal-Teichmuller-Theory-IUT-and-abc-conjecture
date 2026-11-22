/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03FullDataConsumerActual
import tmp.sheaf.xif.paper.Mzk1A2Node03RemainingFieldsActual
import Mathlib.Tactic

/-! # A2 node03 integration interface -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03IntegrationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03FullDataActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03RemainingFieldsActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- Integration of the accepted node03 components: full data plus the
remaining geometric fields, attached to the same source. -/
structure A2Node03Interface (A : InitialThetaArithmeticData l) where
  source : SourceSignQuotientData A
  full : A2Node03FullData source
  remaining : A2Node03RemainingFieldsData source

def A2Node03Interface.toWitness
    (D : A2Node03Interface A) :
    Iut.OrbicurveSignQuotientWitness D.source.signAction D.source.quotient :=
  D.full.toWitness

noncomputable def A2Node03Interface.toSourceSignQuotientData
    (D : A2Node03Interface A) :
    SourceSignQuotientData A :=
  D.full.toSourceSignQuotientData

def A2Node03InterfaceRequired : Prop := Nonempty (A2Node03Interface A)

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03IntegrationActual
