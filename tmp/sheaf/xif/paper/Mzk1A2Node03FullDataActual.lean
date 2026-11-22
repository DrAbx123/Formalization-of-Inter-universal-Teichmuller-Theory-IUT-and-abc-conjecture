/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03SourceSignQuotientAssemblyActual
import tmp.sheaf.xif.paper.Mzk1A2Node03VFieldsConsumerActual
import Mathlib.Tactic

/-! # A2 node03: full data bundle -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03FullDataActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceSignQuotientAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03VFieldsConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceVFieldsActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceWitnessConsumerActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

structure A2Node03FullData (S : SourceSignQuotientData A) where
  assembly : A2Node03SourceSignQuotientAssemblyData S
  vFields : A2Node03SourceVFieldsData S

noncomputable def A2Node03FullData.toSourceSignQuotientData
    {S : SourceSignQuotientData A}
    (D : A2Node03FullData S) :
    SourceSignQuotientData A :=
  sourceSignQuotientDataWithProducerWitness
    (sourceSignQuotientDataWithVFields S D.vFields) D.assembly.producer

def A2Node03FullData.toWitness
    {S : SourceSignQuotientData A}
    (D : A2Node03FullData S) :
    Iut.OrbicurveSignQuotientWitness S.signAction S.quotient :=
  D.assembly.producer.toWitness

@[simp] theorem A2Node03FullData.toSourceSignQuotientData_V
    {S : SourceSignQuotientData A}
    (D : A2Node03FullData S) :
    D.toSourceSignQuotientData.V = D.vFields.V := rfl

def A2Node03FullDataRequired
    (S : SourceSignQuotientData A) : Prop :=
  Nonempty (A2Node03FullData S)

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03FullDataActual
