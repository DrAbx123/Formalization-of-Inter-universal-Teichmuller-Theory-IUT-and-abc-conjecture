/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03SourceSignQuotientAssemblyActual
import Mathlib.Tactic

/-! # A2 node03: consume assembly data into witness/source data -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03AssemblyConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceSignQuotientAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03SourceWitnessConsumerActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

def A2Node03SourceSignQuotientAssemblyData.toWitness
    {S : SourceSignQuotientData A}
    (D : A2Node03SourceSignQuotientAssemblyData S) :
    Iut.OrbicurveSignQuotientWitness S.signAction S.quotient :=
  D.producer.toWitness

noncomputable def A2Node03SourceSignQuotientAssemblyData.toSourceSignQuotientData
    {S : SourceSignQuotientData A}
    (D : A2Node03SourceSignQuotientAssemblyData S) :
    SourceSignQuotientData A :=
  sourceSignQuotientDataWithProducerWitness S D.producer

@[simp] theorem A2Node03SourceSignQuotientAssemblyData.toSourceSignQuotientData_xF
    {S : SourceSignQuotientData A}
    (D : A2Node03SourceSignQuotientAssemblyData S) :
    (A2Node03SourceSignQuotientAssemblyData.toSourceSignQuotientData D).xF = S.xF := rfl

theorem A2Node03SourceSignQuotientAssemblyData.nonempty_witness
    {S : SourceSignQuotientData A}
    (D : A2Node03SourceSignQuotientAssemblyData S) :
    Nonempty (Iut.OrbicurveSignQuotientWitness S.signAction S.quotient) :=
  ⟨A2Node03SourceSignQuotientAssemblyData.toWitness D⟩

theorem A2Node03SourceSignQuotientAssemblyRequired_iff
    (S : SourceSignQuotientData A) :
    A2Node03SourceSignQuotientAssemblyRequired S ↔
      Nonempty (A2Node03SourceSignQuotientAssemblyData S) := Iff.rfl

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03AssemblyConsumerActual
