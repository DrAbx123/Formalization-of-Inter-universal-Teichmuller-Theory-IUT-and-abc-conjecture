/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03IntegrationActual
import Mathlib.Tactic

/-! # A2 node03: integration consumer lemmas -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03IntegrationConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03IntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03FullDataActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

@[simp] theorem A2Node03Interface.toSourceSignQuotientData_quotientWitness
    (D : A2Node03Interface A) :
    D.toSourceSignQuotientData.quotientWitness = D.toWitness := rfl

theorem A2Node03Interface.nonempty_witness (D : A2Node03Interface A) :
    Nonempty (Iut.OrbicurveSignQuotientWitness
      D.source.signAction D.source.quotient) :=
  ⟨D.toWitness⟩

theorem A2Node03Interface.exists_sourceSignQuotientData
    (D : A2Node03Interface A) :
    ∃ T : SourceSignQuotientData A,
      T.xF = D.source.xF ∧ T.cF = D.source.cF ∧
      T.V = D.full.vFields.V :=
  ⟨D.toSourceSignQuotientData, rfl, rfl, rfl⟩

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03IntegrationConsumerActual
