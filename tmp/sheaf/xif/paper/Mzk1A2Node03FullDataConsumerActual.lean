/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A2Node03FullDataActual
import Mathlib.Tactic

/-! # A2 node03: full data consumer lemmas -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1A2Node03FullDataConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1A2Node03FullDataActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

@[simp] theorem A2Node03FullData.toSourceSignQuotientData_quotientWitness
    {S : SourceSignQuotientData A}
    (D : A2Node03FullData S) :
    D.toSourceSignQuotientData.quotientWitness = D.toWitness := rfl

@[simp] theorem A2Node03FullData.toSourceSignQuotientData_xF
    {S : SourceSignQuotientData A}
    (D : A2Node03FullData S) :
    D.toSourceSignQuotientData.xF = S.xF := rfl

@[simp] theorem A2Node03FullData.toSourceSignQuotientData_cF
    {S : SourceSignQuotientData A}
    (D : A2Node03FullData S) :
    D.toSourceSignQuotientData.cF = S.cF := rfl

theorem A2Node03FullData.exists_sourceSignQuotientData
    {S : SourceSignQuotientData A}
    (D : A2Node03FullData S) :
    ∃ T : SourceSignQuotientData A,
      T.xF = S.xF ∧ T.cF = S.cF ∧
      T.V = D.vFields.V :=
  ⟨D.toSourceSignQuotientData, rfl, rfl, rfl⟩

end LeanFormal.IUT.XiFPaper.Mzk1A2Node03FullDataConsumerActual
