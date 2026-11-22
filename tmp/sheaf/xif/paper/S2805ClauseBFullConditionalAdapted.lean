import tmp.sheaf.xif.paper.S2787ClauseB37Actual
import tmp.sheaf.xif.paper.S2786SignQuotientActual
import tmp.sheaf.xif.paper.S2794Multiplicative37Actual
import tmp.sheaf.xif.paper.S2797ClauseA37ConditionalActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2787ClauseB37Actual
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2797ClauseA37ConditionalActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2805ClauseBFullConditionalAdapted

variable (S : SourceSignQuotientData S2786Arithmetic)
variable (C : SourceClauseA S2786Arithmetic S)

/-- Clause B data assembled only from the three S2787 fields: no hand-written
30-field record.  multiplicative / qWitness / residueCoprime are explicit
inputs; the first can be fed from S2794 at the two 37 places, the latter two
remain genuine source data. -/
noncomputable def S2805ClauseBData
    (multiplicative :
      ∀ p : NumberField.FinitePlace S2786Arithmetic.F,
        NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) p ∈ S.V_mod_bad →
        S2786Arithmetic.curve.HasMultiplicativeReductionAt p)
    (qWitness :
      ∀ (p : NumberField.FinitePlace S2786Arithmetic.F)
        (_hp : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) p ∈ S.V_mod_bad),
        Nonempty (SourceTateComparisonWitness S2786Arithmetic p))
    (residueCoprime :
      ∀ (p : NumberField.FinitePlace S2786Arithmetic.F)
        (_hp : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) p ∈ S.V_mod_bad),
        Nat.Coprime S2771FiveLabel.value
          (NumberFieldFinitePlace.residueCharacteristic
            (NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) p))) :
    S2787ClauseBData (l := S2771FiveLabel) S C where
  multiplicative := multiplicative
  qWitness := qWitness
  residueCoprime := residueCoprime

/-- Clause B from the explicit S2787 interface fields. -/
theorem S2805ClauseB
    (multiplicative :
      ∀ p : NumberField.FinitePlace S2786Arithmetic.F,
        NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) p ∈ S.V_mod_bad →
        S2786Arithmetic.curve.HasMultiplicativeReductionAt p)
    (qWitness :
      ∀ (p : NumberField.FinitePlace S2786Arithmetic.F)
        (_hp : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) p ∈ S.V_mod_bad),
        Nonempty (SourceTateComparisonWitness S2786Arithmetic p))
    (residueCoprime :
      ∀ (p : NumberField.FinitePlace S2786Arithmetic.F)
        (_hp : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) p ∈ S.V_mod_bad),
        Nat.Coprime S2771FiveLabel.value
          (NumberFieldFinitePlace.residueCharacteristic
            (NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) p))) :
    SourceClauseB S2786Arithmetic S C :=
  S2787ClauseB_of_data
    (S2805ClauseBData S C multiplicative qWitness residueCoprime)

#check S2805ClauseBData
#check S2805ClauseB
#print axioms S2805ClauseB

end LeanFormal.IUT.XiFPaper.S2805ClauseBFullConditionalAdapted
end
