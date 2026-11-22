import tmp.sheaf.xif.paper.S2842A37ClauseAssemblyConditionalActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2784KernelFieldActual
open LeanFormal.IUT.XiFPaper.S2836RebuildOnKernelArithmetic
open LeanFormal.IUT.XiFPaper.S2842A37ClauseAssemblyConditionalActual
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2843A37SourceCompletionConditionalActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- A37 source witness from the S2842 conditional clause assembly. -/
noncomputable def S2843Witness
    (S : SourceSignQuotientData arithmetic37)
    (multiplicative : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad →
        arithmetic37.curve.HasMultiplicativeReductionAt p)
    (qWitness : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      (hp : comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad) →
        Nonempty (SourceTateComparisonWitness arithmetic37 p))
    (residueCoprime : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad →
        Nat.Coprime S2771FiveLabel.value
          (residueCharacteristic (comap (k := arithmetic37.Fmod) p)))
    (torsion23Rational : arithmetic37.curve.Torsion23Rational)
    (hSerre : InitialThetaSource.TorsionCarrierReduction.SerreStyleLargeImageStatement
      arithmetic37.curve S2771FiveLabel)
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := arithmetic37) (S := S))
    (localFamily : SourceClauseELocalFamilyUnit arithmetic37 S
      (S2836ClauseA S)
      (S2842ClauseB S multiplicative qWitness residueCoprime)
      (S2842ClauseC S multiplicative qWitness residueCoprime
        torsion23Rational hSerre)
      (S2842ClauseD S multiplicative qWitness residueCoprime
        torsion23Rational hSerre kSide))
    (boundary : SourceClauseFBoundaryUnit arithmetic37 S
      (S2836ClauseA S)
      (S2842ClauseB S multiplicative qWitness residueCoprime)
      (S2842ClauseC S multiplicative qWitness residueCoprime
        torsion23Rational hSerre)
      (S2842ClauseD S multiplicative qWitness residueCoprime
        torsion23Rational hSerre kSide)
      (S2842ClauseE S multiplicative qWitness residueCoprime
        torsion23Rational hSerre kSide localFamily)) :
    SourceClauseConstructionWitness S2771FiveLabel :=
  witnessOfClauseAssembly arithmetic37 S
    (S2842ClauseAssembly S multiplicative qWitness residueCoprime
      torsion23Rational hSerre kSide localFamily boundary)

/-- A37 native initial Theta data from the conditional witness. -/
noncomputable def S2843NativeData
    (S : SourceSignQuotientData arithmetic37)
    (multiplicative : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad →
        arithmetic37.curve.HasMultiplicativeReductionAt p)
    (qWitness : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      (hp : comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad) →
        Nonempty (SourceTateComparisonWitness arithmetic37 p))
    (residueCoprime : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad →
        Nat.Coprime S2771FiveLabel.value
          (residueCharacteristic (comap (k := arithmetic37.Fmod) p)))
    (torsion23Rational : arithmetic37.curve.Torsion23Rational)
    (hSerre : InitialThetaSource.TorsionCarrierReduction.SerreStyleLargeImageStatement
      arithmetic37.curve S2771FiveLabel)
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := arithmetic37) (S := S))
    (localFamily : SourceClauseELocalFamilyUnit arithmetic37 S
      (S2836ClauseA S)
      (S2842ClauseB S multiplicative qWitness residueCoprime)
      (S2842ClauseC S multiplicative qWitness residueCoprime
        torsion23Rational hSerre)
      (S2842ClauseD S multiplicative qWitness residueCoprime
        torsion23Rational hSerre kSide))
    (boundary : SourceClauseFBoundaryUnit arithmetic37 S
      (S2836ClauseA S)
      (S2842ClauseB S multiplicative qWitness residueCoprime)
      (S2842ClauseC S multiplicative qWitness residueCoprime
        torsion23Rational hSerre)
      (S2842ClauseD S multiplicative qWitness residueCoprime
        torsion23Rational hSerre kSide)
      (S2842ClauseE S multiplicative qWitness residueCoprime
        torsion23Rational hSerre kSide localFamily)) :
    SourceNativeInitialThetaData S2771FiveLabel :=
  SourceClauseConstructionWitness.sourceData
    (S2843Witness S multiplicative qWitness residueCoprime
      torsion23Rational hSerre kSide localFamily boundary)

/-- A37 SourceCompletion from the conditional native data. -/
noncomputable def S2843Completion
    (S : SourceSignQuotientData arithmetic37)
    (multiplicative : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad →
        arithmetic37.curve.HasMultiplicativeReductionAt p)
    (qWitness : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      (hp : comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad) →
        Nonempty (SourceTateComparisonWitness arithmetic37 p))
    (residueCoprime : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad →
        Nat.Coprime S2771FiveLabel.value
          (residueCharacteristic (comap (k := arithmetic37.Fmod) p)))
    (torsion23Rational : arithmetic37.curve.Torsion23Rational)
    (hSerre : InitialThetaSource.TorsionCarrierReduction.SerreStyleLargeImageStatement
      arithmetic37.curve S2771FiveLabel)
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := arithmetic37) (S := S))
    (localFamily : SourceClauseELocalFamilyUnit arithmetic37 S
      (S2836ClauseA S)
      (S2842ClauseB S multiplicative qWitness residueCoprime)
      (S2842ClauseC S multiplicative qWitness residueCoprime
        torsion23Rational hSerre)
      (S2842ClauseD S multiplicative qWitness residueCoprime
        torsion23Rational hSerre kSide))
    (boundary : SourceClauseFBoundaryUnit arithmetic37 S
      (S2836ClauseA S)
      (S2842ClauseB S multiplicative qWitness residueCoprime)
      (S2842ClauseC S multiplicative qWitness residueCoprime
        torsion23Rational hSerre)
      (S2842ClauseD S multiplicative qWitness residueCoprime
        torsion23Rational hSerre kSide)
      (S2842ClauseE S multiplicative qWitness residueCoprime
        torsion23Rational hSerre kSide localFamily)) :
    SourceCompletion S2771FiveLabel :=
  SourceCompletion.ofSourceNative
    (S2843NativeData S multiplicative qWitness residueCoprime
      torsion23Rational hSerre kSide localFamily boundary)

#check S2843Witness
#check S2843NativeData
#check S2843Completion
#print axioms S2843Witness
#print axioms S2843NativeData
#print axioms S2843Completion

end LeanFormal.IUT.XiFPaper.S2843A37SourceCompletionConditionalActual
end
