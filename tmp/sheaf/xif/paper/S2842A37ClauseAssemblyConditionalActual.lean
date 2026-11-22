import tmp.sheaf.xif.paper.S2836ClauseBCRebuildActual
import tmp.sheaf.xif.paper.S2823ClauseDConditionalActual
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31SignQuotientSupplyReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2836RebuildOnKernelArithmetic
open LeanFormal.IUT.XiFPaper.S2836ClauseBCRebuildActual
open LeanFormal.IUT.XiFPaper.S2823ClauseDConditionalActual
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2784KernelFieldActual
open LeanFormal.IUT.XiFPaper.S2834KernelFieldIdentificationActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2842A37ClauseAssemblyConditionalActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

noncomputable def S2842ClauseB
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
          (residueCharacteristic (comap (k := arithmetic37.Fmod) p))) :
    SourceClauseB arithmetic37 S (S2836ClauseA S) :=
  S2836ClauseB S (S2836ClauseA S) multiplicative qWitness residueCoprime

noncomputable def S2842ClauseC
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
      arithmetic37.curve S2771FiveLabel) :
    SourceClauseC arithmetic37 S (S2836ClauseA S)
      (S2842ClauseB S multiplicative qWitness residueCoprime) :=
  S2836ClauseC S (S2836ClauseA S)
    (S2842ClauseB S multiplicative qWitness residueCoprime)
    torsion23Rational hSerre

noncomputable def S2842ClauseD
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
      (A := arithmetic37) (S := S)) :
    SourceClauseD arithmetic37 S (S2836ClauseA S)
      (S2842ClauseB S multiplicative qWitness residueCoprime)
      (S2842ClauseC S multiplicative qWitness residueCoprime
        torsion23Rational hSerre) :=
  S2823ClauseD kSide

noncomputable def S2842ClauseE
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
        torsion23Rational hSerre kSide)) :
    SourceClauseE arithmetic37 S (S2836ClauseA S)
      (S2842ClauseB S multiplicative qWitness residueCoprime)
      (S2842ClauseC S multiplicative qWitness residueCoprime
        torsion23Rational hSerre)
      (S2842ClauseD S multiplicative qWitness residueCoprime
        torsion23Rational hSerre kSide) :=
  S2823ClauseE localFamily

noncomputable def S2842ClauseF
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
    SourceClauseF arithmetic37 S (S2836ClauseA S)
      (S2842ClauseB S multiplicative qWitness residueCoprime)
      (S2842ClauseC S multiplicative qWitness residueCoprime
        torsion23Rational hSerre)
      (S2842ClauseD S multiplicative qWitness residueCoprime
        torsion23Rational hSerre kSide)
      (S2842ClauseE S multiplicative qWitness residueCoprime
        torsion23Rational hSerre kSide localFamily) :=
  S2823ClauseF boundary

noncomputable def S2842ClauseAssembly
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
    SourceClauseAssembly arithmetic37 S where
  clauseA := S2836ClauseA S
  clauseB := S2842ClauseB S multiplicative qWitness residueCoprime
  clauseC := S2842ClauseC S multiplicative qWitness residueCoprime
    torsion23Rational hSerre
  clauseD := S2842ClauseD S multiplicative qWitness residueCoprime
    torsion23Rational hSerre kSide
  clauseE := S2842ClauseE S multiplicative qWitness residueCoprime
    torsion23Rational hSerre kSide localFamily
  clauseF := S2842ClauseF S multiplicative qWitness residueCoprime
    torsion23Rational hSerre kSide localFamily boundary

#check S2842ClauseAssembly
#print axioms S2842ClauseAssembly

end LeanFormal.IUT.XiFPaper.S2842A37ClauseAssemblyConditionalActual
end
