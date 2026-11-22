import tmp.sheaf.xif.paper.S2840A6ClauseAActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors
import tmp.sheaf.xif.paper.S2817ClauseDEFScaffold
import tmp.sheaf.xif.paper.S2823ClauseDConditionalActual
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2840A6ClauseAActual
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2823ClauseDConditionalActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2846A6ClauseBFAssembly

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- A6 ClauseA, conditional only on a sign-quotient record S. -/
noncomputable def S2846A6ClauseA
    (S : SourceSignQuotientData S2847A6) :
    SourceClauseA S2847A6 S :=
  S2840ClauseA S

/-- A6 ClauseB assembly from the three literal Clause-B fields, independent of
the qside file. -/
noncomputable def S2846A6ClauseB
    (S : SourceSignQuotientData S2847A6)
    (multiplicative : ∀ (p : NumberField.FinitePlace S2847A6.F),
      NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
        S2847A6.curve.HasMultiplicativeReductionAt p)
    (qWitness : ∀ (p : NumberField.FinitePlace S2847A6.F),
      (hp : NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad) →
        Nonempty (SourceTateComparisonWitness S2847A6 p))
    (residueCoprime : ∀ (p : NumberField.FinitePlace S2847A6.F),
      NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
        Nat.Coprime S2771FiveLabel.value
          (NumberFieldFinitePlace.residueCharacteristic
            (NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p))) :
    SourceClauseB S2847A6 S (S2846A6ClauseA S) :=
  SourceClauseB.ofTateComparisonWitnesses
    multiplicative qWitness residueCoprime

/-- A6 ClauseF assembly from the canonical BoundaryOrigin scaffold. -/
noncomputable def S2846A6ClauseF
    (S : SourceSignQuotientData S2847A6)
    (B : SourceClauseB S2847A6 S (S2846A6ClauseA S))
    (D : SourceClauseC S2847A6 S (S2846A6ClauseA S) B)
    (E : SourceClauseD S2847A6 S (S2846A6ClauseA S) B D)
    (L : SourceClauseE S2847A6 S (S2846A6ClauseA S) B D E)
    (W : S2817ClauseFScaffold (A := S2847A6) (S := S)
      (C := S2846A6ClauseA S) (B := B) (D := D) (E := E)) :
    SourceClauseF S2847A6 S (S2846A6ClauseA S) B D E L :=
  S2817ClauseF W

/-- Kernel-field identification for A6: K is definitionally the 5-torsion kernel field. -/
noncomputable def S2846A6KernelIdentification :
    S2847A6.K ≃ₐ[S2847A6.F]
      (S2847A6.curve).galoisLTorsionKernelField S2771FiveLabel S2847Basis :=
  AlgEquiv.refl

/-- The kernel identification has full range. -/
theorem S2846A6KernelIdentification_range :
    (Set.range fun x => (S2846A6KernelIdentification x :
      AlgebraicClosure S2847A6.F)) =
      ((S2847A6.curve).galoisLTorsionKernelField S2771FiveLabel S2847Basis :
        Set (AlgebraicClosure S2847A6.F)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact x.2
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩

/-- A6 ClauseC with actual torsion23 and kernel identification; image containment
is an explicit input. -/
noncomputable def S2846A6ClauseC
    (S : SourceSignQuotientData S2847A6)
    (B : SourceClauseB S2847A6 S (S2846A6ClauseA S))
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
        (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation
          S2771FiveLabel S2847A6.curve S2847Basis).range) :
    SourceClauseC S2847A6 S (S2846A6ClauseA S) B :=
  SourceClauseC.ofCanonicalRepresentation
    S2847_torsion23 S2847Basis imageContainsSL2
    S2846A6KernelIdentification S2846A6KernelIdentification_range

/-- A6 ClauseD from the 11 K-side/group witnesses. -/
noncomputable def S2846A6ClauseD
    (S : SourceSignQuotientData S2847A6)
    (B : SourceClauseB S2847A6 S (S2846A6ClauseA S))
    (C : SourceClauseC S2847A6 S (S2846A6ClauseA S) B)
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := S2847A6) (S := S)) :
    SourceClauseD S2847A6 S (S2846A6ClauseA S) B C :=
  S2823ClauseD kSide

/-- A6 ClauseE from the local-family unit. -/
noncomputable def S2846A6ClauseE
    (S : SourceSignQuotientData S2847A6)
    (B : SourceClauseB S2847A6 S (S2846A6ClauseA S))
    (C : SourceClauseC S2847A6 S (S2846A6ClauseA S) B)
    (D : SourceClauseD S2847A6 S (S2846A6ClauseA S) B C)
    (localFamily : SourceClauseELocalFamilyUnit S2847A6 S
      (S2846A6ClauseA S) B C D) :
    SourceClauseE S2847A6 S (S2846A6ClauseA S) B C D :=
  S2823ClauseE localFamily

/-- Full conditional A6 ClauseAssembly. -/
noncomputable def S2846A6ClauseAssembly
    (S : SourceSignQuotientData S2847A6)
    (multiplicative : ∀ (p : NumberField.FinitePlace S2847A6.F),
      NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
        S2847A6.curve.HasMultiplicativeReductionAt p)
    (qWitness : ∀ (p : NumberField.FinitePlace S2847A6.F),
      (hp : NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad) →
        Nonempty (SourceTateComparisonWitness S2847A6 p))
    (residueCoprime : ∀ (p : NumberField.FinitePlace S2847A6.F),
      NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
        Nat.Coprime S2771FiveLabel.value
          (NumberFieldFinitePlace.residueCharacteristic
            (NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p)))
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
        (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation
          S2771FiveLabel S2847A6.curve S2847Basis).range)
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := S2847A6) (S := S))
    (localFamily : SourceClauseELocalFamilyUnit S2847A6 S
      (S2846A6ClauseA S)
      (S2846A6ClauseB S multiplicative qWitness residueCoprime)
      (S2846A6ClauseC S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        imageContainsSL2)
      (S2846A6ClauseD S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        (S2846A6ClauseC S
          (S2846A6ClauseB S multiplicative qWitness residueCoprime)
          imageContainsSL2)
        kSide))
    (boundary : S2817ClauseFScaffold (l := S2771FiveLabel)
      (A := S2847A6) (S := S)
      (C := S2846A6ClauseA S)
      (B := S2846A6ClauseB S multiplicative qWitness residueCoprime)
      (D := S2846A6ClauseC S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        imageContainsSL2)
      (E := S2846A6ClauseD S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        (S2846A6ClauseC S
          (S2846A6ClauseB S multiplicative qWitness residueCoprime)
          imageContainsSL2)
        kSide)) :
    SourceClauseAssembly S2847A6 S where
  clauseA := S2846A6ClauseA S
  clauseB := S2846A6ClauseB S multiplicative qWitness residueCoprime
  clauseC := S2846A6ClauseC S
    (S2846A6ClauseB S multiplicative qWitness residueCoprime)
    imageContainsSL2
  clauseD := S2846A6ClauseD S
    (S2846A6ClauseB S multiplicative qWitness residueCoprime)
    (S2846A6ClauseC S
      (S2846A6ClauseB S multiplicative qWitness residueCoprime)
      imageContainsSL2)
    kSide
  clauseE := S2846A6ClauseE S
    (S2846A6ClauseB S multiplicative qWitness residueCoprime)
    (S2846A6ClauseC S
      (S2846A6ClauseB S multiplicative qWitness residueCoprime)
      imageContainsSL2)
    (S2846A6ClauseD S
      (S2846A6ClauseB S multiplicative qWitness residueCoprime)
      (S2846A6ClauseC S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        imageContainsSL2)
      kSide)
    localFamily
  clauseF := S2846A6ClauseF S
    (S2846A6ClauseB S multiplicative qWitness residueCoprime)
    (S2846A6ClauseC S
      (S2846A6ClauseB S multiplicative qWitness residueCoprime)
      imageContainsSL2)
    (S2846A6ClauseD S
      (S2846A6ClauseB S multiplicative qWitness residueCoprime)
      (S2846A6ClauseC S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        imageContainsSL2)
      kSide)
    (S2846A6ClauseE S
      (S2846A6ClauseB S multiplicative qWitness residueCoprime)
      (S2846A6ClauseC S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        imageContainsSL2)
      (S2846A6ClauseD S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        (S2846A6ClauseC S
          (S2846A6ClauseB S multiplicative qWitness residueCoprime)
          imageContainsSL2)
        kSide)
      localFamily)
    boundary

#check S2846A6ClauseA
#check S2846A6ClauseB
#check S2846A6ClauseF
#check S2846A6KernelIdentification
#check S2846A6KernelIdentification_range
#check S2846A6ClauseC
#check S2846A6ClauseD
#check S2846A6ClauseE
#check S2846A6ClauseAssembly
#print axioms S2846A6ClauseC
#print axioms S2846A6ClauseD
#print axioms S2846A6ClauseE
#print axioms S2846A6ClauseAssembly
#print axioms S2846A6ClauseA
#print axioms S2846A6ClauseB
#print axioms S2846A6ClauseF

end LeanFormal.IUT.XiFPaper.S2846A6ClauseBFAssembly
end