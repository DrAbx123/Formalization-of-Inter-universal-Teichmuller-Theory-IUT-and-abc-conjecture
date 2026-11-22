import tmp.sheaf.xif.paper.S2846A6ClauseBFAssembly
import tmp.sheaf.xif.paper.S2774ClauseCFromDataActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2846A6ClauseBFAssembly
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2774ClauseCFromDataActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2846A6ClauseCDEAssembly

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

variable (S : SourceSignQuotientData S2847A6)
variable (multiplicative : ∀ (p : NumberField.FinitePlace S2847A6.F),
  NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
    S2847A6.curve.HasMultiplicativeReductionAt p)
variable (qWitness : ∀ (p : NumberField.FinitePlace S2847A6.F),
  (hp : NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad) →
    Nonempty (SourceTateComparisonWitness S2847A6 p))
variable (residueCoprime : ∀ (p : NumberField.FinitePlace S2847A6.F),
  NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
    Nat.Coprime S2771FiveLabel.value
      (NumberFieldFinitePlace.residueCharacteristic
        (NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p)))

/-- ClauseB for A6 with the three literal fields. -/
noncomputable def S2846A6B : SourceClauseB S2847A6 S (S2846A6ClauseA S) :=
  S2846A6ClauseB S multiplicative qWitness residueCoprime

/-- ClauseC for A6: kernel identification is definitional for S2847K; only
Serre large-image remains an explicit input. -/
noncomputable def S2846A6C
    (hSerre : InitialThetaSource.TorsionCarrierReduction.SerreStyleLargeImageStatement
      S2847A6.curve S2771FiveLabel) :
    SourceClauseC S2847A6 S (S2846A6ClauseA S) (S2846A6B S multiplicative qWitness residueCoprime) :=
  S2774_sourceClauseC
    (l := S2771FiveLabel) (A := S2847A6) (S := S)
    (C := S2846A6ClauseA S)
    (B := S2846A6B S multiplicative qWitness residueCoprime)
    S2847_torsion23 S2847Basis
    ((S1894GenImageTail_congr S2847A6.curve S2771FiveLabel
      S2847Basis hSerre.choose).mpr hSerre.choose_spec)
    (AlgEquiv.refl : S2847A6.K ≃ₐ[S2847A6.F]
      (PuncturedEllipticCurve.galoisLTorsionKernelField S2771FiveLabel
        S2847A6.curve S2847Basis))
    (by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩)

/-- ClauseD from the K-side scaffold. -/
noncomputable def S2846A6D
    (hSerre : InitialThetaSource.TorsionCarrierReduction.SerreStyleLargeImageStatement
      S2847A6.curve S2771FiveLabel)
    (W : S2817ClauseDScaffold (A := S2847A6) (S := S)) :
    SourceClauseD S2847A6 S (S2846A6ClauseA S)
      (S2846A6B S multiplicative qWitness residueCoprime)
      (S2846A6C S multiplicative qWitness residueCoprime hSerre) :=
  S2817ClauseD W

/-- ClauseE from the local-family scaffold. -/
noncomputable def S2846A6E
    (hSerre : InitialThetaSource.TorsionCarrierReduction.SerreStyleLargeImageStatement
      S2847A6.curve S2771FiveLabel)
    (W : S2817ClauseDScaffold (A := S2847A6) (S := S))
    (W' : S2817ClauseEScaffold (A := S2847A6) (S := S)
      (C := S2846A6ClauseA S)
      (B := S2846A6B S multiplicative qWitness residueCoprime)
      (D := S2846A6C S multiplicative qWitness residueCoprime hSerre)
      (E := S2846A6D S multiplicative qWitness residueCoprime hSerre W)) :
    SourceClauseE S2847A6 S (S2846A6ClauseA S)
      (S2846A6B S multiplicative qWitness residueCoprime)
      (S2846A6C S multiplicative qWitness residueCoprime hSerre)
      (S2846A6D S multiplicative qWitness residueCoprime hSerre W) :=
  S2817ClauseE W'

end LeanFormal.IUT.XiFPaper.S2846A6ClauseCDEAssembly
end