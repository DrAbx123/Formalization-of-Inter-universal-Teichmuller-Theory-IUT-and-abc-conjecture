import tmp.sheaf.xif.paper.S2836RebuildOnKernelArithmetic
import tmp.sheaf.xif.paper.S2834KernelFieldIdentificationActual
import tmp.sheaf.xif.paper.S2835ImageContainsSL2Actual
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2836RebuildOnKernelArithmetic
open LeanFormal.IUT.XiFPaper.S2784KernelFieldActual
open LeanFormal.IUT.XiFPaper.S2834KernelFieldIdentificationActual
open LeanFormal.IUT.XiFPaper.S2835ImageContainsSL2Actual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2836ClauseBCRebuildActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- ClauseB on arithmetic37 from explicit multiplicative, q-witness and
residue-coprime inputs. -/
noncomputable def S2836ClauseB
    (S : SourceSignQuotientData arithmetic37)
    (C : SourceClauseA arithmetic37 S)
    (multiplicative : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad →
        arithmetic37.curve.HasMultiplicativeReductionAt p)
    (qWitness : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      (hp : comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad) →
        Nonempty (SourceTateComparisonWitness arithmetic37 p))
    (residueCoprime : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad →
        Nat.Coprime S2771FiveLabel.value
          (residueCharacteristic
            (comap (k := arithmetic37.Fmod) p))) :
    SourceClauseB arithmetic37 S C :=
  SourceClauseB.ofTateComparisonWitnesses multiplicative qWitness residueCoprime

/-- ClauseC on arithmetic37 with basis37 and the S2834 kernel identification;
torsion23 rationality and image containment remain explicit. -/
noncomputable def S2836ClauseC
    (S : SourceSignQuotientData arithmetic37)
    (C : SourceClauseA arithmetic37 S)
    (B : SourceClauseB arithmetic37 S C)
    (torsion23Rational : arithmetic37.curve.Torsion23Rational)
    (hSerre : InitialThetaSource.TorsionCarrierReduction.SerreStyleLargeImageStatement
      arithmetic37.curve S2771FiveLabel) :
    SourceClauseC arithmetic37 S C B := by
  have hImage :
      Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
        (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation
          S2771FiveLabel arithmetic37.curve basis37).range := by
    exact S2835_imageContainsSL2_of_serre_at_basis hSerre
  exact SourceClauseC.ofCanonicalRepresentation
    torsion23Rational basis37 hImage
    S2834KernelFieldIdentification
    S2834KernelFieldIdentification_range

#check S2836ClauseB
#check S2836ClauseC
#print axioms S2836ClauseB
#print axioms S2836ClauseC

end LeanFormal.IUT.XiFPaper.S2836ClauseBCRebuildActual
end
