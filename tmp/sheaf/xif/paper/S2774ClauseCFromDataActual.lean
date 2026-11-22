import tmp.sheaf.xif.paper.S2771Gap1ClosedActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2774ClauseCFromDataActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual

/-- The rank-two 5-torsion basis supplied by S2771 for the actual curve of an
arithmetic root. -/
theorem S2774_fiveTorsionBasis_nonempty
    {l : PrimeGeFive} (A : InitialThetaArithmeticData l) [CharZero A.F] :
    Nonempty ((Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      A.curve.LTorsion S2771FiveLabel) :=
  S2771_rankTwoTorsionBasis A.curve

/-- Conditional SourceClauseC from explicit data: the large-image inclusion,
the torsion basis and the kernel-field identification (+range) are supplied;
the representation is the canonical Galois representation. -/
noncomputable def S2774_sourceClauseC
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    (torsion23Rational : A.curve.Torsion23Rational)
    (torsionBasis : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      A.curve.LTorsion l)
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
        (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation l A.curve
          torsionBasis).range)
    (kernelFieldIdentification :
      A.K ≃ₐ[A.F]
        (PuncturedEllipticCurve.galoisLTorsionKernelField l A.curve torsionBasis))
    (kernelFieldIdentificationRange :
      (Set.range fun x => (kernelFieldIdentification x :
        AlgebraicClosure A.F)) =
        (PuncturedEllipticCurve.galoisLTorsionKernelField l A.curve torsionBasis :
          Set (AlgebraicClosure A.F))) :
    SourceClauseC A S C B :=
  SourceClauseC.ofCanonicalRepresentation torsion23Rational torsionBasis
    imageContainsSL2 kernelFieldIdentification kernelFieldIdentificationRange

#check S2774_fiveTorsionBasis_nonempty
#check S2774_sourceClauseC
#print axioms S2774_fiveTorsionBasis_nonempty
#print axioms S2774_sourceClauseC

end LeanFormal.IUT.XiFPaper.S2774ClauseCFromDataActual
end
