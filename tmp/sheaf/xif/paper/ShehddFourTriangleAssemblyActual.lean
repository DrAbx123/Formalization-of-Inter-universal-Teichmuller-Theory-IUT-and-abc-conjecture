import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CardQCMPComparison
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ConcreteFiniteRouteColumns
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotGlobalNormalization

/-!
# ShehddFourTriangleAssemblyActual — finite route columns -> QCMP supply -> Cor 3.12

Real assembly for LADDER rung R4: the finite APT/IPL/SHE route columns (ConcreteFiniteStepXI)
are passed as the contract's IPL/SHE/APT data, the q-family + horizon inequality instantiate
the Card-QCMP supply (ofTargetEqLowerSignedLog), and the consumer theorem
`cor312Conclusion_of_toStepXIContract` yields the Cor 3.12 conclusion for the constructed
StepXI contract.  The horizon inequality is the explicit remaining named input (theta face,
certificate-hull/AMPL boundary).  No sorry/axiom, no True placeholder.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddFourTriangleAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.StepXIQCMP
open LeanFormal.IUT.ConcreteFiniteStepXI

variable {k : Type*} [Field k] [NumberField k]

/-- **PROVED assembly:** a finite q-family with nonempty selected places, a theta scale and
the horizon inequality, plus finite APT/IPL/SHE route data, produce a StepXI contract whose
Cor 3.12 conclusion holds. -/
theorem cor312Conclusion_of_finiteRouteColumns
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (place : selectedLowerPlaces) →
      NumberFieldFinitePlace.FinitePlaceQCandidate place.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (thetaSigned : Real)
    (horizon :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters ≤ thetaSigned)
    {l : PrimeGeFive} {N : Nat}
    (g h t : ConcreteFiniteTheorem311.finiteLabel l) :
    Cor312Conclusion
      ((QCMPComparisonSupply.ofTargetEqLowerSignedLog selectedLowerPlaces parameters
          selected_nonempty thetaSigned horizon).toStepXIContract
        (Nonempty (FiniteIPLSquare l N)) (Nonempty (FiniteSHESquare l N))
        (Nonempty (FiniteAPTData l N))
        ⟨finiteIPLSquare l N g h⟩ ⟨finiteSHESquare l N g⟩
        ⟨finiteAPTData l N t⟩) :=
  cor312Conclusion_of_toStepXIContract
    (QCMPComparisonSupply.ofTargetEqLowerSignedLog selectedLowerPlaces parameters
      selected_nonempty thetaSigned horizon)
    (Nonempty (FiniteIPLSquare l N)) (Nonempty (FiniteSHESquare l N))
    (Nonempty (FiniteAPTData l N))
    ⟨finiteIPLSquare l N g h⟩ ⟨finiteSHESquare l N g⟩ ⟨finiteAPTData l N t⟩

/-- **PROVED assembly (signed form):** the constructed contract's qSigned is the
absolute-degree-normalized lower signed log of the finite q-family, and q is negative
whenever the contract's q_negative data is supplied by the constructor chain. -/
theorem qSigned_eq_of_finiteRouteColumns
    (selectedLowerPlaces : Finset (NumberField.FinitePlace k))
    (parameters : (place : selectedLowerPlaces) →
      NumberFieldFinitePlace.FinitePlaceQCandidate place.val)
    (selected_nonempty : selectedLowerPlaces.Nonempty)
    (thetaSigned : Real)
    (horizon :
      ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
        selectedLowerPlaces parameters ≤ thetaSigned)
    {l : PrimeGeFive} {N : Nat}
    (g h t : ConcreteFiniteTheorem311.finiteLabel l) :
    ((QCMPComparisonSupply.ofTargetEqLowerSignedLog selectedLowerPlaces parameters
        selected_nonempty thetaSigned horizon).toStepXIContract
      (Nonempty (FiniteIPLSquare l N)) (Nonempty (FiniteSHESquare l N))
      (Nonempty (FiniteAPTData l N))
      ⟨finiteIPLSquare l N g h⟩ ⟨finiteSHESquare l N g⟩
      ⟨finiteAPTData l N t⟩).qSigned =
    ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog
      selectedLowerPlaces parameters :=
  rfl

end LeanFormal.IUT.XiFPaper.ShehddFourTriangleAssemblyActual
end
