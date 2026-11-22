import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ConcreteFiniteRouteColumns
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteCertificateBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModelTransport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3128Cor312StepXIAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteFiniteStepXI

/-- Concrete Step-XI data assembled from the finite arithmetic route columns:
the finite APT/IPL/SHE/Ind3 units of
`ConcreteFiniteRouteColumns.lean` together with the finite arithmetic
certificate and its bridge to the Step-XI contract.  All inputs (`l`, `N`, the
processor labels `g`, `h`) are explicit; no IUT object is manufactured. -/
structure Cor312StepXIConcreteAssembly (l : PrimeGeFive) (N : Nat) where
  g : ConcreteFiniteTheorem311.finiteLabel l
  h : ConcreteFiniteTheorem311.finiteLabel l
  apt : FiniteAPTData l N
  ipl : FiniteIPLSquare l N
  she : FiniteSHESquare l N
  ind3 : FiniteInd3Certificate l N
  contract : StepXIContract
  contract_eq : contract =
    (finiteColumnArithmeticCertificate l N).toContract
      { targetSigned := (finiteColumnArithmeticCertificate l N).hull.hullVolume
        ipl := Nonempty (FiniteIPLSquare l N)
        she := Nonempty (FiniteSHESquare l N)
        apt := Nonempty (FiniteAPTData l N)
        ipl_evidence := ⟨ipl⟩
        she_evidence := ⟨she⟩
        apt_evidence := ⟨apt⟩
        q_le_target := (finiteColumnArithmeticCertificate l N).q_le_hull
        target_le_theta := (finiteColumnArithmeticCertificate l N).hull_le_theta }
  conclusion : Cor312Conclusion contract
  q_negative : contract.qSigned < 0

def cor312StepXIConcreteAssembly (l : PrimeGeFive) (N : Nat)
    (g h : ConcreteFiniteTheorem311.finiteLabel l) :
    Cor312StepXIConcreteAssembly l N :=
  let contract : StepXIContract :=
    (finiteColumnArithmeticCertificate l N).toContract
      { targetSigned := (finiteColumnArithmeticCertificate l N).hull.hullVolume
        ipl := Nonempty (FiniteIPLSquare l N)
        she := Nonempty (FiniteSHESquare l N)
        apt := Nonempty (FiniteAPTData l N)
        ipl_evidence := ⟨finiteIPLSquare l N g h⟩
        she_evidence := ⟨finiteSHESquare l N g⟩
        apt_evidence := ⟨finiteAPTData l N g⟩
        q_le_target := (finiteColumnArithmeticCertificate l N).q_le_hull
        target_le_theta := (finiteColumnArithmeticCertificate l N).hull_le_theta }
  { g := g
    h := h
    apt := finiteAPTData l N g
    ipl := finiteIPLSquare l N g h
    she := finiteSHESquare l N g
    ind3 := finiteInd3Certificate l N
    contract := contract
    contract_eq := rfl
    conclusion := cor312_of_finite_certificate
      (finiteColumnArithmeticCertificate l N)
      { targetSigned := (finiteColumnArithmeticCertificate l N).hull.hullVolume
        ipl := Nonempty (FiniteIPLSquare l N)
        she := Nonempty (FiniteSHESquare l N)
        apt := Nonempty (FiniteAPTData l N)
        ipl_evidence := ⟨finiteIPLSquare l N g h⟩
        she_evidence := ⟨finiteSHESquare l N g⟩
        apt_evidence := ⟨finiteAPTData l N g⟩
        q_le_target := (finiteColumnArithmeticCertificate l N).q_le_hull
        target_le_theta := (finiteColumnArithmeticCertificate l N).hull_le_theta }
    q_negative := (finiteColumnArithmeticCertificate l N).q_negative }

theorem cor312StepXIConcreteAssembly_nonempty (l : PrimeGeFive) (N : Nat)
    (g h : ConcreteFiniteTheorem311.finiteLabel l) :
    Nonempty (Cor312StepXIConcreteAssembly l N) :=
  ⟨cor312StepXIConcreteAssembly l N g h⟩

theorem cor312StepXIAssembly_conclusion (l : PrimeGeFive) (N : Nat)
    (g h : ConcreteFiniteTheorem311.finiteLabel l) :
    Cor312Conclusion (cor312StepXIConcreteAssembly l N g h).contract :=
  (cor312StepXIConcreteAssembly l N g h).conclusion

theorem cor312StepXIAssembly_q_positive (l : PrimeGeFive) (N : Nat)
    (g h : ConcreteFiniteTheorem311.finiteLabel l) :
    0 < -(cor312StepXIConcreteAssembly l N g h).contract.qSigned :=
  neg_pos.mpr (cor312StepXIConcreteAssembly l N g h).q_negative

theorem cor312StepXIAssembly_ind3_volume
    (l : PrimeGeFive) (N n : Nat)
    (x : FiniteColumnIndex l N) :
    columnLogVolume l x ≤
      columnLogVolume l ((finiteInd3Certificate l N).lift n x) :=
  (finiteInd3Certificate l N).volume_monotone n x

theorem cor312StepXIAssembly_apt_bijective
    (l : PrimeGeFive) (N : Nat)
    (g : ConcreteFiniteTheorem311.finiteLabel l) :
    Function.Bijective (finiteAPTData l N g).equivalence :=
  finiteAPTData_bijective l N g

#check cor312StepXIConcreteAssembly_nonempty
#check cor312StepXIAssembly_conclusion

end LeanFormal.IUT.XiFPaper.S3128Cor312StepXIAssemblyActual
end
