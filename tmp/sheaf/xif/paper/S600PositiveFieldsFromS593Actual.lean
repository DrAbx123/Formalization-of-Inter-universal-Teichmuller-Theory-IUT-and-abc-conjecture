import tmp.sheaf.xif.paper.S593PositivePreimageQvOrderActual
import tmp.sheaf.xif.paper.S576PositiveQvPhiQOrderFieldsActual

/-! # S600: S576 QvPhiQOrderFields and tau directly from S593

Uses S593.positiveQvPhiPreimageAtQvOrder to fill QvPhiQOrderFields directly
(bypassing the S567 preimage interface), then builds tau as natural powers.
No fake fields or tau. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S600PositiveFieldsFromS593Actual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S576PositiveQvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S593PositivePreimageQvOrderActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable (b : Bad (nativePlaceSelection T))
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))

/-- S576 QvPhiQOrderFields filled directly from the S593 qVFamilyK preimage. -/
noncomputable def s600QvPhiQOrderFields :
    QvPhiQOrderFields (K := K) P.ramification (s566Input (K := K) P) A where
  divisor := (positiveQvPhiPreimageAtQvOrder (K := K) T b P A).divisor
  rationalFunction :=
    (positiveQvPhiPreimageAtQvOrder (K := K) T b P A).rationalFunction
  divisor_eq :=
    (positiveQvPhiPreimageAtQvOrder (K := K) T b P A).divisor_eq

/-- Conditional tau = natural powers of the S593 positive element. -/
noncomputable def s600Tau :
    Submonoid (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification
        (s566Input (K := K) P)) A) :=
  tauOfQOrderFields (K := K) P.ramification (s566Input (K := K) P) A
    (s600QvPhiQOrderFields (K := K) T b P A)

/-- Package of fields and tau. -/
structure S600PositiveFieldsTauPackage where
  fields : QvPhiQOrderFields (K := K) P.ramification
    (s566Input (K := K) P) A
  tau : Submonoid (PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) P.ramification
      (s566Input (K := K) P)) A)
  tau_eq : tau = Submonoid.powers
    (qOrderEndomorphismOfFields (K := K) P.ramification
      (s566Input (K := K) P) A fields)

/-- Actual package. -/
noncomputable def s600PositiveFieldsTauPackage :
    S600PositiveFieldsTauPackage (K := K) P A where
  fields := s600QvPhiQOrderFields (K := K) T b P A
  tau := s600Tau (K := K) T b P A
  tau_eq := rfl

/-- The tau is the powers of the positive qOrder element. -/
theorem s600Tau_eq_powers :
    s600Tau (K := K) T b P A =
      Submonoid.powers
        (qOrderEndomorphismOfFields (K := K) P.ramification
          (s566Input (K := K) P) A
          (s600QvPhiQOrderFields (K := K) T b P A)) := rfl

/-- The qOrder element belongs to the tau. -/
theorem s600QOrderEndomorphism_mem_tau :
    qOrderEndomorphismOfFields (K := K) P.ramification
        (s566Input (K := K) P) A
        (s600QvPhiQOrderFields (K := K) T b P A) ∈
      s600Tau (K := K) T b P A :=
  Submonoid.mem_powers _

end LeanFormal.IUT.XiFPaper.S600PositiveFieldsFromS593Actual

end
