import tmp.sheaf.xif.paper.S575QvPhiPositivePreimageActual
import tmp.sheaf.xif.paper.S566QvPhiQOrderFieldsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S601QvPhiQOrderFieldsFromPreimageActual
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S555QvPhiTauConstructionGapActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))
variable {qOrder : ℕ}

noncomputable def qvPhiQOrderFieldsOfPreimage
    (H : PositiveQvPhiPreimage (K := K) P A qOrder) :
    QvPhiQOrderFields (K := K) P.ramification (s566Input P) A where
  divisor := H.divisor
  rationalFunction := H.rationalFunction
  divisor_eq := H.divisor_eq

noncomputable def qOrderEndomorphismOfPreimage
    (H : PositiveQvPhiPreimage (K := K) P A qOrder) :
    PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (s566Input P)) A :=
  qOrderEndomorphismOfFields (K := K) P.ramification (s566Input P) A
    (qvPhiQOrderFieldsOfPreimage (K := K) P A H)

noncomputable def tauOfPreimage
    (H : PositiveQvPhiPreimage (K := K) P A qOrder) :
    Submonoid (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (s566Input P)) A) :=
  tauOfQOrderFields (K := K) P.ramification (s566Input P) A
    (qvPhiQOrderFieldsOfPreimage (K := K) P A H)

theorem qOrderEndomorphismOfPreimage_mem_tau
    (H : PositiveQvPhiPreimage (K := K) P A qOrder) :
    qOrderEndomorphismOfPreimage (K := K) P A H ∈
      tauOfPreimage (K := K) P A H :=
  Submonoid.mem_powers _

end LeanFormal.IUT.XiFPaper.S601QvPhiQOrderFieldsFromPreimageActual
end
