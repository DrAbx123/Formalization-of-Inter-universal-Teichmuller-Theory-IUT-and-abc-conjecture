import tmp.sheaf.xif.paper.S555QvPhiTauConstructionGapActual

-- S563: conditional qOrder/pi element in O^triangle from explicit divisor/
-- rationalFunction fields, and tau = powers of the element.  No fake element.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S555QvPhiTauConstructionGapActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (R : RamificationIndexData (K := K))
variable (data : Input (qvPhi (K := K) R))
variable (A : Object (qvPhi (K := K) R))

-- Exact fields needed to build the element: an effective divisor d and a
-- rational function r whose divisor is of d.
structure QvPhiQOrderFields (A : Object (qvPhi (K := K) R)) where
  divisor : ((qvPhi (K := K) R).obj A.base).carrier
  rationalFunction : data.rationalFunctions.obj A.base
  divisor_eq : data.divisor A.base rationalFunction =
    Algebra.GrothendieckAddGroup.of divisor

noncomputable def qOrderEndomorphismOfFields
    (F : QvPhiQOrderFields (K := K) R data A) :
    PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) R data) A where
  hom :=
    { frobeniusDegree := 1
      base := 𝟙 A.base
      divisor := F.divisor
      rationalFunction := F.rationalFunction
      balance := by
        change (1 : ℕ) • A.divisorClass +
            Algebra.GrothendieckAddGroup.of F.divisor =
          gpPullback (qvPhi (K := K) R) (𝟙 A.base) A.divisorClass +
            data.divisor A.base F.rationalFunction
        rw [one_nsmul, gpPullback_id, F.divisor_eq]
        simp }
  linear := rfl
  baseIdentity := rfl

-- tau = pi^N (natural powers of the chosen qOrder/pi element).
noncomputable def tauOfQOrderFields
    (F : QvPhiQOrderFields (K := K) R data A) :
    Submonoid (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) R data) A) :=
  Submonoid.powers (qOrderEndomorphismOfFields (K := K) R data A F)

theorem qOrderEndomorphism_mem_tau
    (F : QvPhiQOrderFields (K := K) R data A) :
    qOrderEndomorphismOfFields (K := K) R data A F ∈
      tauOfQOrderFields (K := K) R data A F :=
  Submonoid.mem_powers _

theorem tauOfQOrderFields_eq_powers
    (F : QvPhiQOrderFields (K := K) R data A) :
    tauOfQOrderFields (K := K) R data A F =
      Submonoid.powers (qOrderEndomorphismOfFields (K := K) R data A F) :=
  rfl

#check QvPhiQOrderFields
#check qOrderEndomorphismOfFields
#check tauOfQOrderFields
#check qOrderEndomorphism_mem_tau

end LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual

end