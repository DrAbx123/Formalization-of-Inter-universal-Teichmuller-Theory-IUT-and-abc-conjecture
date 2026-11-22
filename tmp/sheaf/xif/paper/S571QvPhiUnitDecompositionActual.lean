import tmp.sheaf.xif.paper.S568QvPhiQOrderTauActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S571QvPhiUnitDecompositionActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S568QvPhiQOrderTauActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (R : RamificationIndexData (K := K))
variable (data : Input (qvPhi (K := K) R))
variable (A : Object (qvPhi (K := K) R))
variable (F : QvPhiQOrderFields (K := K) R data A)

noncomputable def qvPi :
    PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) R data) A :=
  qOrderEndomorphismOfFields (K := K) R data A F

/-- Divisor divisibility is necessary to extract n from a general element. -/
def QvPhiDivisorDivisibility
    (a : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) R data) A) : Prop :=
  ∃ n : ℕ, a.hom.divisor = n • F.divisor

/-- Exact decomposition datum: a = unit * pi^n, with exponent uniqueness. -/
structure QvPhiUnitDecompositionData
    (a : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) R data) A) where
  unit_part : PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) R data) A
  exponent : ℕ
  decomposition : a = unit_part * qvPi (K := K) R data A F ^ exponent
  unique_exponent : ∀ (u : PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) R data) A) (m : ℕ),
      a = u * qvPi (K := K) R data A F ^ m → m = exponent

/-- Exact-missing predicate: every O^triangle element has a unique
unit-times-pi^n decomposition. -/
def QvPhiUnitDecompositionRequired : Prop :=
  ∀ a : PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) R data) A,
    Nonempty (QvPhiUnitDecompositionData (K := K) R data A F a)

/-- Even the weaker divisor divisibility is not available without an actual
qOrder element/divisor comparison. -/
def QvPhiDivisorDivisibilityRequired : Prop :=
  ∀ a : PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) R data) A,
    QvPhiDivisorDivisibility (K := K) R data A F a

/-- The S568 gap's unit/exponent decomposition is exactly the
unit-times-pi^n datum, not a proved instance. -/
def QvPhiS568DecompositionRequired : Prop :=
  Nonempty (QvPhiUnitDecompositionGap (K := K) R data F)

end LeanFormal.IUT.XiFPaper.S571QvPhiUnitDecompositionActual

end
