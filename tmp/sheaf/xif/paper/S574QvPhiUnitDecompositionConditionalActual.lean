import tmp.sheaf.xif.paper.S567QvPhiQOrderFieldsFromTriDataActual
import tmp.sheaf.xif.paper.S571QvPhiUnitDecompositionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S574QvPhiUnitDecompositionConditionalActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S553QvPhiTriDataActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S567QvPhiQOrderFieldsFromTriDataActual
open LeanFormal.IUT.XiFPaper.S571QvPhiUnitDecompositionActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (T : QvPhiTriData (K := K))
variable (D : S556InputDataActual (K := K))
variable (A : Object (qvPhi (K := K) D.ramification))
variable (H : S567QOrderPreimage (K := K) T D A)

abbrev F574 : QvPhiQOrderFields (K := K) D.ramification (s567Input (K := K) D) A :=
  s567QvPhiQOrderFieldsOfPreimage (K := K) T D A H

noncomputable def pi574 :
    PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) D.ramification (s567Input (K := K) D)) A :=
  qvPi (K := K) D.ramification (s567Input (K := K) D) A (F574 (K := K) T D A H)

/-- Conditional decomposition data: given a unit part, exponent and the
decomposition equality, the decomposition field is proved; exponent
uniqueness remains an explicit gap Prop. -/
structure QvPhiUnitDecompositionDataConditional
    (a : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) D.ramification (s567Input (K := K) D)) A) where
  unit_part : PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) D.ramification (s567Input (K := K) D)) A
  exponent : ℕ
  decomposition : a = unit_part * pi574 (K := K) T D A H ^ exponent
  unique_exponent_gap : Prop

noncomputable def qvPhiUnitDecompositionDataConditional
    (a : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) D.ramification (s567Input (K := K) D)) A)
    (unit_part : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) D.ramification (s567Input (K := K) D)) A)
    (n : ℕ)
    (hdecomp : a = unit_part * pi574 (K := K) T D A H ^ n) :
    QvPhiUnitDecompositionDataConditional (K := K) T D A H a where
  unit_part := unit_part
  exponent := n
  decomposition := hdecomp
  unique_exponent_gap := ∀ (u : PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) D.ramification (s567Input (K := K) D)) A)
    (m : ℕ), a = u * pi574 (K := K) T D A H ^ m → m = n

/-- If exponent uniqueness is supplied, the full S571 decomposition data is
constructed (no fake uniqueness). -/
noncomputable def qvPhiUnitDecompositionOfUnique
    (a : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) D.ramification (s567Input (K := K) D)) A)
    (unit_part : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) D.ramification (s567Input (K := K) D)) A)
    (n : ℕ)
    (hdecomp : a = unit_part * pi574 (K := K) T D A H ^ n)
    (huniq : ∀ (u : PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) D.ramification (s567Input (K := K) D)) A)
      (m : ℕ), a = u * pi574 (K := K) T D A H ^ m → m = n) :
    QvPhiUnitDecompositionData (K := K) D.ramification (s567Input (K := K) D) A
      (F574 (K := K) T D A H) a where
  unit_part := unit_part
  exponent := n
  decomposition := hdecomp
  unique_exponent := huniq

def QvPhiExponentUniquenessRequired : Prop :=
  ∀ (a : PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) D.ramification (s567Input (K := K) D)) A)
    (u : PreFrobenioid.LinearBaseIdentityEndomorphism
    (P := qvPreFrobenioid (K := K) D.ramification (s567Input (K := K) D)) A)
    (n m : ℕ), a = u * pi574 (K := K) T D A H ^ n →
    a = u * pi574 (K := K) T D A H ^ m → n = m

end LeanFormal.IUT.XiFPaper.S574QvPhiUnitDecompositionConditionalActual

end
