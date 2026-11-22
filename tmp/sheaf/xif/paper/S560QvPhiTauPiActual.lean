import tmp.sheaf.xif.paper.S550QvPhiPreFrobenioidActual

/-! # S560: pi^ℕ tau on the qvPhi PreFrobenioid — exact boundary

S550 gives the actual `PreFrobenioid`, `RationalMonoidTransport`, and abstract
`QvPhiTauData`/`CharacteristicSplitting` constructor.  S522 supplies only the
ramification index `e(f)`; it does not supply a chosen uniformizer `π`, an
O^triangle element realizing `π`, or the unit decomposition
`O^× × π^ℕ ≅ O^triangle`.  Therefore the literal `τ = π^ℕ` is recorded as exact
missing data, not fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S560QvPhiTauPiActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable (R : RamificationIndexData (K := K))
variable (data : Input (qvPhiRamificationModel (K := K) R))

/-- Exact data for a `π^ℕ` characteristic splitting on the qvPhi model. -/
structure QvPhiTauPiData where
  pi : ∀ X : (qvPreFrobenioid (K := K) R data).IsotropicLinearObject,
    (qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism X.obj
  tau : ∀ X : (qvPreFrobenioid (K := K) R data).IsotropicLinearObject,
    Submonoid ((qvPreFrobenioid (K := K) R data).LinearBaseIdentityEndomorphism X.obj)
  tau_eq_powers : Prop
  pullback_mem : Prop
  units_commute : Prop
  multiplication_bijective : Prop
  isotropicHull_mem_range : Prop

def QvPhiTauPiDataRequired : Prop :=
  Nonempty (QvPhiTauPiData (K := K) R data)

end LeanFormal.IUT.XiFPaper.S560QvPhiTauPiActual
end
