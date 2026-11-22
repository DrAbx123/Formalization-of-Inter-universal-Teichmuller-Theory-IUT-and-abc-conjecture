import tmp.sheaf.xif.paper.S2155MuHatActionActual

-- S2159: actual discrete topology on muQZ and conditional muHatZ action
-- from an algebraic conjugation action on muQZ.  The action itself is
-- the exact first missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2159MuQZActionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2039ActualPsiCns
open LeanFormal.IUT.XiFPaper.S2131G1TopologicalActual
open LeanFormal.IUT.XiFPaper.S2155MuHatActionActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The discrete topology on muQZ (as a bare TopologicalSpace structure). -/
def S2159MuQZTopology : TopologicalSpace (Multiplicative (muQZ p)) := ⊥

theorem S2159MuQZDiscrete :
    @DiscreteTopology (Multiplicative (muQZ p)) (S2159MuQZTopology p) :=
  discreteTopology_bot _

theorem S2159MuQZIsTopologicalGroup :
    letI := S2159MuQZTopology p
    IsTopologicalGroup (Multiplicative (muQZ p)) :=
  letI := S2159MuQZTopology p
  haveI : DiscreteTopology (Multiplicative (muQZ p)) := S2159MuQZDiscrete p
  inferInstance

/-- Exact first missing: conjugation action of Gv on muQZ. -/
abbrev S2159MuQZActionRequired : Type :=
  Gv p →* MulAut (Multiplicative (muQZ p))

/-- Actual pointwise action on muHatZ from an algebraic action on muQZ. -/
noncomputable def S2159MuHatActionOfMuQZ
    (a : S2159MuQZActionRequired p) :
    Gv p →* MulAut (muHatZ p) where
  toFun g : MulAut (muHatZ p) :=
    { toFun := fun f => (a g).toMonoidHom.comp f
      invFun := fun f => (a g).symm.toMonoidHom.comp f
      left_inv := by
        intro f
        ext q
        simp
      right_inv := by
        intro f
        ext q
        simp
      map_mul' := by
        intro f h
        ext q
        simp }
  map_one' := by
    apply MulEquiv.ext
    intro f
    apply MonoidHom.ext
    intro q
    simp
  map_mul' g h := by
    apply MulEquiv.ext
    intro f
    apply MonoidHom.ext
    intro q
    simp [MulAut.mul_apply]

/-- Conditional G1 topological module data from the muQZ action, the module
comparison, and equivariance. -/
noncomputable def S2159TopologicalModuleDataOf
    (a : S2159MuQZActionRequired p)
    (h : muHatComparison p)
    (heq : ∀ (g : Gv p) (x : muHatZ p),
      S2131ModuleEquivOfComparison (p := p) h
        (S2159MuHatActionOfMuQZ p a g x) =
        (PsiCnsCoefficientAction p).automorphism g
          (S2131ModuleEquivOfComparison (p := p) h x)) :
    S2131TopologicalModuleData p where
  muHatAction := S2159MuHatActionOfMuQZ p a
  equiv := S2131ModuleEquivOfComparison (p := p) h
  equivariant := heq

#check S2159MuQZTopology
#check S2159MuQZDiscrete
#check S2159MuQZIsTopologicalGroup
#check S2159MuQZActionRequired
#check S2159MuHatActionOfMuQZ
#check S2159TopologicalModuleDataOf

#print axioms S2159MuQZDiscrete
#print axioms S2159MuHatActionOfMuQZ
#print axioms S2159TopologicalModuleDataOf

end LeanFormal.IUT.XiFPaper.S2159MuQZActionActual

end