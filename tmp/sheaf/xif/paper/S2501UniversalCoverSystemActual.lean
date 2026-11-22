import tmp.sheaf.xif.paper.S2500CategoricalOtriangleActual
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Basic

/-! # S2501: actual finite-Galois inverse system for the universal cover

The index category is the actual cofiltered system of finite-dimensional Galois
intermediate fields of the algebraic closure; transition maps are the actual
field inclusions.  This is the concrete universal-covering index system.  The
O^◃/O^▷ level objects and rho_v maps remain exact missing. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2500CategoricalOtriangleActual

namespace LeanFormal.IUT.XiFPaper.S2501UniversalCoverSystemActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Finite-dimensional Galois intermediate fields of the algebraic closure. -/
abbrev S2501Index : Type := { L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]) //
  FiniteDimensional ℚ_[p] L ∧ IsGalois ℚ_[p] L }

def S2501Le (L M : S2501Index p) : Prop := M.1 ≤ L.1

theorem S2501Le_refl (L : S2501Index p) : S2501Le p L L := le_rfl

theorem S2501Le_trans {L M N : S2501Index p}
    (hLM : S2501Le p L M) (hMN : S2501Le p M N) :
    S2501Le p L N := le_trans hMN hLM

def S2501Obj (L : S2501Index p) : Type := L.1

def S2501Transition {L M : S2501Index p} (h : S2501Le p L M)
    (x : S2501Obj p M) : S2501Obj p L :=
  ⟨x.1, h x.2⟩

theorem S2501Transition_refl (L : S2501Index p) (x : S2501Obj p L) :
    S2501Transition p (S2501Le_refl p L) x = x := by
  apply Subtype.ext
  rfl

/-- The actual finite-Galois inverse system as an S2500ProSystem. -/
noncomputable def S2501ProSystem : S2500ProSystem where
  Index := S2501Index p
  le := S2501Le p
  le_refl := S2501Le_refl p
  le_trans := fun hLM hMN => S2501Le_trans p hLM hMN
  obj := S2501Obj p
  transition := fun h x => S2501Transition p h x
  transition_refl := S2501Transition_refl p

#check S2501Index
#check S2501ProSystem
#check S2501Transition_refl

end LeanFormal.IUT.XiFPaper.S2501UniversalCoverSystemActual
end
