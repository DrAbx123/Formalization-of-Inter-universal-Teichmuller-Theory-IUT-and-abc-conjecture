import tmp.sheaf.xif.paper.S2056IsometricClosureActual
import tmp.sheaf.xif.paper.S2035ActualOUnitsMuActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2035ActualOUnitsMuActual
open LeanFormal.IUT.XiFPaper.S2056IsometricClosureActual
namespace LeanFormal.IUT.XiFPaper.S2058ClosureRingEquivActual
variable (v : FinitePrimePlace 2 7)
local instance (v : FinitePrimePlace 2 7) : Fact (Nat.Prime v.1) := ⟨v.2.2.2⟩
/-- The actual ring equivalence underlying the completion/Q_p algebraic closures. -/
noncomputable def S2058ClosureRingEquiv :
    SourceAlgebraicClosure (QPlace v) ≃+* AlgebraicClosure ℚ_[v.1] :=
  IsAlgClosure.equivOfEquiv
    (L := SourceAlgebraicClosure (QPlace v))
    (M := AlgebraicClosure ℚ_[v.1])
    (S := NormalizedCompletion (QPlace v))
    (R := ℚ_[v.1])
    (completionPadicEquiv v).symm
/-- The exact missing norm-preservation statement for the actual ring equivalence. -/
def S2058NormPreservationRequired (v : FinitePrimePlace 2 7) : Prop :=
  ∀ x : SourceAlgebraicClosure (QPlace v),
    ‖S2058ClosureRingEquiv v x‖ = ‖x‖
#check S2058ClosureRingEquiv
#check S2058NormPreservationRequired
end LeanFormal.IUT.XiFPaper.S2058ClosureRingEquivActual
end
