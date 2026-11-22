/- R5 step 3: base different vanishing, explicit single prerequisite (route 7.1(3) OPEN).

The actual proof differentIdeal Z_p (Integers Q_p) = top needs the integer-ring
identification / traceDual instance alignment; until then hbase is a single documented
input (no sorry).
-/
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import tmp.sheaf.xif.paper.Mzk1G1LocalDifferentOrderZeroActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1BaseDifferentTopInputActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalDifferentUpperBound
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1G1LocalDifferentOrderZeroActual
variable {p : Nat} [Fact p.Prime]

/-- Single documented prerequisite: base paper different order vanishes. -/
structure BaseDifferentTop : Prop where
  hbase : localDifferentPaperOrder (p := p) (L := ℚ_[p]) = 0

/-- Base different vanishing from the single prerequisite. -/
theorem localDifferentPaperOrder_rat_eq_zero_of_base (H : BaseDifferentTop (p := p)) :
    localDifferentPaperOrder (p := p) (L := ℚ_[p]) = 0 :=
  H.hbase

#print axioms localDifferentPaperOrder_rat_eq_zero_of_base
end LeanFormal.IUT.XiFPaper.Mzk1G1BaseDifferentTopInputActual
