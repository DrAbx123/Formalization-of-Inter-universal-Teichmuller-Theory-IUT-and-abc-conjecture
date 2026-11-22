import tmp.sheaf.xif.paper.Mzk1P6IVInequalityActual
import tmp.sheaf.xif.paper.Mzk1P6Thm110DisplayActual
import tmp.sheaf.xif.paper.Mzk1P6IVDisplayAssemblyActual
import tmp.sheaf.xif.paper.Mzk1P6StepVBoundConsumerActual
import tmp.sheaf.xif.paper.Mzk1P6SourceFieldsActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
open LeanFormal.IUT LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.IUTIV.StepVProcessionAverage
open LeanFormal.IUT.XiFPaper.Mzk1P6IVInequalityActual
open LeanFormal.IUT.XiFPaper.Mzk1P6Thm110DisplayActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P6IVActual
open LeanFormal.IUT.XiFPaper.Mzk1P6SourceFieldsActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6FinalAssemblyActual
/-- P6 final assembly, part 1: actual Thm 1.10 display. -/
theorem p6_final_thm110_display
    (T : Thm110DisplayTerms) (hl : 7 ≤ T.l) (hd : 1 ≤ T.dmod)
    (hS : 0 ≤ T.logDFpd + T.logFFpd)
    (hE : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T) :
    thm110Lhs T ≤ thm110Rhs T :=
  Mzk1P6Thm110DisplayActual.p6_thm110_display T hl hd hS hE hCor312
/-- P6 final assembly, part 2: weighted IV inequality. -/
theorem p6_final_iv_inequality
    (n : Nat) (hn : 2 ≤ n) (D Q S T : Real)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (l : Real) (hl : l = 2 * (n : Real) + 1) :
    p6IVR n D Q S T ≤
      (l + 5) / 4 * p6IVD l D - (l + 1) / 24 * p6IVQ l Q +
        p6IVS l S + (l + 5) * p6IVT l T :=
  p6_iv_weighted_inequality n hn D Q S T hD hS hT l hl
/-- P6 final assembly, part 3: weighted average = collection bound. -/
theorem p6_final_weightedAverage
    {E : Type*} [Fintype E] [Nonempty E]
    (lam : E → Real) (weights_pos : ∀ e, 0 < lam e)
    (l logp iotaL : Real) (l_ne_zero : l ≠ 0)
    (j : Nat) (d oq : E → Real) (slot : Fin (j + 1)) :
    (∑ et : Fin (j + 1) → E,
      collectionChoiceBound l logp iotaL j d oq et slot * ∏ i, lam (et i)) /
        (∑ et : Fin (j + 1) → E, ∏ i, lam (et i)) =
      collectionBound l ((∑ e, d e * logp * lam e) / ∑ e, lam e)
        ((∑ e, oq e * logp * lam e) / ∑ e, lam e) logp iotaL j :=
  p6_iv_weightedAverage_collectionBound lam weights_pos l logp iotaL l_ne_zero j d oq slot
#print axioms p6_final_thm110_display
#print axioms p6_final_iv_inequality
#print axioms p6_final_weightedAverage
end LeanFormal.IUT.XiFPaper.Mzk1P6FinalAssemblyActual
end