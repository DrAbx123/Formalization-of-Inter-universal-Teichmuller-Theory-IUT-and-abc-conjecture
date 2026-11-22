import tmp.sheaf.xif.paper.Mzk1P5BridgeIntegrationActual
import tmp.sheaf.xif.paper.Mzk1P5PhaseDerivedActual

/-!
# P5 root choice: r |-> qRoot^l vs r |-> qRoot

Analytic r satisfies r^2=q; the paper root qRoot satisfies qRoot^(2l)=q.
This file compares the two named root choices at the order level:
* r = qRoot^l is square-compatible: (qRoot^l)^2 = qRoot^(2l) = q;
* r = qRoot forces qRoot^2 = qRoot^(2l), i.e. the nontrivial order
  condition qRoot^(2(l-1))=1.  Hence r |-> qRoot is not the correct
  root choice for the actual non-root-of-unity qRoot.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P5RootChoiceOrderActual

open LeanFormal.IUT
open LeanFormal.IUT.Foundations.Theta

universe v

/-- The paper root order data: qRoot^(2l)=q. -/
structure RootChoiceOrderData (R : Type v) [Field R] (l : PrimeGeFive) where
  qRoot : R
  qRoot_ne_zero : qRoot ≠ 0
  q : R
  qRoot_pow : qRoot ^ (2 * l.value) = q

variable {R : Type v} [Field R] {l : PrimeGeFive}
variable (D : RootChoiceOrderData R l)

/-- The choice r = qRoot^l is square-compatible. -/
theorem root_pow_l_square (r : R) (h : r = D.qRoot ^ l.value) :
    r ^ 2 = D.q := by
  rw [h, pow_two, ← pow_add, show l.value + l.value = 2 * l.value by ring,
    D.qRoot_pow]

/-- The choice r = qRoot forces the order equality qRoot^(2l)=qRoot^2. -/
theorem root_pow_one_order (r : R) (h : r = D.qRoot) (hr2 : r ^ 2 = D.q) :
    D.qRoot ^ (2 * l.value) = D.qRoot ^ 2 := by
  rw [D.qRoot_pow, ← hr2, h, pow_two]

#print axioms root_pow_l_square
#print axioms root_pow_one_order

end LeanFormal.IUT.XiFPaper.Mzk1P5RootChoiceOrderActual
