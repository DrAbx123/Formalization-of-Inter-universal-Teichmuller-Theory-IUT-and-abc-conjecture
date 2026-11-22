import LeanFormal.IUT.Foundations.Arithmetic.NormLog

/-!
# ShehddNormLogConsumerActual — norm/log degree consumer

STEP 0 prior-art (reuse only; A475 search: NormLog found):
* Foundations/Arithmetic/NormLog.lean: unitNormLogDegree (Kˣ →* Multiplicative ℝ),
  unitNormLogDegree_apply_mul, unitNormLogDegree_apply_one, norm_pos_unit.

This file packages the norm/log degree as one consumer: it is a monoid hom to the
multiplicative reals, its additive projection is Real.log of the norm, and unit norms are
positive.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddNormLogConsumerActual

open LeanFormal.IUT

/-- **PROVED consumer:** `unitNormLogDegree` is multiplicative, one maps to one, its
additive projection is the log of the norm, and unit norms are positive. -/
theorem unitNormLogDegree_consumer (K : Type*) [NormedField K] (u v : Kˣ) :
    unitNormLogDegree K (1 : Kˣ) = 1 ∧
      unitNormLogDegree K (u * v) =
        unitNormLogDegree K u * unitNormLogDegree K v ∧
        Multiplicative.toAdd (unitNormLogDegree K u) = Real.log ‖(u : K)‖ ∧
          0 < ‖(u : K)‖ :=
  ⟨unitNormLogDegree_apply_one K,
    unitNormLogDegree_apply_mul K u v,
    rfl,
    norm_pos_unit K u⟩

/-- Row record: reused norm/log assets vs the consumer interface. -/
def normLogRows : List (String × String × String) :=
  [ ("unitNormLogDegree monoid hom", "REUSED DEF", "NormLog.unitNormLogDegree")
  , ("multiplicativity / unit laws", "REUSED PROVED", "unitNormLogDegree_apply_mul / _apply_one")
  , ("additive projection = log norm", "REUSED rfl", "unitNormLogDegree.toFun")
  , ("unit norm positivity", "REUSED PROVED", "norm_pos_unit")
  , ("consumer bundle", "COMPOSED PROVED", "unitNormLogDegree_consumer") ]

theorem normLogRows_length : normLogRows.length = 5 := rfl

#check unitNormLogDegree_consumer
#check normLogRows_length

end LeanFormal.IUT.XiFPaper.ShehddNormLogConsumerActual
end
