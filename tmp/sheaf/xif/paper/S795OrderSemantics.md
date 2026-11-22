# S795: order semantics and Def 3.1(c) / q[2u] tension

## Lean order semantics

`FinitePlaceQCandidate.order` (LeanFormal/IUT/Foundations/NumberField/LocalQParameter.lean):
  exponent = -Multiplicative.toAdd (unzero(Valued.v q))
  order    = Int.toNat exponent

Thus `order` is exactly the positive valuation exponent of q.  Lean theorem:
  qVFamily_order_eq_valuation : (qVFamily T b).order = Int.toNat (qVFamily T b).exponent  (rfl)

## Source tension

IUT I Def 3.1(c), lines 3240-3248:
  l is prime to the residue characteristics and to the orders of the
  q-parameters at Vbad.

IUT I Example 3.2(iv), lines 3774-3789:
  q[1u] admits a 2l-th root q[2u] = q[1u]^(1/2l)
  in O-triangle(TX_v[1u]) (the log/root-stack), not in ordinary O-triangle_{K_v}.

In an ordinary integral monoid O^tri = O^× × N log p, if q = u p^n, then a
2l-th root would force n = 2l m, hence 2l | n, contradicting Def 3.1(c)'s
l coprime to n.  S342 proves this rigorously for the completion:
  - qVFamily_order_coprime : Nat.Coprime (qVFamily T b).order l
  - twoLRootData_impossible : no completion TwoLthRootData
  - natRootSystem_impossible : no NatRootSystem qVUnit

## Exact conclusion

S795 Lean file proves:
  Def31cOrdinaryRootConflict :=
    Nat.Coprime (qVFamily T b).order l ∧ Nonempty (TwoLthRootData T b)
  def31cOrdinaryRootConflict_false : not Def31cOrdinaryRootConflict.

If order = valuation and O^tri is ordinary integral, Def 3.1(c) and the
q[2u] root statement conflict.  The source resolves this by putting q[2u] in
the root-stack/log monoid O^tri(TX_v), not in ordinary O^tri_{K_v}.

If instead order is not the valuation, then `qVFamily.order` is not the paper
q-parameter order and cannot be used as a paper invariant.

Lean: tmp/sheaf/xif/paper/S795OrderSemanticsActual.lean (EXIT=0).
