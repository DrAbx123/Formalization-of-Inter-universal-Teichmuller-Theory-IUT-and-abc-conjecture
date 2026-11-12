# THETADATA-EMPTINESS — qOrder vs qroot order and the coprime question

Status: READ-ONLY RESOLUTION, 2026-11-12. No compile, no Lean claim.
Sources: Iut/Cor312/ThetaData/Basic.lean:171-194, TateParameterAt.lean:108-124,
AdmissiblePrime.lean:106-157, Concrete/ThetaLocalConstruct/Data.lean:279-346,
Concrete/Existence.lean:218-320, Iut/Cor312/LeftHandSide.lean:78-93.

## 0. The two orders

1. qOrder is the order of q, not of qroot.
   Basic.lean:176-177:
     D.qOrder w hw =
       ((D.tateParam w hw).toOrdered (isUniformizer_unifAt w)).orderNat
   so qOrder = ord_w(q_w) with respect to a uniformizer of F_w. It is not defined
   from qroot.

2. qrootOf is a 2*ell-th root of the Tate q in the completion:
   Data.lean:280-291:
     qrootOf D v : completionAt D.Kt v
     qrootOf_spec : qrootOf D v ^ (2 * D.ell) =
       ((D.tate.S v hv).t.q : localCompletion v)
   The order of qroot is the order of q divided by 2*ell, with the p-adic
   normalization of ordp. The exact source formula is Data.lean:327-330:
     ordp D.Kt v (qrootOf D v) =
       (D.qOrder w hw : Real) / (2 * D.ell * ramIdx D.F w).

3. q_order_coprime (AdmissiblePrime.lean:152-156) says ell is coprime to the
   order of q (D.qOrder), not to the order of qroot:
     Nat.Coprime D.ell (D.qOrder w hw).

## 1. Does 2*ell*e divide qOrder follow?

No. The source does not state an integer divisibility
  2 * ell * ramIdx D.F w | D.qOrder.
It states the real-valued identity ordp(qroot) = qOrder / (2 ell e). The
quantity ordp is normalized by the rational prime p and is not restricted to
integers: for a ramified completion it already contains the ramification
denominator (ordp of a uniformizer is not 1 in general). Therefore the value
qOrder/(2 ell e) may be rational, and qrootOf can exist as an element of a
ramified completion without 2*ell*e dividing qOrder.

The tempting derivation
  qroot ^ (2 ell) = q
  => 2 ell * ordp(qroot) = ordp(q)
  => 2 ell * e | qOrder
is invalid at the last step: ordp is a real-valued normalized valuation; it does
not say ordp(qroot) is an integer. The source only gives the real identity, so
no contradiction with Coprime ell qOrder follows.

If one additionally assumed that ordp(qroot) is an integer, one would get a
contradiction with ell coprime to qOrder. But that integrality is not a field of
InitialThetaData and is not proved by qrootOf; it would be an extra hypothesis.

## 2. Example: 11a1, I5, ell=7

- qOrder = 5 (raw order of the Tate q; QORDER-NORMALIZATION/QORDER-BOUND).
- Data.lean formula with ramIdx D.F w = 1 gives
    ordp(qroot) = 5/(2*7) = 5/14,
  a rational number, not an integer.
- Coprime(7,5) holds.
- Therefore the pair qOrder=5, ell=7 does NOT contradict q_order_coprime; it only
  shows that qroot must live in a completion whose ramification supplies the
  denominator 14 (or that the root is not in the unramified completion at all).
  Whether such a completion actually occurs for a concrete initial Theta-data is
  a separate arithmetic question, not settled by the order formula.

This also shows why the naive integer-divisibility argument cannot certify
InitialThetaData empty: the source formula is a real ordp identity, not an
integer divisibility statement.

## 3. What is actually required for an InitialThetaData?

InitialThetaData (Basic.lean:81-113) requires:
  F, Fbar, E, VBad, global, prime, orb, localData.
The qroot is derived from localData and the Tate family; InitialThetaData does not
store qroot as a field. The qOrder and coprime fields are:
  qOrder_pos (Basic:180-182),
  coprime_qOrder (Basic:191-194),
  q_order_coprime (AdmissiblePrime:152-156).
No field asserts 2 ell e | qOrder and no field asserts an upper bound on qOrder.

Therefore:
- the qroot/coprime pair is not an inconsistency in the stated fields;
- it also does not prove InitialThetaData empty;
- whether an InitialThetaData exists remains a separate satisfiability question
  (no concrete construction in the audited files; thetaData in Existence.lean:303
  is conditional on EllipticCurveData + CurveArithmetic + TateInputs +
  ModEllRepData + hP2/hP5/hcore; no actual curve is supplied).

## 4. Lean statement draft (source-level, no compile)

The exact source facts to use:

  theorem qOrder_eq_orderNat
      (D : InitialThetaData) (w : FinitePlace D.F)
      (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
      D.qOrder w hw =
        ((D.tateParam w hw).toOrdered (isUniformizer_unifAt w)).orderNat

  theorem qrootOf_spec
      (D : InitialThetaData) {v : FinitePlace D.Kt} (hv : IsBadK D v) :
      qrootOf D v ^ (2 * D.ell) = ((D.tate.S v hv).t.q : localCompletion v)

  lemma ordp_qrootOf
      (D : InitialThetaData) (v : FinitePlace D.Kt) (w : FinitePlace D.F)
      (h : (Place.finite v).LiesOver (Place.finite w))
      (hw : w ∈ badPlacesOver D.F D.E D.VBad) :
      ordp D.Kt v (qrootOf D v) =
        (D.qOrder w hw : Real) / (2 * D.ell * ramIdx D.F w)

No theorem 2*ell*ramIdx | qOrder is available, and no theorem proves
InitialThetaData empty. The correct formal statement of the non-contradiction is
the compatibility of the real identity with q_order_coprime, not an integer
divisibility claim.

## 5. Verdict

1. qOrder is the order of q; qroot order is qOrder/(2 ell e) as a real ordp.
2. The claimed divisibility 2 ell e | qOrder is NOT a source consequence and
   should not be asserted. The real identity is compatible with Coprime(ell,qOrder).
3. 11a1/I5/ell=7 gives qOrder=5 and ordp(qroot)=5/14 (ramIdx=1); this is not an
   integer, so it cannot be used to prove a contradiction. Actual membership of
   11a1 requires the full InitialThetaData arithmetic conditions, which are not
   established by this example.
4. Therefore the qroot/coprime argument does NOT prove InitialThetaData empty;
   the P0 emptiness question is not settled by this route. InitialThetaData
   satisfiability remains OPEN: no concrete inhabitant is constructed, thetaData
   is conditional, and S1487 is not a lana InitialThetaData.
5. The variant status is unchanged: Cor312VariantHolds is an unproved hypothesis;
   if InitialThetaData is empty, the variant is vacuous; if inhabited, no qOrder
   bound. Neither case is a proof of the variant or ABC.
