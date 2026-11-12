# S2149: D9 stack fiber data — exact descent API and first missing

Date: 2026-11-02. Status: no actual stack fiber Q is constructed; no IsStack instance is proved. The S2143 fiber datum is exactly decomposed into a pseudofunctor, pointwise action-groupoid equivalence, the prestack condition, and effective descent.

## 1. S2143StackFiberData

Fields:

- Q : EtaleStackPseudofunctor (S1732A l).F;
- isStack : Q.IsStack (etaleTopology (S1732A l).F);
- pointwise : forall U, Nonempty (Equivalence (Q.obj U) (S1971PointwiseQuotient U)).

## 2. Exact descent API

S2149EffectiveDescent l Q:

  forall (U : SchemeOverField (S1732A l).F) (R : Sieve U),
    R in etaleTopology (S1732A l).F U ->
      (Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).EssSurj

S2149IsStack_iff l Q:

  Q.IsStack (etaleTopology (S1732A l).F) <->
    Q.IsPrestack (etaleTopology (S1732A l).F) / S2149EffectiveDescent l Q

S2149RequiredDescentAPI l Q :=
  Q.IsPrestack (etaleTopology (S1732A l).F) / S2149EffectiveDescent l Q

S2149RequiredDescentAPI_iff l Q:
  S2149RequiredDescentAPI l Q <-> Q.IsStack (etaleTopology (S1732A l).F).

This is the exact descent API needed; the IsStack field is not proved.

## 3. Decomposed fiber datum

S2149StackFiberData l:

- Q : EtaleStackPseudofunctor (S1732A l).F;
- pointwise : forall U, Nonempty (Equivalence (Q.obj U) (S1971PointwiseQuotient U));
- prestack : Q.IsPrestack (etaleTopology (S1732A l).F);
- effective : S2149EffectiveDescent l Q.

Actual conversions:

- S2149StackFiberData.toS2143 : S2149StackFiberData l -> S2143StackFiberData l;
- S2149StackFiberData.ofS2143 : S2143StackFiberData l -> S2149StackFiberData l;
- S2149StackFiberData_iff :
    Nonempty (S2149StackFiberData l) <->
      Nonempty (S2143StackFiberData l);
- S2149StackFiberFirstMissing_iff :
    S2149StackFiberFirstMissing l <-> S2143StackFiberFirstMissing l.

## 4. Exact first missing

S2149StackFiberFirstMissing l := Nonempty (S2149StackFiberData l):

  an actual pseudofunctor Q on the etale site, a pointwise equivalence of Q.obj U
  with the sign action groupoid S1971PointwiseQuotient U, the prestack condition,
  and effective descent for all etale covering sieves.

Equivalently (S2143StackFiberFirstMissing l), an actual etale stack fiber Q
whose U-points are the pointwise action groupoid.

Neither is constructed.  In particular:

- S1971FunctorialPointwiseColimit is not proved;
- S1971Stackification Q is not proved;
- no pointwise action-groupoid-only object is used as Q;
- no IsStack instance is fabricated.

## 5. Consumers

- S2143StackFiberData (via equivalence);
- S2143StackQuotientWitness (fiber field);
- S2143Witness_of_S1971 / S1971Witness_of_S2143;
- S2143HonestQuotient_of_witness / S2143S1964FirstMissing_of_witness.

## 6. No fake

No pointwise groupoid is substituted for the stack; the pointwise equivalence is a
condition on Q. No label-only representable orbicurve is used. No IsStack instance
is claimed. Axioms: propext, Classical.choice, Quot.sound.

## Verification

- EXIT=0
- SHA256: f2081a11a2de188dff30f7c77dd502e9d12a76315812d7ff781f2fb5b00a2e80
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2149StackFiberDataActual.olean, size 118328
- axioms for all four declarations: propext, Classical.choice, Quot.sound.
