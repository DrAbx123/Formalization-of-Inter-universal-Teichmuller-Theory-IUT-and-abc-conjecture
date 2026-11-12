# S2158: Q stack condition — exact slice-sheaf/descent API

Date: 2026-11-02. Status: no proof of IsPrestack or effective descent for S2152Q. The remaining stack condition is reduced to two concrete API obligations. No IsStack instance is claimed.

## 1. Actual input

S2152Q is the actual functorial pointwise colimit:

  S2152Q : EtaleStackPseudofunctor S1726K;

  S2152Q.obj U = S1971PointwiseQuotient U (rfl);

  S2152Q_pointwise U : Nonempty (Equivalence (S2152Q.obj U) (S1971PointwiseQuotient U)).

S1971FunctorialPointwiseColimit is proved.

## 2. Prestack half

S2158QPrestack : Prop :=
  S2152Q.IsPrestack (SchemeOverField.etaleTopology S1726K).

S2158QHomSheaf : Prop :=
  forall (S : SchemeOverField S1726K)
    (M N : S2152Q.obj (LocallyDiscrete.mk (op S))),
    Presheaf.IsSheaf (etaleTopology S1726K).over S (S2152Q.presheafHom M N).

S2158QPrestack_iff_homSheaf:
  S2158QPrestack <-> S2158QHomSheaf.

This is the exact slice-sheaf API: for every test object and every pair of
objects, the hom-presheaf of Q is a sheaf for the slice etale topology.

## 3. Effective descent half

S2158QEffectiveDescent l :=
  S2149EffectiveDescent l S2152Q.

Concretely: for every U and every etale covering sieve R on U,
the descent functor toDescentData for Q is essentially surjective.

## 4. Required API and stack condition

structure S2158QRequiredAPI l:
  prestack : S2158QPrestack;
  effective : S2158QEffectiveDescent l.

S2158QRequiredAPI_iff_isStack l:
  Nonempty (S2158QRequiredAPI l) <-> S2152QIsStack.

Thus the remaining stack condition is exactly:

  hom-presheaf sheaf condition for Q
  +
  effective descent for Q on all etale covering sieves.

## 5. Exact first missing

S2158FirstMissing l := Nonempty (S2158QRequiredAPI l).

S2158FirstMissing_iff_isStack l:
  S2158FirstMissing l <-> S2152QIsStack.

S2158ConcreteFirstMissing l := S2158QHomSheaf / S2158QEffectiveDescent l.

S2158ConcreteFirstMissing_iff l:
  S2158ConcreteFirstMissing l <-> Nonempty (S2158QRequiredAPI l).

No inhabitant of either is constructed.

## 6. Conditional consumer

S2158StackFiberData_of_API l (h : S2158QRequiredAPI l) :
  S2149StackFiberData l.

This uses S2152StackFiberData_of_isStack and the API-to-IsStack equivalence.

## 7. No fake

- Q is the actual S2152 pseudofunctor, not a pointwise-only substitution.
- The pointwise equivalence is proved, not postulated as the stack condition.
- IsPrestack and effective descent are not proved; they are exact missing inputs.
- No label-only representable orbicurve is used.
- Axioms: propext, Classical.choice, Quot.sound.

## 8. S2103 independence

S2103 SlicePushNaturality / S2103FirstMissing remains an independent prestack half
for the S2029 slice-sheaf prestack. S2158 concerns the S2152 pointwise colimit Q;
the two are not identified.

## Verification

- EXIT=0
- SHA256: a3ddc987efc9dbb4f0ed56fc7e3875408c0cc778bd689de79f3faac59c64e77d
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2158QStackActual.olean, size 41568
- axioms for all five declarations: propext, Classical.choice, Quot.sound.
