# S2152: actual functorial pointwise colimit Q; IsStack is the exact remaining missing

Date: 2026-11-02. Status: the actual functorial pointwise colimit Q is constructed and S1971FunctorialPointwiseColimit is proved. The only remaining input for this Q is Q.IsStack (equivalently IsPrestack plus effective descent). No IsStack instance is proved or claimed.

## 1. Actual construction

File: tmp/sheaf/xif/paper/S2152PointwiseColimitActual.lean

The ordinary functor underlying Q:

  S2152PFunctor : (SchemeOverField S1726K)^op ⥤ Cat
  obj U := S1971PointwiseQuotient (LocallyDiscrete.mk U)
  map f := (S1971PrecompFunctor (Discrete.mk f)).toCatHom

The functor laws are definitional:

  map_id U := rfl
  map_comp f g := rfl

The actual functorial pointwise colimit:

  S2152Q : EtaleStackPseudofunctor S1726K :=
    S2152PFunctor.toPseudofunctor'

This uses Mathlib's strict-bicategory promotion of an ordinary functor into Cat.
It is an actual pseudofunctor, not a pointwise-only family and not a label-only object.

## 2. Pointwise identification

S2152Q_obj (U) : S2152Q.obj U = S1971PointwiseQuotient U := rfl.

S2152Q_pointwise (U) :
  Nonempty (Equivalence (S2152Q.obj U) (S1971PointwiseQuotient U)) :=
  ⟨Equivalence.refl⟩.

Consequently:

  S2152FunctorialPointwiseColimit : S1971FunctorialPointwiseColimit

is proved, with witness Q.

## 3. Exact first missing

S2152QIsStack : Prop :=
  S2152Q.IsStack (SchemeOverField.etaleTopology S1726K).

S2152FirstMissing := S2152QIsStack.

Exact descent API:

S2152QIsStack_iff_descent (l) :
  S2152QIsStack <->
    S2152Q.IsPrestack (etaleTopology S1726K) /      S2149EffectiveDescent l S2152Q.

Thus the remaining obligations for Q are exactly:

1. IsPrestack: descent for morphisms / hom-presheaf sheaf condition;
2. effective descent: toDescentData essentially surjective on every etale covering sieve.

Conditional consumers:

- S2152StackFiberData_of_isStack (l) (h : S2152QIsStack) : S2149StackFiberData l;
- S2152S2143FiberData_of_isStack (l) h : S2143StackFiberData l;
- S2152S2149FiberFirstMissing_of_isStack (l) h : S2149StackFiberFirstMissing l;
- S2152S2143FiberFirstMissing_of_isStack (l) h : S2143StackFiberFirstMissing l.

## 4. No fake

- Q is a genuine pseudofunctor into Cat, constructed from an ordinary functor.
- Its U-points are identified with the pointwise action groupoids, but no claim is
  made that the pointwise groupoid alone is a stack.
- Q.IsStack is not proved and no instance is fabricated.
- No label-only representable orbicurve is used.
- Axioms: propext, Classical.choice, Quot.sound.

## 5. S2103 prestack half

Independent: S2103FirstMissing / SlicePushNaturality remains missing. S2152 constructs
the functorial pointwise colimit Q, not the S2029 slice-sheaf stack.

## 6. Status

| Item | Status |
|---|---|
| actual functorial pointwise colimit Q | BUILT |
| S1971FunctorialPointwiseColimit | PROVED |
| pointwise equivalence Q.obj U ~= action groupoid | PROVED |
| Q.IsStack | MISSING |
| IsPrestack / effective descent for Q | MISSING |
| S2149StackFiberData | conditional on Q.IsStack |
| S2143StackFiberData | conditional on Q.IsStack |
| IsStack instance | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: d9b1a9d4bd4d377a49e3eaf5ce48c8ec32962f8ea2ed38a689c4fbf08b4cae9a
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2152PointwiseColimitActual.olean, size 40392
- axioms for all declarations: propext, Classical.choice, Quot.sound.
