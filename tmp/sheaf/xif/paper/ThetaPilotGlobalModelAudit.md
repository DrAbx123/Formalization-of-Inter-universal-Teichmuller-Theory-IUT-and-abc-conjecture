# Theta-pilot global model audit

Scope: source-text and current-tree architecture audit only. No Lean objects are
introduced, and no hull equality or inequality is asserted here.

## 1. Paper architecture: two different global realified objects

IUT III, Definition 3.8, (i) (iut3.txt:6731-6769) defines two distinct objects:

* the q-pilot object: the object of the [global realified] Frobenioid
  `†C^⊩_Δ` (IUT II, Corollary 4.10, (i)) determined by the collection of `q_v`
  for `v ∈ V_bad`;
* the Θ-pilot object: the object of
  `∏_{j∈F_l^×} (†F^⊛_MOD)_j` or `∏_{j∈F_l^×} (†F^⊛_mod)_j`, regarded as an
  object of the global realified Frobenioid `†C^⊩_LGP = C^⊩_LGP(†HT^Θ±ellNF)`
  or `†C^⊩_lgp = C^⊩_lgp(†HT^Θ±ellNF)` (iut3.txt:6731-6769).

The Θ-link is a gluing between the F^⊩×μ-prime-strip whose pilot object is a
Θ-pilot object in the **domain** and the one whose pilot object is a q-pilot
object in the **codomain** (iut3.txt:807-820, 9775-9800). Thus the Theta-pilot
object and the q-pilot object are not objects of the same Frobenioid: the
q-pilot is in `C^⊩_Δ`; the Theta-pilot is in `C^⊩_LGP`/`C^⊩_lgp`. The link
relates them but does not identify their carriers.

The log-volume `−|log Θ|` is the procession-normalized mono-analytic
log-volume of the **holomorphic hull of the union of possible images** of the
Theta-pilot object (iut3.txt:902-907, 10499-10535). The possible images are
regions

    n,◦U_{j,vQ} ⊆ I_Q(S^±_{j+1}; n,◦D^⊣_{vQ})

in the tensor packets indexed by `S^±_{j+1}` (iut3.txt:10535-10586); they are
not weighted averages of theta values and not functions on `F_l^×` with a
single scalar per label.

## 2. Current tree: what is actually constructed

### 2.1 `GlobalRealifiedFrobenioidActual.lean`

This constructs a carrier of a global realified Frobenioid on the base field
`Fmod`:

* one-arrow base category `GlobalBaseCategory`;
* prime index `NumberFieldPlace Fmod`;
* finitely supported realified divisor group/monoid;
* arithmetic degree = log absolute norm at finite places, archimedean weight 1;
* prime divisors and a value functor.

The file explicitly records that the full categorical
`FrobenioidPresentation`/`FrobenioidAxioms`, the `q_v` family, and the `q_v`
zero-locus divisor are **not** constructed there. This is a q-side carrier
layer of `C^⊩_mod`, not the LGP global realified Frobenioid.

### 2.2 `GlobalFrobenioidPresentationActual.lean`

This reuses the actual model Frobenioid presentation

    numberFieldFrobenioidPresentation (F := Fmod)

with its `DivisorialMonoidOn`, structure functor, connectedness, total
epimorphicity, and FrobenioidAxioms. This is an actual model presentation of
`C^⊩_mod`; it is not a construction of `C^⊩_LGP`/`C^⊩_lgp`.

### 2.3 `QPilotGlobalObjectActual.lean`

This constructs a model object

    qPilotGlobalObject : Iut.SourceModelFrobenioid.Object presentationDivisorMonoid

whose divisor class is the finite product over `V_bad` of

    qVZeroLocusEffectiveDivisor b =
      (Finsupp.single (underlyingPrime b.1) 1, 0).

Its degree is the arithmetic degree of that effective divisor, i.e. a sum of
log absolute norms of the underlying finite primes. The file itself states
that this is not identified with a global arithmetic line bundle/global ideal
family, with any source q descent beyond the clause-B q_v family, or with
`−|log q|`.

So this is a q-side model object supported on **prime divisors**, not the
paper's q-pilot object determined by `q_v` as a Frobenioid object; and it is not
a Theta-pilot object at all.

### 2.4 `GlobalQPilotObjectActual.lean`

This constructs the actual collection

    globalQParameterFamily : I.initial.badPlaces → Real
    globalQAbsLogTotal / globalQPilotSignedLog
    globalQPilotCollection

from `I.initial.reduction.qParameter`. It proves the signed global q-pilot
volume equals `sourceQPilotSignedLog I.initial`. It does **not** construct a
Frobenioid object; its boundary says the missing object is a map from the bad
places to the presentation's global prime index plus the corresponding
effective divisor class.

Therefore there are two current q-side constructions, neither of which is the
paper's full global q-pilot Frobenioid object:

* a prime-divisor model object in a model `C^⊩_mod` presentation
  (`QPilotGlobalObjectActual`);
* a real bad-qParameter collection with a missing Frobenioid map
  (`GlobalQPilotObjectActual`).

### 2.5 Value-layer Theta-pilot surrogates

The current Theta-pilot objects are value-layer functions, not global
realified Frobenioid objects:

* `SourceImageHull.sourceThetaPilotPoint` is `fun _ => thetaImageValue R n j`:
  the same value on every component;
* `PaperThetaPilotCarrierActual.paperThetaPilotPointAt q j` is
  `fun _ => ofAdd(log(thetaValue q j))`, again constant on every `F_l^×`
  coordinate;
* `SignedHullSupActual` takes an `sSup` of `sourceLocalLogDegree` over the
  value-realized `sourceHolomorphicHull`.

These are value-layer realizations. They do not construct the actual object of
`C^⊩_LGP`/`C^⊩_lgp`, its LGP-monoid splitting data, the tensor packets
`I_Q(S^±_{j+1}; ...)`, the log-shell regions, or the Kummer isomorphisms.

## 3. Is the current q-side model the same architecture as paper Theta-pilot?

No. The differences are architectural, not just missing equalities:

| paper Theta-pilot | current q-side / value-layer object |
|---|---|
| object of `C^⊩_LGP`/`C^⊩_lgp` | q-side object of model `C^⊩_mod` presentation or bare collection |
| global realified object with LGP-monoid splitting data | effective divisor supported on underlying primes, or finite-support real divisor on bad places |
| possible images are tensor-packet regions `n,◦U_{j,vQ}` | constant value functions / tuples on `F_l^×` |
| log-volume is the hull log-volume of the union of possible images | weighted average of theta logs, or `sSup` over a value-layer hull |
| Kummer isomorphisms and Ind1/Ind2/Ind3 act on the object | no LGP/Kummer/tensor action in the value-layer surrogate |

Consequently, the apparent contradiction

    2.5 log(q_v)  vs.  the q-pilot target

is not a contradiction in the paper. It comes from replacing the paper's
Theta-pilot **global realified hull object** by a value-layer weighted average
of theta logs. A weighted average is not a hull log-volume, and a value
function on labels is not an object of `C^⊩_LGP`/`C^⊩_lgp`. The q-side
prime-divisor model likewise uses a different divisor than the q_v collection
of the paper. No comparison between these two surrogates can be used to
infer a paper inequality or its failure.

## 4. Exact missing objects (not fake)

For a genuine comparison one needs, at least:

1. the actual global realified Frobenioid `C^⊩_LGP`/`C^⊩_lgp` and its
   `FrobenioidPresentation`, not only the `C^⊩_mod` model;
2. the LGP-monoid splitting data at `V_bad` generated by the actual theta
   values `q_v^{j^2}`, with the actual `2l`-th root normalization;
3. the actual tensor packets `I_Q(S^±_{j+1}; D^⊣_{vQ})` and the log-shell
   regions, with the Kummer isomorphisms and Ind1/Ind2/Ind3;
4. the actual global realified Theta-pilot object and its arithmetic divisor;
5. the holomorphic hull of the union of possible images inside that object;
6. the actual q-pilot object of the same global realified Frobenioid
   theory, not just the effective-prime-divisor model;
7. the paper's unit/integral `μ_log` normalization and signed
   `−|log Θ|` convention, applied to the hull.

Until these are constructed, the current q-side objects and value-layer
Theta-pilot surrogates are different architectures. They cannot supply the
paper Theta-pilot hull or a legitimate `2.5 log q_v` counterexample.
