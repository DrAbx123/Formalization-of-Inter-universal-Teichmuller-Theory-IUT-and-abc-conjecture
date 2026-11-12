# S2812 — Degree-faithful section for `ValueMonoidAt`

Date: 2026-11-07
Goal: construct
`s : Multiplicative ℝ →* I.ValueMonoidAt 0 0 v`
with `I.logDegreeAt 0 0 v (s (ofAdd b)) = b`, or give an exact impossibility proof.
Outcome: **exact no-go on the existing source-Haar carrier**; structurally
impossible there. No axiom/fake action added.

## 1. Definitions read

### FPrimeStrip

`LeanFormal/IUT/IUTI/HodgeTheater/PrimeStripCore.lean`:

```lean
structure FPrimeStrip (V : Type*) extends DPrimeStrip V where
  Mon : V → Type v
  [commMonoidMon : ∀ v, CommMonoid (Mon v)]
  action : ∀ v, toDPrimeStrip.Pi v →* MulAut (Mon v)
  degree : ∀ v, Mon v →* Multiplicative Real
```

Key point: `Mon v` is an **arbitrary commutative monoid**, and `degree v`
is an **arbitrary monoid homomorphism**. There is no surjectivity, no splitting,
and no positivity/negativity assumption in the structure.

### ValueMonoidAt and primeStripAt

`LeanFormal/IUT/IUTIII/Theorem311/SourceOriginalInput.lean`:

```lean
def primeStripAt (n m : Int) : FPrimeStrip.{umon, uv, upi} V
def valueMonoidAt (n m : Int) (v : V) : Type umon
```

`LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceImageHull.lean`:

```lean
abbrev ValueMonoidAt (n m : Int) (v : V) : Type umon :=
  (I.primeStripAt n m).Mon v

def logDegreeAt (n m : Int) (v : V) (x : I.ValueMonoidAt n m v) : Real :=
  Multiplicative.toAdd ((I.primeStripAt n m).degree v x)
```

### SourceImageRealization

```lean
structure SourceImageRealization (v : V) where
  posRealAction : Multiplicative Real →* I.ValueMonoidAt 0 0 v
  degree_of_q : I.logDegreeAt 0 0 v
    (posRealAction (Multiplicative.ofAdd
      (Real.log ((I.theaterAt 0 0).thetaPacket.q)))) =
    Real.log ((I.theaterAt 0 0).thetaPacket.q)
```

A degree-faithful section is exactly this:

```lean
def S2812DegreeFaithfulSection (v : V) : Prop :=
  ∃ s : Multiplicative Real →* I.ValueMonoidAt 0 0 v,
    ∀ b : Real, I.logDegreeAt 0 0 v (s (Multiplicative.ofAdd b)) = b
```

This is strictly stronger than `degree_of_q` (one point `b = log q`).

## 2. Actual no-go theorem

File:

```text
tmp/sheaf/xif/paper/S2812DegreeFaithfulSectionActual.lean
```

### General criterion

```lean
theorem S2812_no_section_of_logDegree_nonpos
    (hnonpos : ∀ x : I.ValueMonoidAt 0 0 v,
      I.logDegreeAt 0 0 v x ≤ 0) :
    ¬ S2812DegreeFaithfulSection I v
```

Proof: if `s` exists, evaluate at `b = 1`; the section gives
`logDegreeAt ... = 1`, while `hnonpos` gives it `≤ 0`, so `1 ≤ 0`.

### Existing actual source-Haar carrier

```lean
theorem S2812_sourceHaarActual_logDegree_nonpos
    (S : SourceDefinition31Data l) (n m : Int)
    (x : SourceHaarActualValueMonoid) :
    (sourceHaarActualOriginalInput S).logDegreeAt n m () x ≤ 0
```

This is the actual degree upper bound `≤ 0` on the existing carrier.
Consequently:

```lean
theorem S2812_sourceHaarActual_no_degreeFaithfulSection
    (S : SourceDefinition31Data l) :
    ¬ ∃ s : Multiplicative Real →* SourceHaarActualValueMonoid,
        ∀ b : Real,
          (sourceHaarActualOriginalInput S).logDegreeAt 0 0 ()
            (s (Multiplicative.ofAdd b)) = b
```

Axioms: `[propext, Classical.choice, Quot.sound]`.

## 3. Why it cannot be built on the current carrier

1. `FPrimeStrip.Mon` is arbitrary. The structure gives no element of positive
   degree, no surjectivity of `degree`, and no group structure that would
   split `degree`.
2. The actual source-Haar value monoid has **all** degrees `≤ 0`
   (`S2812_sourceHaarActual_logDegree_nonpos`). Since the positive reals form a
   group, any monoid hom into a nonpositive-degree monoid would have to send
   every positive real to degree `0`; `hdeg` would force `b = 0` for all
   `b`. The theorem above is the exact contradiction.
3. S1666/`sourceHaarActualImageRealization` only supplies `degree_of_q`
   because `q = 1`; that is a special one-point coincidence, not a section.
4. S2718 is a completion log-shell interface on `Completion place`; it has no
   `posRealAction` and cannot be transported to this value monoid.

## 4. What must change

A degree-faithful section requires replacing the carrier, not proving a field:

- **New value carrier**: an `FPrimeStrip` whose `Mon v` contains positive-degree
  elements, e.g. a copy of `Multiplicative ℝ` with `degree = id`.
  Then `s := id` (or the corresponding inclusion) satisfies
  `logDegreeAt 0 0 v (s (ofAdd b)) = b` by definition.
- **Splitting datum**: a monoid section of `degree v` (equivalently, a chosen
  splitting of the degree hom on its image) plus the proof that its image has the
  right degree; this is new data, not derivable from `OriginalInput`.
- **New SourceImageRealization**: once the carrier section exists, package
  `posRealAction := s` and `hdeg := ...`; then S2600/S2601 become unconditional
  for that input.

No such carrier/section exists in the current actual tree. The existing
source-Haar carrier is provably impossible.

## 5. Status

```text
S2812DegreeFaithfulSectionActual.lean
  src 2844 B
  SHA256 5f4d09186d7388ee65ff354648b1505589aa356b966f355890cf0b64905e5e51
  olean 41944 B
  SHA256 4c255dafdf1952385f65011e5acdd09b91e47bb9231b5bb29b9e465c53ea01c2
  EXIT=0
  AXIOMS [propext, Classical.choice, Quot.sound]
```

Verdict: **no degree-faithful section on the existing source-Haar carrier**
(actual no-go). A different value monoid/carrier with positive-degree elements
is required; do not add an axiom or a fake `posRealAction`.
