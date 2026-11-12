# ROUTE-B-FMOD-ID — rootBase vs C3LogShellPlaceL base field/place identification

Status: READ-ONLY audit, 2026-11-12. No compile.
Objects:
- Mzk1RouteBBridgeActual.lean (BaseCompletionEquivL, BaseCompletionEquivLObstruction)
- PaperRootCompletionTensorActual.lean
- PaperThetaRootObstructionActual.lean
- QVFamTensorCoefficientActual.lean
- Mzk1C3LogShellTensorLActual.lean
- S1487OQPilotScalarEqualityActual.lean (S1487FaithfulSourceData/Input/C3)

## 1. Exact types

rootBase (PaperRootCompletionTensorActual:35):
  abbrev rootBase : Type := sourceRootField T b.
sourceRootField (PaperThetaRootObstructionActual:41-42):
  abbrev sourceRootField : Type := NormalizedCompletion (qVFamTensorPlace T b).
Therefore, definitionally:
  rootBase T b = NormalizedCompletion (qVFamTensorPlace T b)   [rfl].

qVFamTensorPlace (QVFamTensorCoefficientActual:47):
  abbrev qVFamTensorPlace : NumberField.FinitePlace T.arithmetic.F :=
    (nativeBadLift T).lift b.
Its type is the F-place, not Fmod. The derived place-with-prime is
qVFamTensorPlaces (QVFam:63-66):
  def qVFamTensorPlaces ... : FinitePlaceAtPrime T.arithmetic.F (qVFamTensorP T b) :=
    ⟨qVFamTensorPlace T b, rfl⟩.

C3LogShellPlaceL (Mzk1C3LogShellTensorLActual:35-37):
  abbrev C3LogShellPlaceL (i : C3L.tensorIndex) :
    FinitePlaceAtPrime I.initial.arithmetic.Fmod C3L.p :=
    C3L.tensorPlaces i (C3L.tensorTuple i).
C3 fiber:
  CommonPrimeCompletion (C3LogShellPlaceL C3L i)
  = NormalizedCompletion (C3LogShellPlaceL C3L i).val.

RouteBBridge BaseCompletionEquivL asks exactly
  rootBase T b = CommonPrimeCompletion (C3LogShellPlaceL C3L i).
After unfolding the two definitions this is an equality of normalized completions
of two places, one over T.arithmetic.F and one over I.initial.arithmetic.Fmod.

## 2. S1487 chain: where the base fields are shared

S1487FaithfulSourceData (S1487:520-524):
  S1487SourceData ... with arithmetic := S1487Arithmetic l.
S1487Arithmetic (S1487:395-396):
  abbrev S1487Arithmetic (l) : InitialThetaArithmeticData :=
    concreteGaussianInitialThetaArithmeticData l.
concreteGaussianInitialThetaArithmeticData (ConcreteFinitePlaceBoundary:25-31):
  Fmod := GaussianField
  F := GaussianField
  K := GaussianField
  curve := concreteSplitPuncturedCurve.baseChange GaussianField.
Thus inside S1487, for the I side:
  I.initial.arithmetic.Fmod = GaussianField   [definitional]
  I.initial.arithmetic.F = GaussianField      [definitional].
S1487FaithfulInput (S1487:537-539):
  S1487OriginalInput S1487FaithfulSourceData, with initial := S1487FaithfulSourceData.
S1487FaithfulC3 (S1487:548-550):
  actualSourcePilotRegionDataL S1487FivePlace, type
  SourcePilotRegionDataL (I := S1487FaithfulInput).
S1487FivePlace (S1487:128):
  FinitePlaceAtPrime GaussianField 5.
So for the concrete S1487 I, the base field is definitionally GaussianField and
the C3 place is a finite place at prime 5.

What is NOT present:
- S1487 uses OriginalInput, not SourceNativeInitialThetaData. There is no native
  T in S1487 with T.arithmetic = S1487Arithmetic.
- Even if one builds such a T, no theorem equates an arbitrary
  T.arithmetic.Fmod with I.initial.arithmetic.Fmod. Both are independent
  structure fields of InitialThetaArithmeticData (ArithmeticData.lean:62-81).
- qVFamTensorPlace uses F, while C3LogShellPlaceL uses Fmod. The F=Fmod
  identification is only definitional for the concrete Gaussian arithmetic; it
  is not generic.
- There is no canonical b <-> C3L.tensorIndex map. RouteBBridge already records
  BadToC3TensorMapL as an explicit obstruction (Mzk1RouteBBridgeActual:80-98).

## 3. Natural identification: only conditional, not rfl

There is one rfl part:
  rootBase T b = NormalizedCompletion (qVFamTensorPlace T b)   [sourceRootField]
and one rfl part:
  CommonPrimeCompletion (C3LogShellPlaceL C3L i)
    = NormalizedCompletion (C3LogShellPlaceL C3L i).val.

But the cross equality needs:
  (i) base-field equality T.arithmetic.F = I.initial.arithmetic.Fmod (or an
      arithmetic-record equality T.arithmetic = I.initial.arithmetic plus
      F=Fmod for the concrete Gaussian case);
  (ii) prime equality qVFamTensorP T b = C3L.p;
  (iii) an index map e : C3L.tensorIndex -> Bad (nativePlaceSelection T);
  (iv) a place equality after these casts:
       qVFamTensorPlaces T b = C3LogShellPlaceL C3L (e? b) (suitably cast).
No existing declaration supplies (i)-(iv) for arbitrary T/I/C3L.

A faithful abstract record (explicit target data, no inhabitant) is:

  structure RouteBBasePlaceID
      (T : SourceNativeInitialThetaData) (I : OriginalInput)
      (C3L : SourcePilotRegionDataL (I := I)) where
    index : C3L.tensorIndex -> Bad (nativePlaceSelection T)
    arith_eq : T.arithmetic = I.initial.arithmetic
    f_eq_fmod : T.arithmetic.F = T.arithmetic.Fmod
    prime_eq : forall i, qVFamTensorP T (index i) = C3L.p
    place_eq : forall i, HEq (qVFamTensorPlace T (index i))
      (C3LogShellPlaceL C3L i).val

Given such data plus the cast of F=Fmod, one can build
BaseCompletionEquivL; without it, only the existing
BaseCompletionEquivLObstruction Prop is available.

## 4. Lean lemma templates

(1) Definitional rootBase unfolding (true by rfl):
  theorem rootBase_eq_normalized
      (T) (b) :
      rootBase T b = NormalizedCompletion (qVFamTensorPlace T b) := rfl
  theorem c3Fiber_eq_normalized
      (I) (C3L) (i) :
      CommonPrimeCompletion (C3LogShellPlaceL C3L i) =
        NormalizedCompletion (C3LogShellPlaceL C3L i).val := rfl

(2) Place equality -> completion equality (schematic; after the base-field and
prime casts are supplied by RouteBBasePlaceID):
  theorem rootBase_eq_c3Fiber_of_place_eq
      (hplace : qVFamTensorPlace T b = (C3LogShellPlaceL C3L i).val) :
      rootBase T b = CommonPrimeCompletion (C3LogShellPlaceL C3L i) := by
    rw [rootBase_eq_normalized, c3Fiber_eq_normalized]
    exact congrArg NormalizedCompletion hplace

  This is only schematic: the two sides have types over T.arithmetic.F and
  I.initial.arithmetic.Fmod, so hplace is well-typed only after the F=Fmod
  identification. In Lean the actual lemma must take the cast/equality
  hypotheses explicitly, not assume them.

(3) S1487 specialization: for S1487FaithfulInput and S1487FaithfulC3, the base
field is definitionally GaussianField and C3 place is S1487FivePlace; the only
missing pieces are a native T with the same arithmetic and the place/index
equality. No theorem currently builds that T.

## 5. Verdict

- There is no generic equality T.arithmetic.Fmod = I.initial.arithmetic.Fmod;
  the two are independent InitialThetaArithmeticData fields.
- S1487's base fields are definitionally equal only because its arithmetic is
  concreteGaussianInitialThetaArithmeticData (Fmod=F=K=GaussianField).
- qVFamTensorPlace is an F-place; C3LogShellPlaceL is an Fmod-place-at-prime.
  Even with F=Fmod, one still needs prime and place equality plus an index map.
- rootBase = NormalizedCompletion qVFamTensorPlace is rfl; the missing cross
  equality is the BaseCompletionEquivL.carrier_eq, exactly the Route B GAP.
- No natural rfl bridge exists for arbitrary T/I/C3L. A conditional
  RouteBBasePlaceID record plus cast hypotheses is the honest Lean shape.
- No Lean file written; no compile claimed.
