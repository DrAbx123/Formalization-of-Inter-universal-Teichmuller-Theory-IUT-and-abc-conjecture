# FMOD-F-RELATION — base field, completion direction, and Route B assumptions

Status: READ-ONLY audit, 2026-11-12. No compile.
Sources:
- LeanFormal/IUT/IUTI/InitialTheta/ArithmeticData.lean:26-96
- LeanFormal/IUT/Foundations/NumberField/FinitePlaceExtension.lean:45-95
- LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedCompletion.lean:20-30
- LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceCommonPrimeCompletion.lean:20
- QVFamTensorCoefficientActual.lean:42-73
- Mzk1C3LogShellTensorLActual.lean:30-45
- Mzk1RouteBBridgeActual.lean

## 1. Exact Fmod/F relation

InitialThetaArithmeticData (ArithmeticData:62-81) has independent fields
Fmod, F, K, each a NumberField, plus:
  [Algebra Fmod F]
  [Algebra F K]
  [Algebra Fmod K]
  [IsScalarTower Fmod F K]
  [FiniteDimensional Fmod F] [IsGalois Fmod F]
  [FiniteDimensional F K] [IsGalois F K]
  tower : ThetaFieldTower l Fmod F K.
ThetaFieldTower (ArithmeticData:26-36) adds:
  sqrtNegOne : HasSqrtNegOne F
  degreePrimeToL : Nat.Coprime (Module.finrank Fmod F) l.value.

So:
- Fmod is the base number field.
- F is a finite Galois extension of Fmod (algebraMap Fmod F; injective because F is a
  field and the map is a nontrivial algebra map; IsGalois/FD are fields).
- K is a finite Galois extension of F, with Fmod -> F -> K scalar tower.
- There is NO field map F -> Fmod in the data. The only canonical direction is
  algebraMap Fmod F (inclusion), and algebraMap F K / Fmod K.
- F is not "the Galois closure of Fmod" in general; it is a chosen finite Galois
  extension. K is the top field.
- T.arithmetic and I.initial.arithmetic are independent structure values. There is
  no theorem Fmod(T)=Fmod(I) or F(T)=F(I); equality must be supplied explicitly.

## 2. Completion direction

For a finite place P of F, the base place is
  comap (k := Fmod) P : NumberField.FinitePlace Fmod.
FinitePlaceExtension.completionMap (k := Fmod) P is a ring hom
  Completion (comap P) ->+* Completion P,
i.e. from the BASE completion to the EXTENSION completion. It is continuous and
injective (completionMap_injective), and on the dense base field it is the
algebra map (completionMap_coe). It is not surjective in general: Completion P is
a finite extension of Completion (comap P).

NormalizedCompletion place is definitionally Completion place
(FinitePlaceNormalizedCompletion:25), and
CommonPrimeCompletion place := NormalizedCompletion place.val
(FinitePlaceCommonPrimeCompletion:20). Thus the natural completion map is

  NormalizedCompletion (comap P) ->+* NormalizedCompletion P,

base to extension. There is no natural continuous ring map
NormalizedCompletion P -> NormalizedCompletion (comap P) in the data.

Consequence: for nontrivial F/Fmod, rootBase (completion of an F-place) is an
extension of the C3 Fmod-fiber completion, not equal to it.

## 3. qVFamTensorPlace vs C3LogShellPlaceL

qVFamTensorPlace (QVFam:47):
  FinitePlace T.arithmetic.F.
qVFamTensorPlaces (QVFam:63-66):
  FinitePlaceAtPrime T.arithmetic.F (qVFamTensorP T b).
C3LogShellPlaceL (Mzk1C3:35-37):
  FinitePlaceAtPrime I.initial.arithmetic.Fmod C3L.p.

Thus:
- qVFamTensorPlace is an F-place; C3LogShellPlaceL is an Fmod-place-at-prime.
- Even after identifying T.arithmetic.Fmod with I.initial.arithmetic.Fmod, the
  qVFam place is over F, not Fmod. The base Fmod-place is
  comap (k := Fmod) (qVFamTensorPlace T b), not qVFamTensorPlace itself.
- A necessary correspondence is:
    comap (k := Fmod) (qVFamTensorPlace T b) = (C3LogShellPlaceL C3L i).val
  after the Fmod base-field cast. This is a place-over relation, not an equality
  of places in the same field.
- The natural completion object is therefore an embedding
    CommonPrimeCompletion (C3LogShellPlaceL C3L i) ->+* rootBase T b
  via completionMap, not a ring equivalence or type equality.

## 4. Route B exact assumption list

Theorem-level (already available):
- algebraMap Fmod F is injective (field extension).
- comap (k := Fmod) P exists for every F-place P.
- completionMap (k := Fmod) P : NormalizedCompletion (comap P) ->+*
  NormalizedCompletion P is a continuous injective ring hom
  (FinitePlaceExtension.completionMap, continuous_completionMap,
  completionMap_injective, completionMap_coe).
- NormalizedCompletion/CommonPrimeCompletion unfold to Completion
  (rfl/definitional).

Must be explicit (not in tree):
1. Arithmetic-record relation:
   hArith : T.arithmetic = I.initial.arithmetic, or at least
   Fmod_eq : T.arithmetic.Fmod = I.initial.arithmetic.Fmod
   (plus cast of the algebra/F structures).
2. Place-over relation:
   hplace : comap (k := Fmod) (qVFamTensorPlace T b) =
     (C3LogShellPlaceL C3L i).val, after hFmod cast.
3. Index map:
   e : C3L.tensorIndex -> Bad (nativePlaceSelection T) or an equivalence, with
   the above hplace for e i.
4. If one insists on an EQUIVALENCE rootBase = CommonPrimeCompletion C3, then
   additionally F = Fmod (degree one / concrete Gaussian case) or a separate
   proof that the extension completion is the base. In general this is false.
5. For the S1487 concrete case only:
   S1487Arithmetic has Fmod=F=K=GaussianField, so F=Fmod is definitional; the
   only remaining work is a native T with that arithmetic and a place/index
   equality. No such native T is constructed in S1487.

## 5. Correct Route B bridge shape

For the general case, replace RouteBBridge's BaseCompletionEquivL (type equality)
by a completion embedding:

  structure BaseCompletionEmbeddingL
      (b : Bad (nativePlaceSelection T)) (i : C3L.tensorIndex) where
    base_eq : T.arithmetic.Fmod = I.initial.arithmetic.Fmod
    place_over : comap (k := Fmod) (qVFamTensorPlace T b) =
      (C3LogShellPlaceL C3L i).val  -- after base_eq cast
    -- the ring hom is then completionMap at the F-place
    embedding : CommonPrimeCompletion (C3LogShellPlaceL C3L i) ->+* rootBase T b

The embedding is constructed by completionMap after rewriting the base place to
the C3 place. This is proved from hplace + definitional unfolding, not assumed.

Only in the special case F=Fmod (e.g. S1487 Gaussian arithmetic, or a proved
degree-one extension) may one strengthen the embedding to an equivalence/type
equality rootBase = CommonPrimeCompletion C3.

## 6. Lean template

Definitional unfolding:
  theorem rootBase_eq_normalized
      (T) (b) :
      rootBase T b = NormalizedCompletion (qVFamTensorPlace T b) := rfl
  theorem c3Fiber_eq_normalized
      (I) (C3L) (i) :
      CommonPrimeCompletion (C3LogShellPlaceL C3L i) =
        NormalizedCompletion (C3LogShellPlaceL C3L i).val := rfl

Conditional embedding (schematic; after the Fmod cast and place-over equality):
  noncomputable def routeBCompletionEmbedding
      (hplace : comap (k := T.arithmetic.Fmod) (qVFamTensorPlace T b) =
        (C3LogShellPlaceL C3L i).val) :
      NormalizedCompletion (C3LogShellPlaceL C3L i) ->+*
        NormalizedCompletion (qVFamTensorPlace T b) := by
    -- rewrite the C3 Fmod-place to comap of the F-place,
    -- then apply FinitePlaceExtension.completionMap at the F-place
    exact completionMap (k := T.arithmetic.Fmod) (qVFamTensorPlace T b)

This is base-to-extension; do not state it as an equivalence. For the concrete
F=Fmod case, compose with the identity/place equality to obtain the equiv.

## 7. Verdict

- Fmod is the base field; F is a finite Galois extension; the only canonical map
  is Fmod -> F. No F -> Fmod.
- Completion has a natural base-to-extension continuous injective map
  completionMap; the extension completion is not equal to the base completion in
  general.
- qVFamTensorPlace is an F-place; C3LogShellPlaceL is an Fmod-place. The natural
  relation is "comap of the F-place equals the C3 Fmod-place", and then an
  embedding of completions, not an equality.
- RouteBBridge's BaseCompletionEquivL is too strong in general; only the
  F=Fmod/concrete-Gaussian case can use it. The correct general shape is
  BaseCompletionEmbeddingL.
- Explicit assumptions are: arithmetic/Fmod equality, place-over equality,
  index map; F=Fmod only for the equivalence specialization.
- No Lean file written; no compile claimed.
