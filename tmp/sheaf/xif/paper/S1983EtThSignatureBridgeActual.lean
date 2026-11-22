import tmp.sheaf.s1972.S1972CFSignatureAudit

/-!
# S1983: the [EtTh] type-name to OrbicurveSignature bridge

## The source statement

[EtTh] (*The Etale Theta Function and its Frobenioid-theoretic Manifestations*,
2008), Section 0, defines the type name (1, 1)^± (text lines 363--368):

    if C_2^log -> S_1^log is of type (1, 1), and the finite group of
    automorphisms is given by the action of "±1" [i.e., relative to the group
    structure of the underlying elliptic curve of C_2^log -> S_1^log], then the
    resulting stable log orbicurve will be referred to as being of type (1, 1)^±.

Definition 2.1 (text lines 2332--2432) introduces (1, l-tors) and
(1, l-tors)^± by the same scheme: the degree-l cover X^log -> X^log (all cusps
rational) and the stack-theoretic quotient C^log := [X^log / ι] by the elliptic
involution ι ("multiplication by −1").  So (1,1)^± is a *construction type*:
the stack quotient of a type-(1,1) curve by ±1.  It is not a numerical
signature in the sense of Iut.OrbicurveSignature.

IUT I, Definition 3.1(b) says exactly this for C_F:

    X_F -> C_F for the hyperbolic orbicurve obtained by forming the
    stack-theoretic quotient of X_F by the unique F-involution "-1" of X_F

and 3.1(d),(f) add C_K := C_F ×_F K (the K-core) and the degree-l covers
C_K^-> -> C_K, X_K^-> -> X_K of types (1,l-tors)^±, (1,l-tors).

## The honest signature

From the paper data (X_F is of type (1,1); the 2-torsion is F-rational by
3.1(b); the origin is removed) the honest orbifold signature of
C_F = [X_F/{±1}] is (0; [2,2,2]; 1), of orbifold Euler characteristic -1/2:
three order-two stacky points at the images of the three nonzero two-torsion
points, one cusp at the image of the origin.  On the actual S1726 model S1964
proves exactly this fixed locus.  The K-core C_K has the same type name (1,1)^±
and the same honest signature; the degree-l covers have honest signatures
(1; []; l) and (0; [2,2,2]; (l+1)/2).

## What this file constructs (definition + theorem, no axiom)

* EtThType: the four [EtTh] type names as a syntax, with EtThType.prequotient
  (the signature of the curve being quotiented) and EtThType.isSignQuotient.
* SignQuotientInput / SignQuotientInput.quotient: the ±1 stack quotient at the
  level of signatures, from the geometric data (genus one, no stacky points,
  an odd number of cusps of which exactly one -- the origin -- is fixed, and
  rational 2-torsion).  The quotient signature is (0; [2,2,2]; (n+1)/2).
* SignQuotientInput.quotient_unique: the honest signature is *forced* by
  (i) coarse genus zero, (ii) the three order-two stacky points, and (iii) the
  Euler characteristic of a degree-two ±1-torsor.  Nothing is chosen.
* etthSignature : EtThType -> Iut.OrbicurveSignature: the bridge.  For the ^±
  names it is the ±1 quotient of the pre-quotient curve's signature; for the
  other names it is the curve itself.
* Comparison theorems: etthSignature (1,1)^± = (0;[2,2,2];1) equals S1964's
  honest signature (paperCF); the Euler characteristic relations
  2·χ((1,1)^±) = χ((1,1)), χ((1,l-tors)) = l·χ((1,1)),
  2·χ((1,l-tors)^±) = χ((1,l-tors)); hyperbolicity of all four types; and the
  label mismatch theorems.  In particular
  sourceTypeOneOnePlusMinus = (1; [2]; 0) is a *transcription error*, not a
  second convention (genus, stacky orders and punctures are all wrong; only
  χ = -1/2 happens to coincide), the D-clause label
  SourceOrbicurveSignature.typeOneOne = (1; []; 1) is the pre-quotient X_F
  signature, and the K-side labels (1; [l]; 0), (1; [2,l]; 0) are attached to
  the wrong objects (the K-cores) with wrong values.
* paperCFType, paperCKType, paperXFType, paperCKTorsType: the paper's objects
  typed by [EtTh], and their honest signatures.
* S1983EtThCF, S1983FirstMissing: the paper target typed by the [EtTh] name,
  and its exact missing datum.

## The exact missing datum

Two gaps, both recorded below as Lean statements and neither postulated:

1. S1964FirstMissing (S1964): the quotient stack [X_F/{±1}] -- the pointwise
   lax colimit of the sign action on the Cat-valued etale stack, its
   functoriality, Pseudofunctor.IsStack (stackification) and the bicategorical
   universal property.  Without it there is no cF at all.
2. S1983SignatureNotForcedByFiber: HyperbolicOrbicurve.signature is an
   *inserted* field, not a function of the stack.  Hence even with the quotient
   constructed, the equality cF.signature = etthSignature (1,1)^± must be *data*
   of the target, unless the production signature field is changed to be
   computed from geometry -- which is out of scope here.

A third, purely geometric statement is isolated for the genus = 0 component:
S1983CoarseQuotientIsAffineLine, the statement that the invariant ring of the
actual affine coordinate ring under [-1] is exactly K[x] (equivalently: the
coarse quotient of X_F by ±1 is the affine line, so its projective completion
is P^1 with one cusp).  Its easy inclusion (K[x] is fixed) is proved
(S1983PolyToCoordinateRing_mem); the reverse inclusion needs the normal form
R' = K[x] ⊕ K[x]·y, which is not in the tree.

This file introduces no axiom, no sorry, no admit and no postulated quotient.
The #print axioms block at the end records the footprint of every main
declaration (propext, Classical.choice, Quot.sound).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S1983EtThSignatureBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.S1972CFSignatureAudit
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual
open LeanFormal.IUT.XiFPaper.S1964QuotientCFActual

universe u

/-! ## 1. The [EtTh] type names -/

/-- The four [EtTh] type names of the paper's orbicurves:

* oneOne -- type (1,1): a once-punctured elliptic curve ([EtTh], Section 0);
* oneOnePlusMinus -- type (1,1)^±: the stack-theoretic quotient of a type-(1,1)
  curve by the action of ±1 ([EtTh], Section 0);
* oneLTors l -- type (1,l-tors): the degree-l cover X^log -> X^log of [EtTh],
  Definition 2.1;
* oneLTorsPlusMinus l -- type (1,l-tors)^±: the same quotient construction
  applied to that cover ([EtTh], Definition 2.1).

These are *construction* type names, not numerical signatures. -/
inductive EtThType : Type where
  | oneOne : EtThType
  | oneOnePlusMinus : EtThType
  | oneLTors (l : PrimeGeFive) : EtThType
  | oneLTorsPlusMinus (l : PrimeGeFive) : EtThType

namespace EtThType

/-- Whether the type name is one of the ^± names, i.e. whether it is defined by
forming the stack-theoretic quotient by ±1. -/
def isSignQuotient : EtThType → Bool
  | oneOne => false
  | oneOnePlusMinus => true
  | oneLTors _ => false
  | oneLTorsPlusMinus _ => true

theorem isSignQuotient_oneOne : isSignQuotient oneOne = false := rfl

theorem isSignQuotient_oneOnePlusMinus :
    isSignQuotient oneOnePlusMinus = true := rfl

theorem isSignQuotient_oneLTors (l : PrimeGeFive) :
    isSignQuotient (oneLTors l) = false := rfl

theorem isSignQuotient_oneLTorsPlusMinus (l : PrimeGeFive) :
    isSignQuotient (oneLTorsPlusMinus l) = true := rfl

/-- The curve of which the type name is (or is not) the ±1 stack quotient: for
(1,1)^± the pre-quotient is a type-(1,1) curve, for (1,l-tors)^± it is the
type-(1,l-tors) cover.  For the non-^± names this is the curve itself.  This
records the [EtTh] construction at the level of signatures. -/
def prequotient : EtThType → Iut.OrbicurveSignature
  | oneOne => Iut.OrbicurveSignature.oncePuncturedElliptic
  | oneOnePlusMinus => Iut.OrbicurveSignature.oncePuncturedElliptic
  | oneLTors l => honestXKTors l
  | oneLTorsPlusMinus l => honestXKTors l

@[simp] theorem prequotient_oneOne :
    prequotient oneOne = Iut.OrbicurveSignature.oncePuncturedElliptic := rfl

@[simp] theorem prequotient_oneOnePlusMinus :
    prequotient oneOnePlusMinus =
      Iut.OrbicurveSignature.oncePuncturedElliptic := rfl

@[simp] theorem prequotient_oneLTors (l : PrimeGeFive) :
    prequotient (oneLTors l) = honestXKTors l := rfl

@[simp] theorem prequotient_oneLTorsPlusMinus (l : PrimeGeFive) :
    prequotient (oneLTorsPlusMinus l) = honestXKTors l := rfl

end EtThType

/-! ## 2. Euler characteristics of the two signature shapes -/

/-- A genus-zero signature with three order-two stacky points has orbifold
Euler characteristic 1/2 - punctures. -/
theorem eulerCharacteristic_eq_half_sub_punctures
    (s : Iut.OrbicurveSignature) (hg : s.genus = 0)
    (hs : s.stackyOrders = [2, 2, 2]) :
    s.eulerCharacteristic = 1 / 2 - (s.punctures : ℚ) := by
  have hsum :
      (List.map (fun m : ℕ => 1 - (1 : ℚ) / m) [2, 2, 2]).sum = 3 / 2 := by
    norm_num
  unfold Iut.OrbicurveSignature.eulerCharacteristic
  rw [hg, hs, hsum]
  push_cast
  ring

/-- A genus-one signature with no stacky points has orbifold Euler
characteristic - punctures. -/
theorem eulerCharacteristic_eq_neg_punctures
    (s : Iut.OrbicurveSignature) (hg : s.genus = 1)
    (hs : s.stackyOrders = []) :
    s.eulerCharacteristic = -(s.punctures : ℚ) := by
  have hsum :
      (List.map (fun m : ℕ => 1 - (1 : ℚ) / m) ([] : List ℕ)).sum = 0 := by
    simp
  unfold Iut.OrbicurveSignature.eulerCharacteristic
  rw [hg, hs, hsum]
  push_cast
  ring

/-! ## 3. The ±1 stack quotient at the level of signatures

[EtTh], Section 0, builds (1,1)^± from a type-(1,1) curve by the quotient of
±1.  The geometric input needed for the signature of that quotient is:

* the pre-quotient is a genus-one curve with no stacky points;
* the involution -1 has exactly one fixed cusp (the origin) and pairs the
  others, so the number n of cusps is odd and the quotient has 1 + (n-1)/2
  cusps;
* the two-torsion is rational, so the three nonzero two-torsion points give
  three order-two stacky points in the quotient.

SignQuotientInput records exactly this input and SignQuotientInput.quotient is
the resulting signature. -/

/-- The geometric input of the [EtTh] ±1 quotient construction, at the level of
signatures. -/
structure SignQuotientInput where
  /-- The signature of the curve being quotiented. -/
  source : Iut.OrbicurveSignature
  /-- The pre-quotient has genus one. -/
  genus_eq : source.genus = 1
  /-- The pre-quotient has no stacky points. -/
  stackyOrders_eq : source.stackyOrders = []
  /-- An odd number of cusps, exactly one of which (the origin) is fixed. -/
  punctures_odd : Odd source.punctures

namespace SignQuotientInput

/-- The honest signature of the [EtTh] ±1 stack quotient: genus zero, the three
order-two stacky points coming from the rational two-torsion, and (n+1)/2
cusps. -/
def quotient (I : SignQuotientInput) : Iut.OrbicurveSignature where
  genus := 0
  stackyOrders := [2, 2, 2]
  punctures := (I.source.punctures + 1) / 2
  stackyOrders_ge_two := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide

@[simp] theorem quotient_genus (I : SignQuotientInput) : I.quotient.genus = 0 :=
  rfl

@[simp] theorem quotient_stackyOrders (I : SignQuotientInput) :
    I.quotient.stackyOrders = [2, 2, 2] :=
  rfl

@[simp] theorem quotient_punctures (I : SignQuotientInput) :
    I.quotient.punctures = (I.source.punctures + 1) / 2 :=
  rfl

/-- The quotient is a degree-two ±1-torsor: 2·χ(quotient) = χ(source). -/
theorem quotient_eulerCharacteristic (I : SignQuotientInput) :
    2 * I.quotient.eulerCharacteristic = I.source.eulerCharacteristic := by
  have hsrc :=
    eulerCharacteristic_eq_neg_punctures I.source I.genus_eq I.stackyOrders_eq
  have hquot := eulerCharacteristic_eq_half_sub_punctures I.quotient
    (quotient_genus I) (quotient_stackyOrders I)
  obtain ⟨k, hk⟩ := I.punctures_odd
  have hp : I.quotient.punctures = k + 1 := by
    rw [quotient_punctures, hk]
    omega
  rw [hquot, hsrc, hp, hk]
  push_cast
  ring

/-- The quotient of a curve with at least one cusp is a hyperbolic orbicurve. -/
theorem quotient_hyperbolic (I : SignQuotientInput) :
    I.quotient.IsHyperbolic := by
  unfold Iut.OrbicurveSignature.IsHyperbolic
  have hquot := eulerCharacteristic_eq_half_sub_punctures I.quotient
    (quotient_genus I) (quotient_stackyOrders I)
  obtain ⟨k, hk⟩ := I.punctures_odd
  have hp : I.quotient.punctures = k + 1 := by
    rw [quotient_punctures, hk]
    omega
  rw [hquot, hp]
  have hk0 : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
  push_cast
  linarith

/-- *The honest signature is forced, not chosen.*  Any signature with
(i) coarse genus zero, (ii) the three order-two stacky points supplied by the
rational two-torsion and (iii) the Euler characteristic of a degree-two
±1-torsor over the source is the quotient signature. -/
theorem quotient_unique (I : SignQuotientInput) (T : Iut.OrbicurveSignature)
    (hg : T.genus = 0) (hs : T.stackyOrders = [2, 2, 2])
    (heuler : 2 * T.eulerCharacteristic = I.source.eulerCharacteristic) :
    T = I.quotient := by
  apply Iut.OrbicurveSignature.ext
  · rw [hg]
    rfl
  · rw [hs]
    rfl
  · rw [quotient_punctures]
    have hT := eulerCharacteristic_eq_half_sub_punctures T hg hs
    have hsrc :=
      eulerCharacteristic_eq_neg_punctures I.source I.genus_eq I.stackyOrders_eq
    rw [hT, hsrc] at heuler
    have h2 : (2 : ℚ) * (T.punctures : ℚ) = (I.source.punctures : ℚ) + 1 := by
      linarith
    have h2' : 2 * T.punctures = I.source.punctures + 1 := by
      exact_mod_cast h2
    omega

end SignQuotientInput

/-- The ±1 quotient input for the [EtTh] type (1,1): the once-punctured
elliptic curve; its unique cusp is the origin, which is fixed by -1. -/
def signQuotientInputOncePunctured : SignQuotientInput where
  source := Iut.OrbicurveSignature.oncePuncturedElliptic
  genus_eq := rfl
  stackyOrders_eq := rfl
  punctures_odd := ⟨0, rfl⟩

/-- The ±1 quotient input for the [EtTh] type (1,l-tors): the degree-l cover of
the once-punctured elliptic curve, with l rational cusps, one of which is fixed
by the involution. -/
def signQuotientInputLTors (l : PrimeGeFive) : SignQuotientInput where
  source := honestXKTors l
  genus_eq := rfl
  stackyOrders_eq := rfl
  punctures_odd := l.odd

/-! ## 4. The bridge definition -/

/-- *The [EtTh] type-name to OrbicurveSignature bridge.*  The honest orbifold
signature attached to each [EtTh] type name:

* (1,1)        |-> (1; []; 1),
* (1,1)^±      |-> (0; [2,2,2]; 1),
* (1,l-tors)   |-> (1; []; l),
* (1,l-tors)^± |-> (0; [2,2,2]; (l+1)/2).

The ^± values are computed by the ±1 quotient construction of Section 3, not
chosen. -/
def etthSignature : EtThType → Iut.OrbicurveSignature
  | EtThType.oneOne => Iut.OrbicurveSignature.oncePuncturedElliptic
  | EtThType.oneOnePlusMinus => signQuotientInputOncePunctured.quotient
  | EtThType.oneLTors l => honestXKTors l
  | EtThType.oneLTorsPlusMinus l => (signQuotientInputLTors l).quotient

/-- The ^± names are, definitionally, the ±1 quotient of their pre-quotient. -/
theorem etthSignature_quotient_shape :
    etthSignature EtThType.oneOnePlusMinus =
        signQuotientInputOncePunctured.quotient ∧
      (∀ l : PrimeGeFive, etthSignature (EtThType.oneLTorsPlusMinus l) =
        (signQuotientInputLTors l).quotient) :=
  ⟨rfl, fun _ => rfl⟩

@[simp] theorem etthSignature_oneOne :
    etthSignature EtThType.oneOne =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  rfl

@[simp] theorem etthSignature_oneOne_genus :
    (etthSignature EtThType.oneOne).genus = 1 :=
  rfl

@[simp] theorem etthSignature_oneOne_stackyOrders :
    (etthSignature EtThType.oneOne).stackyOrders = [] :=
  rfl

@[simp] theorem etthSignature_oneOne_punctures :
    (etthSignature EtThType.oneOne).punctures = 1 :=
  rfl

@[simp] theorem etthSignature_oneOnePlusMinus_genus :
    (etthSignature EtThType.oneOnePlusMinus).genus = 0 :=
  rfl

@[simp] theorem etthSignature_oneOnePlusMinus_stackyOrders :
    (etthSignature EtThType.oneOnePlusMinus).stackyOrders = [2, 2, 2] :=
  rfl

/-- The honest (1,1)^± signature has one cusp: (1+1)/2 = 1. -/
theorem etthSignature_oneOnePlusMinus_punctures :
    (etthSignature EtThType.oneOnePlusMinus).punctures = 1 := by
  decide

@[simp] theorem etthSignature_oneLTors_genus (l : PrimeGeFive) :
    (etthSignature (EtThType.oneLTors l)).genus = 1 :=
  rfl

@[simp] theorem etthSignature_oneLTors_stackyOrders (l : PrimeGeFive) :
    (etthSignature (EtThType.oneLTors l)).stackyOrders = [] :=
  rfl

@[simp] theorem etthSignature_oneLTors_punctures (l : PrimeGeFive) :
    (etthSignature (EtThType.oneLTors l)).punctures = l.value :=
  rfl

@[simp] theorem etthSignature_oneLTorsPlusMinus_genus (l : PrimeGeFive) :
    (etthSignature (EtThType.oneLTorsPlusMinus l)).genus = 0 :=
  rfl

@[simp] theorem etthSignature_oneLTorsPlusMinus_stackyOrders
    (l : PrimeGeFive) :
    (etthSignature (EtThType.oneLTorsPlusMinus l)).stackyOrders = [2, 2, 2] :=
  rfl

@[simp] theorem etthSignature_oneLTorsPlusMinus_punctures
    (l : PrimeGeFive) :
    (etthSignature (EtThType.oneLTorsPlusMinus l)).punctures =
      (l.value + 1) / 2 :=
  rfl

/-- *The bridge theorem for C_F*: the [EtTh] type (1,1)^± has honest signature
(0; [2,2,2]; 1) -- S1964's honest quotient signature. -/
theorem etthSignature_oneOnePlusMinus_eq_honestSignature :
    etthSignature EtThType.oneOnePlusMinus = S1964HonestQuotientSignature := by
  apply Iut.OrbicurveSignature.ext
  · rw [etthSignature_oneOnePlusMinus_genus]
    rfl
  · rw [etthSignature_oneOnePlusMinus_stackyOrders]
    rfl
  · rw [etthSignature_oneOnePlusMinus_punctures]
    rfl

/-- The same statement with S1972's name paperCF for the honest signature. -/
theorem etthSignature_oneOnePlusMinus_eq_paperCF :
    etthSignature EtThType.oneOnePlusMinus = paperCF :=
  etthSignature_oneOnePlusMinus_eq_honestSignature

/-- *The bridge theorem for the (1,1) type*: it is exactly the
once-punctured-elliptic signature, which is the D-clause label
SourceOrbicurveSignature.typeOneOne transported to OrbicurveSignature. -/
theorem etthSignature_oneOne_eq_legacyTypeOneOne :
    etthSignature EtThType.oneOne =
      toIutSignature SourceOrbicurveSignature.typeOneOne := by
  apply Iut.OrbicurveSignature.ext <;> rfl

/-- *The bridge theorem for the (1,l-tors) type*: the honest signature of the
degree-l cover is (1; []; l). -/
theorem etthSignature_oneLTors_eq_honestXKTors (l : PrimeGeFive) :
    etthSignature (EtThType.oneLTors l) = honestXKTors l :=
  rfl

/-- *The bridge theorem for the (1,l-tors)^± type*: the honest signature of the
degree-l quotient orbicurve is (0; [2,2,2]; (l+1)/2). -/
theorem etthSignature_oneLTorsPlusMinus_eq_honestCKTors (l : PrimeGeFive) :
    etthSignature (EtThType.oneLTorsPlusMinus l) = honestCKTors l := by
  apply Iut.OrbicurveSignature.ext <;> rfl

/-! ## 5. Hyperbolicity of the four types -/

theorem etthSignature_oneOne_hyperbolic :
    (etthSignature EtThType.oneOne).IsHyperbolic :=
  Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic

theorem etthSignature_oneOnePlusMinus_hyperbolic :
    (etthSignature EtThType.oneOnePlusMinus).IsHyperbolic :=
  SignQuotientInput.quotient_hyperbolic signQuotientInputOncePunctured

theorem etthSignature_oneLTors_hyperbolic (l : PrimeGeFive) :
    (etthSignature (EtThType.oneLTors l)).IsHyperbolic :=
  honestXKTors_hyperbolic l

theorem etthSignature_oneLTorsPlusMinus_hyperbolic (l : PrimeGeFive) :
    (etthSignature (EtThType.oneLTorsPlusMinus l)).IsHyperbolic :=
  SignQuotientInput.quotient_hyperbolic (signQuotientInputLTors l)

/-- Every [EtTh] type name has a hyperbolic honest signature. -/
theorem etthSignature_isHyperbolic (t : EtThType) :
    (etthSignature t).IsHyperbolic := by
  cases t with
  | oneOne => exact etthSignature_oneOne_hyperbolic
  | oneOnePlusMinus => exact etthSignature_oneOnePlusMinus_hyperbolic
  | oneLTors l => exact etthSignature_oneLTors_hyperbolic l
  | oneLTorsPlusMinus l => exact etthSignature_oneLTorsPlusMinus_hyperbolic l

/-! ## 6. Euler-characteristic relations

These are the orbifold Riemann-Hurwitz relations of the two covering towers:
X_F -> C_F is a degree-two ±1-torsor, and X_K^-> -> X_K, C_K^-> -> C_K are
degree-l covers. -/

/-- χ(C_F) = -1/2. -/
theorem etthSignature_oneOnePlusMinus_euler :
    (etthSignature EtThType.oneOnePlusMinus).eulerCharacteristic = -1 / 2 := by
  have h := eulerCharacteristic_eq_half_sub_punctures
    (etthSignature EtThType.oneOnePlusMinus) rfl rfl
  rw [h, etthSignature_oneOnePlusMinus_punctures]
  norm_num

/-- The degree-two {±1}-torsor X_F -> C_F: 2·χ(C_F) = χ(X_F) = -1. -/
theorem etthSignature_oneOnePlusMinus_euler_two_mul :
    2 * (etthSignature EtThType.oneOnePlusMinus).eulerCharacteristic =
      (etthSignature EtThType.oneOne).eulerCharacteristic := by
  have hX : (etthSignature EtThType.oneOne).eulerCharacteristic = -1 :=
    Iut.OrbicurveSignature.oncePuncturedElliptic_eulerCharacteristic
  rw [etthSignature_oneOnePlusMinus_euler, hX]
  norm_num

/-- χ(1,l-tors) = -l. -/
theorem etthSignature_oneLTors_euler (l : PrimeGeFive) :
    (etthSignature (EtThType.oneLTors l)).eulerCharacteristic =
      -(l.value : ℚ) :=
  honestXKTors_euler l

/-- χ((1,l-tors)^±) = -l/2. -/
theorem etthSignature_oneLTorsPlusMinus_euler (l : PrimeGeFive) :
    (etthSignature (EtThType.oneLTorsPlusMinus l)).eulerCharacteristic =
      -(l.value : ℚ) / 2 :=
  honestCKTors_euler l

/-- The degree-l cover X_K^-> -> X_K multiplies χ by l. -/
theorem etthSignature_oneLTors_euler_l (l : PrimeGeFive) :
    (etthSignature (EtThType.oneLTors l)).eulerCharacteristic =
      (l.value : ℚ) * (etthSignature EtThType.oneOne).eulerCharacteristic := by
  have hX : (etthSignature EtThType.oneOne).eulerCharacteristic = -1 :=
    Iut.OrbicurveSignature.oncePuncturedElliptic_eulerCharacteristic
  rw [etthSignature_oneLTors_euler, hX]
  ring

/-- The degree-l cover C_K^-> -> C_K multiplies χ by l. -/
theorem etthSignature_oneLTorsPlusMinus_euler_l (l : PrimeGeFive) :
    (etthSignature (EtThType.oneLTorsPlusMinus l)).eulerCharacteristic =
      (l.value : ℚ) *
        (etthSignature EtThType.oneOnePlusMinus).eulerCharacteristic := by
  rw [etthSignature_oneLTorsPlusMinus_euler, etthSignature_oneOnePlusMinus_euler]
  ring

/-- The degree-two {±1}-torsor X_K^-> -> C_K^->. -/
theorem etthSignature_oneLTors_euler_two_mul (l : PrimeGeFive) :
    2 * (etthSignature (EtThType.oneLTorsPlusMinus l)).eulerCharacteristic =
      (etthSignature (EtThType.oneLTors l)).eulerCharacteristic := by
  rw [etthSignature_oneLTorsPlusMinus_euler, etthSignature_oneLTors_euler]
  ring

/-! ## 7. The Lean labels versus the honest [EtTh] signatures

The tree carries two C_F labels, sourceTypeOneOnePlusMinus = (1; [2]; 0) and
SourceOrbicurveSignature.typeOneOne = (1; []; 1), and two K-side labels
(1; [l]; 0) and (1; [2,l]; 0).  None of them is the honest [EtTh] signature. -/

/-- *The (1,1)^± label (1; [2]; 0) is a transcription error, not a second
convention*: genus 1 versus 0. -/
theorem etthSignature_oneOnePlusMinus_ne_sourceTypeOneOnePlusMinus :
    etthSignature EtThType.oneOnePlusMinus ≠ sourceTypeOneOnePlusMinus := by
  intro h
  have hg : (etthSignature EtThType.oneOnePlusMinus).genus =
      sourceTypeOneOnePlusMinus.genus :=
    congrArg Iut.OrbicurveSignature.genus h
  rw [etthSignature_oneOnePlusMinus_genus] at hg
  exact Nat.zero_ne_one hg

/-- The error is invisible to Euler-characteristic tests: both values are
-1/2. -/
theorem etthSignature_oneOnePlusMinus_euler_eq_paperLabel :
    (etthSignature EtThType.oneOnePlusMinus).eulerCharacteristic =
      sourceTypeOneOnePlusMinus.eulerCharacteristic := by
  rw [etthSignature_oneOnePlusMinus_euler, paperLabelCF_euler]

/-- The D-clause label (1; []; 1) is the pre-quotient X_F signature, not the
quotient signature: genus 1 versus 0. -/
theorem etthSignature_oneOnePlusMinus_ne_legacyTypeOneOne :
    etthSignature EtThType.oneOnePlusMinus ≠
      toIutSignature SourceOrbicurveSignature.typeOneOne := by
  intro h
  have hg : (etthSignature EtThType.oneOnePlusMinus).genus =
      (toIutSignature SourceOrbicurveSignature.typeOneOne).genus :=
    congrArg Iut.OrbicurveSignature.genus h
  rw [etthSignature_oneOnePlusMinus_genus, toIutSignature_genus] at hg
  have h1 : SourceOrbicurveSignature.typeOneOne.genus = 1 := rfl
  rw [h1] at hg
  exact Nat.zero_ne_one hg

/-- The two C_F labels of the tree also disagree with each other. -/
theorem paperLabelCF_ne_legacyTypeOneOne' :
    sourceTypeOneOnePlusMinus ≠
      toIutSignature SourceOrbicurveSignature.typeOneOne :=
  paperLabelCF_ne_legacyTypeOneOne

/-- The K-side label (1; [l]; 0) is not the honest (1,l-tors) signature
(1; []; l): no stacky points and l cusps. -/
theorem etthSignature_oneLTors_ne_legacyTypeOneLTorsion (l : PrimeGeFive) :
    etthSignature (EtThType.oneLTors l) ≠
      toIutSignature (SourceOrbicurveSignature.typeOneLTorsion l) := by
  intro h
  have hp : (etthSignature (EtThType.oneLTors l)).punctures =
      (toIutSignature (SourceOrbicurveSignature.typeOneLTorsion l)).punctures :=
    congrArg Iut.OrbicurveSignature.punctures h
  rw [etthSignature_oneLTors_punctures, toIutSignature_punctures] at hp
  have h0 : (SourceOrbicurveSignature.typeOneLTorsion l).punctures = 0 := rfl
  rw [h0] at hp
  have h5 := l.ge_five
  omega

/-- The K-side label (1; [2,l]; 0) is not the honest (1,l-tors)^± signature
(0; [2,2,2]; (l+1)/2): genus 1 versus 0. -/
theorem etthSignature_oneLTorsPlusMinus_ne_legacyTypeOneLTorsionPlusMinus
    (l : PrimeGeFive) :
    etthSignature (EtThType.oneLTorsPlusMinus l) ≠
      toIutSignature
        (SourceOrbicurveSignature.typeOneLTorsionPlusMinus l) := by
  intro h
  have hg : (etthSignature (EtThType.oneLTorsPlusMinus l)).genus =
      (toIutSignature
        (SourceOrbicurveSignature.typeOneLTorsionPlusMinus l)).genus :=
    congrArg Iut.OrbicurveSignature.genus h
  rw [etthSignature_oneLTorsPlusMinus_genus, toIutSignature_genus] at hg
  have h1 :
      (SourceOrbicurveSignature.typeOneLTorsionPlusMinus l).genus = 1 := rfl
  rw [h1] at hg
  exact Nat.zero_ne_one hg

/-- The honest C_F signature is not the coarse quotient (0; []; 1): the three
order-two stacky points are essential (the coarse quotient has Euler
characteristic 1, hence is not hyperbolic). -/
theorem etthSignature_oneOnePlusMinus_ne_coarse :
    etthSignature EtThType.oneOnePlusMinus ≠ S1964CoarseQuotientSignature := by
  intro h
  apply coarseCF_ne_paperCF
  rw [← etthSignature_oneOnePlusMinus_eq_paperCF, h]

/-- *The K-core is not the (1,l-tors)^± object.*  The paper's K-core
C_K = C_F ×_F K is of type (1,1)^± (base change preserves the type), while
(1,l-tors)^± names the degree-l cover C_K^->.  Their honest signatures differ:
(0;[2,2,2];1) versus (0;[2,2,2];(l+1)/2). -/
theorem etthSignature_oneLTorsPlusMinus_ne_oneOnePlusMinus
    (l : PrimeGeFive) :
    etthSignature (EtThType.oneLTorsPlusMinus l) ≠
      etthSignature EtThType.oneOnePlusMinus := by
  intro h
  have hp := congrArg Iut.OrbicurveSignature.punctures h
  rw [etthSignature_oneLTorsPlusMinus_punctures,
    etthSignature_oneOnePlusMinus_punctures] at hp
  have h5 := l.ge_five
  omega

/-! ## 8. The paper's objects typed by [EtTh] -/

/-- The [EtTh] type of X_F (IUT I, Definition 3.1(b)): a once-punctured
elliptic curve, type (1,1). -/
def paperXFType : EtThType := EtThType.oneOne

/-- The [EtTh] type of C_F = [X_F/{±1}] (IUT I, Definition 3.1(b)):
type (1,1)^±. -/
def paperCFType : EtThType := EtThType.oneOnePlusMinus

/-- The [EtTh] type of the K-core C_K := C_F ×_F K (IUT I, Definition 3.1(d)):
base change along F -> K preserves the type, so C_K is again of type (1,1)^±. -/
def paperCKType : EtThType := EtThType.oneOnePlusMinus

/-- The [EtTh] type of the degree-l cover C_K^-> of IUT I, Definition
3.1(d),(f): type (1,l-tors)^±. -/
def paperCKTorsType (l : PrimeGeFive) : EtThType :=
  EtThType.oneLTorsPlusMinus l

/-- The honest signature of X_F. -/
theorem paperXF_signature :
    etthSignature paperXFType = Iut.OrbicurveSignature.oncePuncturedElliptic :=
  rfl

/-- The honest signature of C_F: (0; [2,2,2]; 1). -/
theorem paperCF_signature :
    etthSignature paperCFType = S1964HonestQuotientSignature :=
  etthSignature_oneOnePlusMinus_eq_honestSignature

/-- The honest signature of the K-core C_K: the same (0; [2,2,2]; 1) as C_F. -/
theorem paperCK_signature :
    etthSignature paperCKType = S1964HonestQuotientSignature :=
  etthSignature_oneOnePlusMinus_eq_honestSignature

/-- The honest signature of C_K^->: (0; [2,2,2]; (l+1)/2). -/
theorem paperCKTors_signature (l : PrimeGeFive) :
    etthSignature (paperCKTorsType l) = honestCKTors l :=
  rfl

/-- The production sign-quotient contract's cF metadata cannot be the honest
[EtTh] signature: SourceSignQuotientData.cF_genus forces genus 1. -/
theorem sourceSignQuotientData_cF_ne_etth
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.cF.signature ≠ etthSignature EtThType.oneOnePlusMinus := by
  simpa [etthSignature_oneOnePlusMinus_eq_paperCF] using
    sourceSignQuotientData_cF_ne_paperCF S

/-- The contract's cK = cF × K is the K-core, but its metadata is the
(1,l-tors)^± label; it is not the honest core signature either. -/
theorem sourceSignQuotientData_cK_ne_etth
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.cK.signature ≠ etthSignature EtThType.oneOnePlusMinus := by
  simpa [etthSignature_oneOnePlusMinus_eq_paperCF] using
    sourceSignQuotientData_cK_ne_paperCF S

/-- By contrast the contract's xF is correctly typed: it is the (1,1)
object. -/
theorem sourceSignQuotientData_xF_eq_etth
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (S : SourceSignQuotientData A) :
    S.xF.signature = etthSignature EtThType.oneOne := by
  rw [etthSignature_oneOne]
  exact sourceSignQuotientData_xF_eq_oncePunctured S

/-! ## 9. The paper target typed by [EtTh] and the exact first missing -/

/-- The paper-faithful C_F target typed by [EtTh]: the quotient orbicurve
C_F = X_F/{±1} carrying its honest (1,1)^± signature (0; [2,2,2]; 1), the
sign-invariant quotient morphism, and the bicategorical universal property. -/
abbrev S1983EtThCF (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) :=
  S1964CFQuotientAt l A (etthSignature EtThType.oneOnePlusMinus)
    etthSignature_oneOnePlusMinus_hyperbolic

/-- Targets with equal signature labels have the same inhabitedness: the label
is a parameter, and the two quotient-at structures have the same fields. -/
theorem S1983CFQuotientAt_congr {s t : Iut.OrbicurveSignature} (h : s = t)
    (hs : s.IsHyperbolic) (ht : t.IsHyperbolic) (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    Nonempty (S1964CFQuotientAt l A s hs) ↔
      Nonempty (S1964CFQuotientAt l A t ht) := by
  cases h
  exact Iff.rfl

/-- The [EtTh]-typed target is exactly S1964's honest-labelled target: the two
signatures are the same honest signature. -/
theorem S1983EtThCF_iff_honest (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    Nonempty (S1983EtThCF l A) ↔ Nonempty (S1964HonestCFQuotient l A) :=
  S1983CFQuotientAt_congr etthSignature_oneOnePlusMinus_eq_honestSignature
    etthSignature_oneOnePlusMinus_hyperbolic
    S1964HonestQuotientSignature_hyperbolic l A

/-- The existence of the honest [EtTh]-typed C_F is the existence of the
quotient structure with the honest label. -/
def S1983FirstMissing (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) : Prop :=
  Nonempty (S1983EtThCF l A)

theorem S1983FirstMissing_iff_honest (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) :
    S1983FirstMissing l A ↔ Nonempty (S1964HonestCFQuotient l A) :=
  S1983EtThCF_iff_honest l A

/-- *The first gap*: the [EtTh]-typed C_F requires the quotient stack, i.e.
S1964's S1964FirstMissing. -/
theorem S1964FirstMissing_ofS1983 {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (h : S1983FirstMissing l A) : S1964FirstMissing l A :=
  S1964FirstMissing_ofHonest ((S1983FirstMissing_iff_honest l A).mp h)

/-- *The second gap, as a Lean theorem*: the signature is not a function of the
etale stack fiber.  Any fiber can carry any prescribed hyperbolic signature
(realizedHyperbolicOrbicurve), so a theorem of the form "the constructed
quotient has signature (0; [2,2,2]; 1)" is not derivable from the fiber alone.
Concretely, over any fiber there is a hyperbolic orbicurve whose signature is
the transcription label (1; [2]; 0) instead of the honest signature.  Hence the
honest signature must either be part of the target data (as in S1983EtThCF), or
the production signature field must be changed to be computed from geometry. -/
theorem S1983SignatureNotForcedByFiber {F : Type u} [Field F]
    (fiber : Iut.EtaleStackPseudofunctor F)
    (isStack : fiber.IsStack (Iut.SchemeOverField.etaleTopology F)) :
    ∃ X : Iut.HyperbolicOrbicurve F,
      X.stack.fiber = fiber ∧
        X.signature ≠ etthSignature EtThType.oneOnePlusMinus := by
  refine
    ⟨realizedHyperbolicOrbicurve F fiber isStack sourceTypeOneOnePlusMinus
      sourceTypeOneOnePlusMinus_hyperbolic, rfl, ?_⟩
  intro h
  exact etthSignature_oneOnePlusMinus_ne_sourceTypeOneOnePlusMinus h.symm

/-! ## 10. Grounding in the actual S1726 model

S1964 proved that the actual elliptic involution on the actual model
E' : y^2 = x^3 + (61/64)x^2 - (125/64)x has exactly three fixed affine points,
the two-torsion points (0,0), (1,0), (-125/64,0), and that the coordinate
endomorphism acts by y |-> -y there.  These are the three order-two stacky
points of the quotient. -/

/-- The affine two-torsion point (0,0) of the actual model. -/
abbrev S1983PointZero : S1726PuncturedCurve :=
  ⟨(0, 0), S1726Equation_zero_zero⟩

/-- The affine two-torsion point (1,0) of the actual model. -/
abbrev S1983PointOne : S1726PuncturedCurve :=
  ⟨(1, 0), S1726Equation_one_zero⟩

/-- The affine two-torsion point (-125/64,0) of the actual model. -/
abbrev S1983PointNeg125 : S1726PuncturedCurve :=
  ⟨(-125/64, 0), S1964Equation_neg125⟩

/-- *The fixed points of the actual involution are exactly the three
two-torsion points* (the reverse implication is new; S1964 had the forward
one). -/
theorem S1983_fixedPoint_cases (p : S1726PuncturedCurve) :
    S1964Neg p = p ↔
      p = S1983PointZero ∨ p = S1983PointOne ∨ p = S1983PointNeg125 := by
  constructor
  · intro hp
    rcases S1964FixedPoint_cases hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro hp
    rcases hp with h | h | h
    · rw [h]
      exact (S1964Neg_eq_self_iff _).mpr rfl
    · rw [h]
      exact (S1964Neg_eq_self_iff _).mpr rfl
    · rw [h]
      exact (S1964Neg_eq_self_iff _).mpr rfl

/-- The fixed locus of the actual involution, as a set. -/
theorem S1983FixedLocus_eq :
    {p : S1726PuncturedCurve | S1964Neg p = p} =
      ({S1983PointZero, S1983PointOne, S1983PointNeg125} :
        Set S1726PuncturedCurve) := by
  ext p
  rw [Set.mem_setOf_eq, S1983_fixedPoint_cases p]
  simp

/-- The three fixed points are pairwise distinct (S1964). -/
theorem S1983_fixedPoints_pairwise_distinct :
    S1983PointZero ≠ S1983PointOne ∧
      S1983PointZero ≠ S1983PointNeg125 ∧
        S1983PointOne ≠ S1983PointNeg125 :=
  S1964TwoTorsion_pairwise_distinct

/-- *The three order-two stacky points of the honest (1,1)^± signature are
exactly the fixed points of the actual elliptic involution*: the signature has
stackyOrders = [2,2,2] (three order-two points) and the actual model has
exactly three fixed affine points, the two-torsion points. -/
theorem S1983_stackyOrders_eq_fixedLocus :
    (etthSignature EtThType.oneOnePlusMinus).stackyOrders = [2, 2, 2] ∧
      {p : S1726PuncturedCurve | S1964Neg p = p} =
        ({S1983PointZero, S1983PointOne, S1983PointNeg125} :
          Set S1726PuncturedCurve) :=
  ⟨rfl, S1983FixedLocus_eq⟩

/-- *The single cusp of the honest signature is forced* by the degree-two
±1-torsor: given genus zero, the three order-two stacky points and
2·χ(C) = χ(X_F), the puncture count is exactly one. -/
theorem S1983_punctures_forced (T : Iut.OrbicurveSignature)
    (hg : T.genus = 0) (hs : T.stackyOrders = [2, 2, 2])
    (heuler : 2 * T.eulerCharacteristic =
      Iut.OrbicurveSignature.oncePuncturedElliptic.eulerCharacteristic) :
    T = etthSignature EtThType.oneOnePlusMinus :=
  SignQuotientInput.quotient_unique signQuotientInputOncePunctured T hg hs heuler

/-- The data of the honest (1,1)^± signature. -/
theorem S1983_honestSignature_data :
    (etthSignature EtThType.oneOnePlusMinus).genus = 0 ∧
      (etthSignature EtThType.oneOnePlusMinus).stackyOrders = [2, 2, 2] ∧
        (etthSignature EtThType.oneOnePlusMinus).punctures = 1 :=
  ⟨rfl, rfl, etthSignature_oneOnePlusMinus_punctures⟩

/-! ### The genus-zero component: the invariant ring of the actual model -/

/-- The K-algebra map K[X] -> R' sending X to the class of the affine coordinate
x. -/
noncomputable def S1983PolyToCoordinateRing :
    Polynomial S1726K →ₐ[S1726K] S1726CoordinateRing :=
  Polynomial.aeval
    (Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) (MvPolynomial.X 0))

theorem S1983PolyToCoordinateRing_X :
    S1983PolyToCoordinateRing (Polynomial.X) =
      Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial})
        (MvPolynomial.X 0) := by
  simp [S1983PolyToCoordinateRing]

theorem S1983PolyToCoordinateRing_comp :
    S1898CoordEndo.comp S1983PolyToCoordinateRing = S1983PolyToCoordinateRing := by
  apply Polynomial.algHom_ext
  rw [AlgHom.comp_apply, S1983PolyToCoordinateRing_X]
  exact S1964CoordEndo_x

/-- K[x] is contained in the fixed subring of the actual involution. -/
theorem S1983PolyToCoordinateRing_mem (p : Polynomial S1726K) :
    S1898CoordEndo (S1983PolyToCoordinateRing p) =
      S1983PolyToCoordinateRing p := by
  have h := congrArg
    (fun f : Polynomial S1726K →ₐ[S1726K] S1726CoordinateRing => f p)
    S1983PolyToCoordinateRing_comp
  simpa [AlgHom.comp_apply] using h

/-- The fixed subring of the actual affine coordinate ring under [-1]. -/
def S1983InvariantSubring : Set S1726CoordinateRing :=
  {r | S1898CoordEndo r = r}

/-- *The precise missing geometric input for the genus = 0 component of the
honest signature.*  The invariant ring of the actual affine coordinate ring
under [-1] is exactly K[x]; equivalently, the coarse quotient of the
once-punctured elliptic curve by ±1 is the affine line, so its projective
completion is P^1 with one cusp.

The inclusion K[x] ⊆ R'^[-1] is proved above (S1983PolyToCoordinateRing_mem).
The reverse inclusion needs the normal form R' = K[x] ⊕ K[x]·y with
y^2 = x^3 + (61/64)x^2 - (125/64)x, which is not in the tree.  This statement is
the remaining geometric input of the signature computation; it is recorded, not
postulated as an instance. -/
def S1983CoarseQuotientIsAffineLine : Prop :=
  S1983InvariantSubring = Set.range S1983PolyToCoordinateRing

/-! ## 11. Axiom footprint -/

#print axioms etthSignature
#print axioms etthSignature_oneOnePlusMinus_eq_honestSignature
#print axioms etthSignature_oneOnePlusMinus_punctures
#print axioms etthSignature_oneOnePlusMinus_euler
#print axioms etthSignature_oneOnePlusMinus_euler_two_mul
#print axioms etthSignature_oneLTors_euler_l
#print axioms etthSignature_oneLTorsPlusMinus_euler_l
#print axioms etthSignature_isHyperbolic
#print axioms etthSignature_oneOnePlusMinus_ne_sourceTypeOneOnePlusMinus
#print axioms etthSignature_oneOnePlusMinus_euler_eq_paperLabel
#print axioms etthSignature_oneOnePlusMinus_ne_legacyTypeOneOne
#print axioms etthSignature_oneLTors_ne_legacyTypeOneLTorsion
#print axioms etthSignature_oneLTorsPlusMinus_ne_legacyTypeOneLTorsionPlusMinus
#print axioms etthSignature_oneLTorsPlusMinus_ne_oneOnePlusMinus
#print axioms etthSignature_oneOnePlusMinus_ne_coarse
#print axioms SignQuotientInput.quotient_unique
#print axioms SignQuotientInput.quotient_eulerCharacteristic
#print axioms S1983EtThCF
#print axioms S1983EtThCF_iff_honest
#print axioms S1964FirstMissing_ofS1983
#print axioms S1983SignatureNotForcedByFiber
#print axioms S1983_fixedPoint_cases
#print axioms S1983FixedLocus_eq
#print axioms S1983_stackyOrders_eq_fixedLocus
#print axioms S1983_punctures_forced
#print axioms S1983PolyToCoordinateRing_mem

end LeanFormal.IUT.XiFPaper.S1983EtThSignatureBridgeActual

end
