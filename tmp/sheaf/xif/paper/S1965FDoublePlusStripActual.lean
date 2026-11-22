import tmp.sheaf.xif.paper.S1959PaperCoricVerticesActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripComponentIdentification
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge

/-!
# S1965: the F-double-plus-prime-strip carrier and the actual C-mod packaging

Layer: O (original Theta-link / q-pilot), on the source-faithful S1895 input.

S1959 identified the exact first missing type of the paper-level coric vertices:
the F^double-plus-prime-strip carrier

  (C^double-plus, Prime(C^double-plus) ~= V, F^dagger, {rho_v})

of IUT I, Definition 5.2, (iv), and IUT II, Definition 4.9, (vii)--(viii)
(see also IUT I, Remark 5.2.1, (ii), for the construction from an
F-prime-strip).  The tree had only FPrimeStrip (the F^dagger part) and the
global realified Frobenioid C^double-plus-mod.

This file does three things.

## 1. The carrier type

It defines FDoublePlusPrimeStrip V, a structure whose fields are exactly the
paper data:

* global : the global realified Frobenioid C^double-plus (an actual
  Iut.FrobenioidPresentation, Frobenioids I, Definition 1.3);
* basePoint : a base object at which the divisor monoid is evaluated;
* primeIndex and primeEquiv : Prime(C^double-plus) ~= V;
* localDivisor v : the local divisor monoid Phi(C^double-plus, v), an actual
  additive submonoid of the global divisor monoid, with an additive
  equivalence to NNReal (the paper's R_{>=0});
* fDagger : the F^dagger-prime-strip;
* localRealified v : the local realified divisor monoid
  Phi^rlf(C^dagger_v), with a multiplicative equivalence to Multiplicative
  NNReal;
* rho : the local isomorphism rho_v : Phi(C^double-plus,v) ~= Phi^rlf(C^dagger_v).

No field is a Prop slot, True/PUnit carrier, empty type or arbitrary
inhabitant.  The fields are the paper's data; the type is not asserted to be
inhabited by an arbitrary value.

## 2. The actual C-mod instance

It constructs a genuine inhabitant

  paperModFDoublePlus D : FDoublePlusPrimeStrip (NumberFieldPlace (PaperFmod D))

with

* global := paperGlobalRealifiedFrobenioid D (the actual C^double-plus-mod of
  S1927, built from the realified effective divisor cone of Fmod);
* primeIndex := NumberFieldPlace (PaperFmod D) and primeEquiv := refl;
* localDivisor v := the actual place component of the realified effective
  divisor monoid (the v-supported submonoid), with an explicit additive
  equivalence to NNReal (finite place: the coefficient at v; infinite place:
  the archimedean coordinate at v);
* fDagger := the actual numberFieldPrimeStrip of Example 3.6, reindexed from
  HeightOneSpectrum + InfinitePlace to NumberFieldPlace;
* localRealified v := Multiplicative NNReal, the canonical R_{>=0} model of
  the local realified divisor monoid;
* rho := the place-component equivalence.

This is an actual F^double-plus-prime-strip with the C^double-plus-mod global
Frobenioid and the actual number-field F^dagger part.  It is the paper's
C^double-plus-mod vertex, not the Theta or Gaussian vertex.

## 3. The exact first missing for C^double-plus-env / C^double-plus-gau

Corollary 4.6, (iv), (v), constructs the local theta and Gaussian monoid
assignments PsiFenv, PsiFgau and then the global realified Frobenioids
C^double-plus-env, C^double-plus-gau together with the local isomorphisms

  Phi(C^double-plus-env,v) ~= PsiFenv^R_v,   Phi(C^double-plus-gau,v) ~= PsiFgau^R_v.

The active LeanFormal/Iut tree contains no theta monoid and no Gaussian
monoid: HodgeTheater records only the finite thetaPacket.  Hence the local
realified monoid families for env and gau are not constructed.  This file does
NOT introduce a paper-side ThetaMonoid type, a Prop slot or a Nonempty gate for
them: any such type inhabited from the present data would be a fake slot.

What is constructed instead is the exact conditional packaging

  paperCoricDoublePlusOfLocalMonoids D M e,

which from any local monoid family M with a multiplicative equivalence
e : M v ~= R_{>=0} produces the F^double-plus carrier on the actual C-mod
global Frobenioid and the actual number-field F^dagger strip.  For env/gau the
missing input is exactly the paper's local theta/Gaussian realification data
(and its construction from PsiFenv/PsiFgau); the packaging itself is not
missing.

There is a second, independent boundary: the actual numberFieldPrimeStrip has
trivial geometric kernels (Example36PrimeStripComponentIdentification), while
the paper's F^dagger components use tempered/etale fundamental groups of
once-punctured elliptic curves with nontrivial geometric kernel.  That
geometric component is a separate missing source construction.

The S1959 reduced vertices use the one-column index FinitePrimePlace 2 7,
whereas the actual C^double-plus-mod prime set is NumberFieldPlace Fmod.  The
file constructs the reindexing operation of the carrier and the conditional
one-column carrier paperOneColumnDoublePlus D e from a place equivalence e;
no such equivalence is constructed, so the reduced vertices are not silently
identified with the C-mod carrier.

No sorry, axiom, True/PUnit slot, empty type or assumption-only Nonempty gate
is used.  The only classical inputs are the ones already used by S1895/S1927
(propext, Classical.choice, Quot.sound).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT

universe u v

open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual.Realified
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open IsDedekindDomain NumberField

/-! ## 1. Reindexing of F-prime-strips and the number-field place equivalence -/

namespace FPrimeStrip

/-- Reindex an F-prime-strip along an equivalence of place types.  This is a
genuine transport of every fiber, not a new prime-strip. -/
noncomputable def reindex {V W : Type*} (e : V ≃ W)
    (F : FPrimeStrip V) : FPrimeStrip W where
  Pi := fun w => F.Pi (e.symm w)
  groupPi := fun w => F.groupPi (e.symm w)
  G := fun w => F.G (e.symm w)
  groupG := fun w => F.groupG (e.symm w)
  proj := fun w => F.proj (e.symm w)
  proj_surjective := fun w => F.proj_surjective (e.symm w)
  Mon := fun w => F.Mon (e.symm w)
  commMonoidMon := fun w => F.commMonoidMon (e.symm w)
  action := fun w => F.action (e.symm w)
  degree := fun w => F.degree (e.symm w)

end FPrimeStrip

/-- The number-field place carrier NumberFieldPlace is the sum of the finite
and infinite places.  The F^dagger strip of Example 3.6 is indexed by
HeightOneSpectrum + InfinitePlace; this equivalence identifies the two. -/
noncomputable def numberFieldPlaceEquivPlaceIndex
    (F : Type u) [Field F] [NumberField F] :
    NumberFieldPlace F ≃ NumberFieldPlaceIndex (F := F) where
  toFun
    | NumberFieldPlace.finite p => Sum.inl p.maximalIdeal
    | NumberFieldPlace.infinite w => Sum.inr w
  invFun
    | Sum.inl v => NumberFieldPlace.finite (NumberField.FinitePlace.mk v)
    | Sum.inr w => NumberFieldPlace.infinite w
  left_inv
    | NumberFieldPlace.finite p => by
        simp [NumberField.FinitePlace.mk_maximalIdeal]
    | NumberFieldPlace.infinite w => by rfl
  right_inv
    | Sum.inl v => by
        simp [NumberField.FinitePlace.maximalIdeal_mk]
    | Sum.inr w => by rfl

/-- The actual number-field F^dagger-prime-strip, reindexed to the paper place
carrier NumberFieldPlace.  It is the F^dagger part used by the C-mod carrier. -/
noncomputable def numberFieldPrimeStripOnPlaces
    (F : Type u) [Field F] [NumberField F] :
    FPrimeStrip (NumberFieldPlace F) :=
  FPrimeStrip.reindex (numberFieldPlaceEquivPlaceIndex F).symm
    (numberFieldPrimeStrip (F := F))

/-- Convert an additive equivalence to a multiplicative equivalence of the
Multiplicative type tags. -/
noncomputable def addEquivToMulEquiv {A B : Type*} [Add A] [Add B]
    (e : A ≃+ B) : Multiplicative A ≃* Multiplicative B where
  toFun a := Multiplicative.ofAdd (e a.toAdd)
  invFun b := Multiplicative.ofAdd (e.symm b.toAdd)
  left_inv a := by simp
  right_inv b := by simp
  map_mul' a b := by
    change Multiplicative.ofAdd (e (a.toAdd + b.toAdd)) =
      Multiplicative.ofAdd (e a.toAdd) * Multiplicative.ofAdd (e b.toAdd)
    rw [e.map_add]
    rfl

/-! ## 2. The F^double-plus-prime-strip carrier -/

/-- The paper's F^double-plus-prime-strip data, IUT I, Definition 5.2, (iv),
and IUT II, Definition 4.9, (vii)--(viii):

  (C^double-plus, Prime(C^double-plus) ~= V, F^dagger, {rho_v}).

The fields are the actual mathematical data.  Conditions (a)--(e) of
Definition 5.2, (iv), are represented by the global Frobenioid, the prime
equivalence, the local divisor components, the F^dagger strip, the local
realified divisors and rho.  Condition (f) (isomorphism to the paper's F-mod
datum) is the identification of the whole tuple; for the actual C-mod instance
below the tuple is built from the actual C-mod construction.

The generic structure records the carrier data; it does not assert the
isomorphism conditions (a) and (f) as fields.  paperModFDoublePlus below has
global exactly paperGlobalRealifiedFrobenioid D (the actual C-mod), so (a)
and (f) hold by construction there.  The topological structure on the local
monoids is not modeled: the fields carry the monoid structure and the
R_{>=0} equivalence, which is the algebraic content of rho_v.  No Prop slot
or arbitrary carrier is used for the missing topological refinement. -/
structure FDoublePlusPrimeStrip (V : Type v) where
  /-- C^double-plus: the global realified Frobenioid. -/
  global : Iut.FrobenioidPresentation
  /-- a base object at which the global divisor monoid is evaluated -/
  basePoint : (global.baseCategory : Type)
  /-- Prime(C^double-plus) -/
  primeIndex : Type v
  /-- Prime(C^double-plus) ~= V -/
  primeEquiv : primeIndex ≃ V
  /-- the local divisor monoid Phi(C^double-plus,v), as an actual submonoid of
  the global divisor monoid -/
  localDivisor : V -> AddSubmonoid
    ((global.preFrobenioid.divisorMonoid.obj basePoint).carrier)
  /-- Phi(C^double-plus,v) ~= R_{>=0} -/
  localDivisorEquiv : forall v, localDivisor v ≃+ NNReal
  /-- F^dagger -/
  fDagger : FPrimeStrip V
  /-- the local realified divisor monoid Phi^rlf(C^dagger_v) -/
  localRealified : V -> Type v
  [commMonoidLocalRealified : forall v, CommMonoid (localRealified v)]
  /-- Phi^rlf(C^dagger_v) ~= R_{>=0} -/
  localRealifiedEquiv : forall v, localRealified v ≃* Multiplicative NNReal
  /-- rho_v : Phi(C^double-plus,v) ~= Phi^rlf(C^dagger_v) -/
  rho : forall v, Multiplicative (localDivisor v) ≃* localRealified v

attribute [instance] FDoublePlusPrimeStrip.commMonoidLocalRealified

namespace FDoublePlusPrimeStrip

variable {V : Type v} (P : FDoublePlusPrimeStrip V)

/-- The underlying F^dagger-prime-strip. -/
def toFPrimeStrip : FPrimeStrip V := P.fDagger

/-- The underlying global realified Frobenioid. -/
def toGlobal : Iut.FrobenioidPresentation := P.global

/-- Reindex the carrier along an equivalence of place types. -/
noncomputable def reindex {W : Type v} (e : V ≃ W) :
    FDoublePlusPrimeStrip W where
  global := P.global
  basePoint := P.basePoint
  primeIndex := P.primeIndex
  primeEquiv := P.primeEquiv.trans e
  localDivisor := fun w => P.localDivisor (e.symm w)
  localDivisorEquiv := fun w => P.localDivisorEquiv (e.symm w)
  fDagger := FPrimeStrip.reindex e P.fDagger
  localRealified := fun w => P.localRealified (e.symm w)
  commMonoidLocalRealified := fun w => P.commMonoidLocalRealified (e.symm w)
  localRealifiedEquiv := fun w => P.localRealifiedEquiv (e.symm w)
  rho := fun w => P.rho (e.symm w)

end FDoublePlusPrimeStrip

end LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S1965FDoublePlusStripActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual.Realified
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open IsDedekindDomain NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 3. The actual local divisor components of the realified divisor monoid -/

/-- The local divisor component at a finite place p: the realified effective
divisors supported at p and with zero archimedean coordinate. -/
def finitePlaceComponent (p : HeightOneSpectrum (𝓞 F)) :
    AddSubmonoid (RealEffectiveDivisor (F := F)) := by
  classical
  exact
  { carrier := {x | x.1.support ⊆ {p} ∧ x.2 = 0}
    zero_mem' := by
      refine ⟨?_, rfl⟩
      simp
    add_mem' := by
      rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
      refine ⟨?_, by simp [hx2, hy2]⟩
      intro q hq
      have hq' : q ∈ Finsupp.support (x.1 + y.1) := hq
      have hq'' : q ∈ Finsupp.support x.1 ∪ Finsupp.support y.1 :=
        Finsupp.support_add (g₁ := x.1) (g₂ := y.1) hq'
      exact (Finset.mem_union.mp hq'').elim (fun h => hx1 h) (fun h => hy1 h) }

/-- The local divisor component at an infinite place w: the realified
effective divisors with zero finite part and archimedean support at w. -/
def infinitePlaceComponent (w : InfinitePlace F) :
    AddSubmonoid (RealEffectiveDivisor (F := F)) := by
  classical
  exact
  { carrier := {x | x.1 = 0 ∧ forall w' : InfinitePlace F, w' ≠ w -> x.2 w' = 0}
    zero_mem' := by
      refine ⟨rfl, ?_⟩
      intro w' hw'
      rfl
    add_mem' := by
      rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
      refine ⟨by simp [hx1, hy1], ?_⟩
      intro w' hw'
      simp [hx2 w' hw', hy2 w' hw'] }

/-- The local divisor component Phi(C-mod,v) at an arbitrary place. -/
def placeComponent (v : NumberFieldPlace F) :
    AddSubmonoid (RealEffectiveDivisor (F := F)) :=
  match v with
  | NumberFieldPlace.finite p => finitePlaceComponent (F := F) p.maximalIdeal
  | NumberFieldPlace.infinite w => infinitePlaceComponent (F := F) w

/-- The finite-place component is additively equivalent to R_{>=0}: read the
coefficient at p. -/
noncomputable def finitePlaceComponentEquiv (p : HeightOneSpectrum (𝓞 F)) :
    finitePlaceComponent (F := F) p ≃+ NNReal := by
  classical
  exact
  { toFun := fun x => x.1.1 p
    invFun := fun c =>
      ⟨(Finsupp.single p c, 0), by
        refine ⟨?_, rfl⟩
        intro q hq
        by_cases hc : c = 0
        · subst hc; simp at hq
        · rwa [Finsupp.support_single _ hc] at hq⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply Prod.ext
      · apply Finsupp.ext
        intro q
        by_cases hq : q = p
        · subst hq; simp
        · have hnot : q ∉ x.1.1.support := by
            intro hmem
            have hmem' := x.2.1 hmem
            simp only [Finset.mem_singleton] at hmem'
            exact hq hmem'
          rw [Finsupp.notMem_support_iff] at hnot
          simp [Finsupp.single_eq_of_ne hq, hnot]
      · exact x.2.2.symm
    right_inv := by
      intro c
      simp
    map_add' := by
      intro x y
      simp }

/-- The infinite-place component is additively equivalent to R_{>=0}: read
the archimedean coordinate at w. -/
noncomputable def infinitePlaceComponentEquiv (w : InfinitePlace F) :
    infinitePlaceComponent (F := F) w ≃+ NNReal := by
  classical
  exact
  { toFun := fun x => x.1.2 w
    invFun := fun c =>
      ⟨(0, Pi.single w c), by
        refine ⟨rfl, ?_⟩
        intro w' hw'
        simp [Pi.single_eq_of_ne hw']⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply Prod.ext
      · exact x.2.1.symm
      · funext w'
        by_cases h : w' = w
        · subst h; simp
        · have hzero := x.2.2 w' h
          simp [Pi.single_eq_of_ne h, hzero]
    right_inv := by
      intro c
      simp
    map_add' := by
      intro x y
      simp }

/-- The place component is additively equivalent to R_{>=0}. -/
noncomputable def placeComponentEquiv (v : NumberFieldPlace F) :
    placeComponent (F := F) v ≃+ NNReal :=
  match v with
  | NumberFieldPlace.finite p => finitePlaceComponentEquiv (F := F) p.maximalIdeal
  | NumberFieldPlace.infinite w => infinitePlaceComponentEquiv (F := F) w

/-! ## 4. The actual C-mod F^double-plus-prime-strip -/

/-- The actual F^double-plus-prime-strip with the C^double-plus-mod global
realified Frobenioid and the actual number-field F^dagger strip. -/
noncomputable def paperModFDoublePlus (D : S1895PaperInput) :
    FDoublePlusPrimeStrip (NumberFieldPlace (PaperFmod D)) where
  global := paperGlobalRealifiedFrobenioid D
  basePoint := paperGlobalBaseObject D
  primeIndex := NumberFieldPlace (PaperFmod D)
  primeEquiv := Equiv.refl _
  localDivisor := fun v => placeComponent (F := PaperFmod D) v
  localDivisorEquiv := fun v => placeComponentEquiv (F := PaperFmod D) v
  fDagger := numberFieldPrimeStripOnPlaces (F := PaperFmod D)
  localRealified := fun _ => Multiplicative NNReal
  commMonoidLocalRealified := fun _ => inferInstance
  localRealifiedEquiv := fun _ => MulEquiv.refl _
  rho := fun v => addEquivToMulEquiv (placeComponentEquiv (F := PaperFmod D) v)

/-- The global Frobenioid of the actual mod carrier is C^double-plus-mod. -/
@[simp] theorem paperModFDoublePlus_global (D : S1895PaperInput) :
    (paperModFDoublePlus D).global = paperGlobalRealifiedFrobenioid D := rfl

/-- Its prime index is the actual place type of Fmod. -/
@[simp] theorem paperModFDoublePlus_primeIndex (D : S1895PaperInput) :
    (paperModFDoublePlus D).primeIndex = NumberFieldPlace (PaperFmod D) := rfl

/-- Its prime equivalence is the identity. -/
@[simp] theorem paperModFDoublePlus_primeEquiv (D : S1895PaperInput)
    (v : NumberFieldPlace (PaperFmod D)) :
    (paperModFDoublePlus D).primeEquiv v = v := rfl

/-- Its F^dagger part is the actual number-field strip on the paper places. -/
@[simp] theorem paperModFDoublePlus_fDagger (D : S1895PaperInput) :
    (paperModFDoublePlus D).fDagger =
      numberFieldPrimeStripOnPlaces (F := PaperFmod D) := rfl

/-- The local divisor monoid at v is the actual v-supported submonoid of the
realified effective divisor monoid. -/
@[simp] theorem paperModFDoublePlus_localDivisor (D : S1895PaperInput)
    (v : NumberFieldPlace (PaperFmod D)) :
    (paperModFDoublePlus D).localDivisor v =
      placeComponent (F := PaperFmod D) v := rfl

/-- The divisor monoid of C^double-plus-mod at the base object is the actual
realified effective divisor monoid of Fmod. -/
theorem paperModFDoublePlus_divisorMonoid (D : S1895PaperInput) :
    ((paperModFDoublePlus D).global.preFrobenioid.divisorMonoid.obj
      (paperModFDoublePlus D).basePoint).carrier =
      RealEffectiveDivisor (F := PaperFmod D) := rfl

/-! ## 5. The actual prime generator and the rho normalization -/

/-- The generator of the local divisor component at a place: the prime divisor
itself, with coefficient one. -/
noncomputable def placeComponentPrime (v : NumberFieldPlace F) :
    placeComponent (F := F) v := by
  classical
  match v with
  | NumberFieldPlace.finite p =>
      exact
        ⟨(Finsupp.single p.maximalIdeal 1, 0), by
          refine ⟨?_, rfl⟩
          intro q hq
          have hq' : q ∈ Finsupp.support
              (Finsupp.single p.maximalIdeal (1 : NNReal)) := hq
          simpa [Finsupp.support_single _ one_ne_zero] using hq'⟩
  | NumberFieldPlace.infinite w =>
      exact
        ⟨(0, Pi.single w 1), by
          refine ⟨rfl, ?_⟩
          intro w' hw'
          simp [Pi.single_eq_of_ne hw']⟩

/-- The component equivalence sends the prime generator to 1 in R_{>=0}. -/
theorem placeComponentEquiv_prime (v : NumberFieldPlace F) :
    placeComponentEquiv (F := F) v (placeComponentPrime (F := F) v) = 1 := by
  cases v with
  | finite p =>
      change (placeComponentPrime (F := F) (NumberFieldPlace.finite p)).1.1
        p.maximalIdeal = 1
      simp [placeComponentPrime]
  | infinite w =>
      change (placeComponentPrime (F := F) (NumberFieldPlace.infinite w)).1.2 w = 1
      simp [placeComponentPrime]

/-- The rho of the actual mod carrier sends the prime generator to the
normalized generator 1 of the local realified divisor monoid. -/
theorem paperModFDoublePlus_rho_prime (D : S1895PaperInput)
    (v : NumberFieldPlace (PaperFmod D)) :
    (paperModFDoublePlus D).rho v
        (Multiplicative.ofAdd (placeComponentPrime (F := PaperFmod D) v)) =
      Multiplicative.ofAdd (1 : NNReal) := by
  change addEquivToMulEquiv (placeComponentEquiv (F := PaperFmod D) v)
      (Multiplicative.ofAdd (placeComponentPrime (F := PaperFmod D) v)) =
    Multiplicative.ofAdd (1 : NNReal)
  simp [addEquivToMulEquiv, placeComponentEquiv_prime]

/-- The local divisor component is nontrivial: it contains the prime
generator. -/
theorem placeComponentPrime_mem (v : NumberFieldPlace F) :
    (placeComponentPrime (F := F) v : RealEffectiveDivisor (F := F)) ∈
      placeComponent (F := F) v :=
  (placeComponentPrime (F := F) v).2

/-! ## 6. The conditional coric packaging and the one-column index -/

/-- The conditional env/gau packaging: from any local monoid family M and a
multiplicative equivalence e : M v ~= R_{>=0}, construct the F^double-plus
carrier on the actual C^double-plus-mod global Frobenioid and the actual
number-field F^dagger strip.

For the paper's env/gau vertices, M is the realification of the local theta or
Gaussian monoid and e is the local isomorphism of IUT II, Corollary 4.6, (v).
Those local monoids are the exact missing source construction (see the module
header); this function is the packaging interface, not an inhabitant of them. -/
noncomputable def paperCoricDoublePlusOfLocalMonoids
    (D : S1895PaperInput)
    (M : NumberFieldPlace (PaperFmod D) -> Type)
    [commM : forall v, CommMonoid (M v)]
    (e : forall v, M v ≃* Multiplicative NNReal) :
    FDoublePlusPrimeStrip (NumberFieldPlace (PaperFmod D)) where
  global := paperGlobalRealifiedFrobenioid D
  basePoint := paperGlobalBaseObject D
  primeIndex := NumberFieldPlace (PaperFmod D)
  primeEquiv := Equiv.refl _
  localDivisor := fun v => placeComponent (F := PaperFmod D) v
  localDivisorEquiv := fun v => placeComponentEquiv (F := PaperFmod D) v
  fDagger := numberFieldPrimeStripOnPlaces (F := PaperFmod D)
  localRealified := M
  commMonoidLocalRealified := commM
  localRealifiedEquiv := e
  rho := fun v =>
    (addEquivToMulEquiv (placeComponentEquiv (F := PaperFmod D) v)).trans
      (e v).symm

/-- The rho of the conditional packaging is the component equivalence followed
by the inverse of the local identification e. -/
theorem paperCoricDoublePlusOfLocalMonoids_rho_apply
    (D : S1895PaperInput)
    (M : NumberFieldPlace (PaperFmod D) -> Type)
    [commM : forall v, CommMonoid (M v)]
    (e : forall v, M v ≃* Multiplicative NNReal)
    (v : NumberFieldPlace (PaperFmod D))
    (x : Multiplicative (placeComponent (F := PaperFmod D) v)) :
    (paperCoricDoublePlusOfLocalMonoids D M e).rho v x =
      (e v).symm
        (addEquivToMulEquiv (placeComponentEquiv (F := PaperFmod D) v) x) := rfl

/-- The conditional packaging has the same global Frobenioid and F^dagger
part as the mod carrier; only the local realified monoids and rho differ. -/
theorem paperCoricDoublePlusOfLocalMonoids_global
    (D : S1895PaperInput)
    (M : NumberFieldPlace (PaperFmod D) -> Type)
    [commM : forall v, CommMonoid (M v)]
    (e : forall v, M v ≃* Multiplicative NNReal) :
    (paperCoricDoublePlusOfLocalMonoids D M e).global =
      (paperModFDoublePlus D).global := rfl

/-- The conditional packaging is the mod carrier when the local monoid family
is the canonical R_{>=0}. -/
theorem paperCoricDoublePlusOfLocalMonoids_refl
    (D : S1895PaperInput) :
    paperCoricDoublePlusOfLocalMonoids D
        (fun _ => Multiplicative NNReal) (fun _ => MulEquiv.refl _) =
      paperModFDoublePlus D := by
  rfl

/-- The conditional one-column carrier: from an equivalence between the actual
place type of Fmod and the S1959 one-column index FinitePrimePlace 2 7, the
actual mod carrier reindexes to the one-column index.

No such equivalence is constructed in the tree.  The paper's V is the selected
place set of K, and S1959 uses FinitePrimePlace 2 7 as a reduced one-column
index; this definition records the exact missing reindexing datum. -/
noncomputable def paperOneColumnDoublePlus
    (D : S1895PaperInput)
    (e : NumberFieldPlace (PaperFmod D) ≃ FinitePrimePlace 2 7) :
    FDoublePlusPrimeStrip (FinitePrimePlace 2 7) :=
  (paperModFDoublePlus D).reindex e

/-- The one-column carrier keeps the mod global Frobenioid. -/
@[simp] theorem paperOneColumnDoublePlus_global (D : S1895PaperInput)
    (e : NumberFieldPlace (PaperFmod D) ≃ FinitePrimePlace 2 7) :
    (paperOneColumnDoublePlus D e).global =
      paperGlobalRealifiedFrobenioid D := rfl

/-- The one-column carrier's prime equivalence is the given place equivalence
composed with the mod prime equivalence. -/
@[simp] theorem paperOneColumnDoublePlus_primeEquiv (D : S1895PaperInput)
    (e : NumberFieldPlace (PaperFmod D) ≃ FinitePrimePlace 2 7)
    (p : (paperModFDoublePlus D).primeIndex) :
    (paperOneColumnDoublePlus D e).primeEquiv p =
      e ((paperModFDoublePlus D).primeEquiv p) := rfl

/-- The one-column carrier's F^dagger part is the reindexed actual
number-field strip. -/
@[simp] theorem paperOneColumnDoublePlus_fDagger (D : S1895PaperInput)
    (e : NumberFieldPlace (PaperFmod D) ≃ FinitePrimePlace 2 7) :
    (paperOneColumnDoublePlus D e).fDagger =
      FPrimeStrip.reindex e
        (numberFieldPrimeStripOnPlaces (F := PaperFmod D)) := rfl

/-! ## 7. Axiom probes -/

#print axioms paperModFDoublePlus
#print axioms paperModFDoublePlus_rho_prime
#print axioms paperCoricDoublePlusOfLocalMonoids
#print axioms paperOneColumnDoublePlus

end LeanFormal.IUT.XiFPaper.S1965FDoublePlusStripActual
