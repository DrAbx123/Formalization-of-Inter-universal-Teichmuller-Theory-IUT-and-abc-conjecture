import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTII.Frobenioid.FinitePrimeStripRestriction
import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralFPrimeStrip
import LeanFormal.IUT.IUTII.Frobenioid.LocalPrimeStrip

/-!
# Prime-strip construction spike: fiber links between the concrete carriers

This file implements the first, source-free assembly step of
`IUT-I-II.prime-strips-frobenioids` (see `IUTII/Frobenioid/PrimeStrips.lean:5`):
the concrete F-prime-strip carriers built from the local arithmetic input are
connected to each other by

* definitional compatibility lemmas between the finite-interval carriers and
  the unrestricted carriers (`..._eq_global`),
* an indexed fiber-link structure `FPrimeStripLink`, with identity and
  composition, and the concrete links: finite unit strip to global unit strip,
  finite integral strip to global integral strip, integral strip to unit strip
  along `LocalIntegralMonoid.toAlgebraicClosureUnits`, and the composite of the
  finite integral strip to the global unit strip,
* degree transport along links and equality transport along equivalences,
* transport of the geometric kernel along prime-strip equivalences,
* `toD` alignment witnesses with the `DPrimeStrip` carriers of
  `IUTI/HodgeTheater/PrimeStripCore.lean`.

Not constructed here, and recorded as the boundary obligation at the end of
this file: a nontrivial geometric fundamental group (the current `proj` is the
identity, so `DPrimeStrip.geometric` is trivial), prime strips over the places
of a general number field rather than only over `ℚ_[p]`, the categorical
Frobenioid with its evaluation functor, arithmetic Frobenius data, and the
divisorial/realified value-monoid structure. Those remain the source-facing
content of `IUT-I-II.prime-strips-frobenioids`.
-/

namespace LeanFormal.IUT

universe u v w

/-- An indexed fiber link between two concrete F-prime-strips along an index
map `index : W → V`.  It transports the three carrier fibers (Pi, G, Mon) by
monoid homomorphisms compatible with the projection, the Galois action, and
the degree.  A link is not required to be injective or surjective: the
integral-to-unit evaluation below is not an isomorphism, while the interval
reindexing links are. -/
structure FPrimeStripLink {W : Type u} {V : Type v}
    (S : FPrimeStrip W) (T : FPrimeStrip V) where
  index : W → V
  mapPi : ∀ w, S.toDPrimeStrip.Pi w →* T.toDPrimeStrip.Pi (index w)
  mapG : ∀ w, S.G w →* T.G (index w)
  mapMon : ∀ w, S.Mon w →* T.Mon (index w)
  compatProj : ∀ w,
    (T.proj (index w)).comp (mapPi w) = (mapG w).comp (S.proj w)
  compatAction : ∀ w (g : S.toDPrimeStrip.Pi w) (x : S.Mon w),
    mapMon w (S.action w g x) =
      T.action (index w) (mapPi w g) (mapMon w x)
  compatDegree : ∀ w (x : S.Mon w),
    T.degree (index w) (mapMon w x) = S.degree w x

namespace FPrimeStripLink

variable {W : Type u} {V : Type v} {X : Type w}

/-- The identity link on a strip. -/
def refl (S : FPrimeStrip W) : FPrimeStripLink S S where
  index := id
  mapPi := fun w => MonoidHom.id _
  mapG := fun w => MonoidHom.id _
  mapMon := fun w => MonoidHom.id _
  compatProj := fun w => by ext x; rfl
  compatAction := fun w g x => rfl
  compatDegree := fun w x => rfl

/-- Composition of fiber links. -/
def trans {S : FPrimeStrip W} {T : FPrimeStrip V} {U : FPrimeStrip X}
    (L₁ : FPrimeStripLink S T) (L₂ : FPrimeStripLink T U) :
    FPrimeStripLink S U where
  index := fun w => L₂.index (L₁.index w)
  mapPi := fun w => (L₂.mapPi (L₁.index w)).comp (L₁.mapPi w)
  mapG := fun w => (L₂.mapG (L₁.index w)).comp (L₁.mapG w)
  mapMon := fun w => (L₂.mapMon (L₁.index w)).comp (L₁.mapMon w)
  compatProj := fun w => by
    calc (U.proj (L₂.index (L₁.index w))).comp
          ((L₂.mapPi (L₁.index w)).comp (L₁.mapPi w))
        = ((U.proj (L₂.index (L₁.index w))).comp (L₂.mapPi (L₁.index w))).comp
            (L₁.mapPi w) :=
          MonoidHom.comp_assoc _ _ _
      _ = ((L₂.mapG (L₁.index w)).comp (T.proj (L₁.index w))).comp
            (L₁.mapPi w) := by
          rw [L₂.compatProj]
      _ = (L₂.mapG (L₁.index w)).comp
            ((T.proj (L₁.index w)).comp (L₁.mapPi w)) :=
          (MonoidHom.comp_assoc _ _ _).symm
      _ = (L₂.mapG (L₁.index w)).comp ((L₁.mapG w).comp (S.proj w)) := by
          rw [L₁.compatProj]
      _ = ((L₂.mapG (L₁.index w)).comp (L₁.mapG w)).comp (S.proj w) :=
          (MonoidHom.comp_assoc _ _ _).symm
  compatAction := fun w g x => by
    calc L₂.mapMon (L₁.index w) (L₁.mapMon w (S.action w g x))
        = L₂.mapMon (L₁.index w)
            (T.action (L₁.index w) (L₁.mapPi w g) (L₁.mapMon w x)) :=
          congrArg (L₂.mapMon (L₁.index w)) (L₁.compatAction w g x)
      _ = U.action (L₂.index (L₁.index w))
            (L₂.mapPi (L₁.index w) (L₁.mapPi w g))
            (L₂.mapMon (L₁.index w) (L₁.mapMon w x)) :=
          L₂.compatAction (L₁.index w) (L₁.mapPi w g) (L₁.mapMon w x)
  compatDegree := fun w x => by
    calc U.degree (L₂.index (L₁.index w))
          (L₂.mapMon (L₁.index w) (L₁.mapMon w x))
        = T.degree (L₁.index w) (L₁.mapMon w x) :=
          L₂.compatDegree (L₁.index w) (L₁.mapMon w x)
      _ = S.degree w x := L₁.compatDegree w x

/-- A link transports the local degree at every fiber. -/
theorem localDegree_apply {S : FPrimeStrip W} {T : FPrimeStrip V}
    (L : FPrimeStripLink S T) (w : W) (x : S.Mon w) :
    T.degreeData.localDegree (L.index w) (L.mapMon w x) =
      S.degreeData.localDegree w x := by
  change Multiplicative.toAdd (T.degree (L.index w) (L.mapMon w x)) =
    Multiplicative.toAdd (S.degree w x)
  rw [L.compatDegree]

end FPrimeStripLink

namespace LocalIntegralMonoid

/-- The monoid-level evaluation to algebraic-closure units is equivariant for
the Galois actions: on the integral monoid the action restricts the algebra
automorphism to the integral closure, on algebraic-closure units it is the
induced unit action. -/
theorem toAlgebraicClosureUnits_galoisAction
    (p : Nat) [Fact (Nat.Prime p)] (g : LocalAbsoluteGalois p)
    (value : LocalIntegralMonoid p) :
    toAlgebraicClosureUnits p (galoisAction p g value) =
      localGaloisUnitsAction p g (toAlgebraicClosureUnits p value) := by
  apply Units.ext
  rfl

end LocalIntegralMonoid

namespace FPrimeStripLink

/-- The interval unit strip reindexed along the inclusion of its places into
the rational prime places: every fiber is definitionally the corresponding
fiber of the unrestricted unit strip. -/
noncomputable def finiteToGlobalUnitLink (lower upper : Nat) :
    FPrimeStripLink (finiteLocalFPrimeStrip lower upper) localFPrimeStrip where
  index := FinitePrimePlace.toRationalPrimePlace
  mapPi := fun w => MonoidHom.id _
  mapG := fun w => MonoidHom.id _
  mapMon := fun w => MonoidHom.id _
  compatProj := fun w => by ext x; rfl
  compatAction := fun w g x => rfl
  compatDegree := fun w x => rfl

/-- The interval integral strip reindexed along the inclusion of its places
into the rational prime places. -/
noncomputable def finiteToGlobalIntegralLink (lower upper : Nat) :
    FPrimeStripLink (finiteLocalIntegralFPrimeStrip lower upper)
      localIntegralFPrimeStrip where
  index := FinitePrimePlace.toRationalPrimePlace
  mapPi := fun w => MonoidHom.id _
  mapG := fun w => MonoidHom.id _
  mapMon := fun w => MonoidHom.id _
  compatProj := fun w => by ext x; rfl
  compatAction := fun w g x => rfl
  compatDegree := fun w x => rfl

/-- The integral-to-unit evaluation link at every rational prime place: the
value monoid of the integral strip maps to the ambient algebraic-closure units
by `LocalIntegralMonoid.toAlgebraicClosureUnits`. -/
noncomputable def localIntegralUnitLink :
    FPrimeStripLink localIntegralFPrimeStrip localFPrimeStrip where
  index := id
  mapPi := fun v => MonoidHom.id _
  mapG := fun v => MonoidHom.id _
  mapMon := fun v => by
    letI := Fact.mk v.2
    exact LocalIntegralMonoid.toAlgebraicClosureUnits v.1
  compatProj := fun v => by ext x; rfl
  compatAction := fun v g x => by
    letI := Fact.mk v.2
    exact LocalIntegralMonoid.toAlgebraicClosureUnits_galoisAction v.1 g x
  compatDegree := fun v x => by
    letI := Fact.mk v.2
    rfl

/-- The integral-to-unit evaluation link for each finite prime interval. -/
noncomputable def finiteIntegralUnitLink (lower upper : Nat) :
    FPrimeStripLink (finiteLocalIntegralFPrimeStrip lower upper)
      (finiteLocalFPrimeStrip lower upper) where
  index := id
  mapPi := fun v => MonoidHom.id _
  mapG := fun v => MonoidHom.id _
  mapMon := fun v => by
    letI := Fact.mk v.prime
    exact LocalIntegralMonoid.toAlgebraicClosureUnits v.1
  compatProj := fun v => by ext x; rfl
  compatAction := fun v g x => by
    letI := Fact.mk v.prime
    exact LocalIntegralMonoid.toAlgebraicClosureUnits_galoisAction v.1 g x
  compatDegree := fun v x => by
    letI := Fact.mk v.prime
    rfl

/-- The two-leg composite: interval integral strip to the global unit strip,
via the finite integral-to-unit evaluation and the reindexing. -/
noncomputable def finiteIntegralToGlobalUnitLink (lower upper : Nat) :
    FPrimeStripLink (finiteLocalIntegralFPrimeStrip lower upper)
      localFPrimeStrip :=
  (finiteIntegralUnitLink lower upper).trans (finiteToGlobalUnitLink lower upper)

end FPrimeStripLink

/-! ## Definitional compatibility of the finite-interval carriers with the
unrestricted carriers -/

theorem finiteLocalDPrimeStrip_Pi_eq_global (lower upper : Nat)
    (w : FinitePrimePlace lower upper) :
    (finiteLocalDPrimeStrip lower upper).Pi w =
      localDPrimeStrip.Pi w.toRationalPrimePlace := rfl

theorem finiteLocalDPrimeStrip_G_eq_global (lower upper : Nat)
    (w : FinitePrimePlace lower upper) :
    (finiteLocalDPrimeStrip lower upper).G w =
      localDPrimeStrip.G w.toRationalPrimePlace := rfl

theorem finiteLocalFPrimeStrip_monoid_eq_global (lower upper : Nat)
    (w : FinitePrimePlace lower upper) :
    (finiteLocalFPrimeStrip lower upper).Mon w =
      localFPrimeStrip.Mon w.toRationalPrimePlace := rfl

theorem finiteLocalFPrimeStrip_degree_eq_global (lower upper : Nat)
    (w : FinitePrimePlace lower upper)
    (x : (finiteLocalFPrimeStrip lower upper).Mon w) :
    (finiteLocalFPrimeStrip lower upper).degree w x =
      localFPrimeStrip.degree w.toRationalPrimePlace x := rfl

theorem finiteLocalFPrimeStrip_action_eq_global (lower upper : Nat)
    (w : FinitePrimePlace lower upper)
    (g : (finiteLocalFPrimeStrip lower upper).Pi w)
    (x : (finiteLocalFPrimeStrip lower upper).Mon w) :
    (finiteLocalFPrimeStrip lower upper).action w g x =
      localFPrimeStrip.action w.toRationalPrimePlace g x := rfl

theorem finiteLocalIntegralFPrimeStrip_monoid_eq_global (lower upper : Nat)
    (w : FinitePrimePlace lower upper) :
    (finiteLocalIntegralFPrimeStrip lower upper).Mon w =
      localIntegralFPrimeStrip.Mon w.toRationalPrimePlace := rfl

theorem finiteLocalIntegralFPrimeStrip_degree_eq_global (lower upper : Nat)
    (w : FinitePrimePlace lower upper)
    (x : (finiteLocalIntegralFPrimeStrip lower upper).Mon w) :
    (finiteLocalIntegralFPrimeStrip lower upper).degree w x =
      localIntegralFPrimeStrip.degree w.toRationalPrimePlace x := rfl

theorem finiteLocalIntegralFPrimeStrip_action_eq_global (lower upper : Nat)
    (w : FinitePrimePlace lower upper)
    (g : (finiteLocalIntegralFPrimeStrip lower upper).Pi w)
    (x : (finiteLocalIntegralFPrimeStrip lower upper).Mon w) :
    (finiteLocalIntegralFPrimeStrip lower upper).action w g x =
      localIntegralFPrimeStrip.action w.toRationalPrimePlace g x := rfl

/-! ## `toD` alignment with the prime-strip core carriers -/

theorem localFPrimeStrip_toD :
    localFPrimeStrip.toD = localDPrimeStrip := rfl

theorem localIntegralFPrimeStrip_toD :
    localIntegralFPrimeStrip.toD = localDPrimeStrip := rfl

theorem finiteLocalFPrimeStrip_toD (lower upper : Nat) :
    (finiteLocalFPrimeStrip lower upper).toD =
      finiteLocalDPrimeStrip lower upper := rfl

theorem finiteLocalIntegralFPrimeStrip_toD (lower upper : Nat) :
    (finiteLocalIntegralFPrimeStrip lower upper).toD =
      finiteLocalDPrimeStrip lower upper := rfl

/-! ## Degree transport and geometric-kernel transport -/

namespace FPrimeStripEquiv

variable {W : Type u} {F F' : FPrimeStrip W}

/-- An equivalence of strips preserves fiberwise local degrees. -/
theorem localDegree_eq (φ : FPrimeStripEquiv F F') (w : W) (x : F.Mon w) :
    F'.degreeData.localDegree w (φ.isoMon w x) = F.degreeData.localDegree w x := by
  change Multiplicative.toAdd (F'.degree w (φ.isoMon w x)) =
    Multiplicative.toAdd (F.degree w x)
  rw [φ.compatDegree]

/-- An equivalence of strips preserves every finite total degree. -/
theorem totalDegree_eq (φ : FPrimeStripEquiv F F') (s : Finset W)
    (x : ∀ w, F.Mon w) :
    F'.totalDegree s (fun w => φ.isoMon w (x w)) = F.totalDegree s x := by
  unfold FPrimeStrip.totalDegree PrimeStripDegree.totalDegree
  exact Finset.sum_congr rfl (fun w _ => φ.localDegree_eq w (x w))

end FPrimeStripEquiv

namespace DPrimeStripEquiv

variable {W : Type u} {D D' : DPrimeStrip W}

/-- An equivalence of D-prime-strips maps the geometric kernel onto the
geometric kernel: the projection compatibility identifies the kernels. -/
theorem geometric_iff (φ : DPrimeStripEquiv D D') (w : W) (x : D.Pi w) :
    φ.isoPi w x ∈ D'.geometric w ↔ x ∈ D.geometric w := by
  rw [DPrimeStrip.geometric_carrier, DPrimeStrip.geometric_carrier,
    φ.compat_apply w x]
  constructor
  · intro h
    apply (φ.isoG w).injective
    rw [h, map_one]
  · intro h
    rw [h, map_one]

end DPrimeStripEquiv

namespace FPrimeStripEquiv

variable {W : Type u} {F F' : FPrimeStrip W}

/-- An equivalence of F-prime-strips maps the geometric kernel of the
underlying D-prime-strip onto the geometric kernel. -/
theorem geometric_iff (φ : FPrimeStripEquiv F F') (w : W)
    (x : F.toDPrimeStrip.Pi w) :
    φ.isoPi w x ∈ F'.toDPrimeStrip.geometric w ↔
      x ∈ F.toDPrimeStrip.geometric w :=
  φ.toD.geometric_iff w x

end FPrimeStripEquiv

/-!
## Source-facing boundary records

The following primitives of `IUT-I-II.prime-strips-frobenioids` are not
constructed by this spike, in consumer order:

1. **Geometric fundamental group.** The paper's `proj` is the surjection from
   a geometric fundamental group to the local absolute Galois group; here
   `proj` is `MonoidHom.id`, so `DPrimeStrip.geometric` is trivial. A
   nontrivial realization needs the etale fundamental group of a (punctured)
   curve over the local field together with its quotient to the absolute
   Galois group. This is consumed by the Frobenioid input of
   `IUTII/Kummer/VerticalLogKummer.lean` and by the K1/K2 realization in
   `IUTIII/Theorem311/SourceK1K2Construction.lean`. It cannot be built by
   choosing an arbitrary type: the kernel is the arithmetic content of the
   strip.
2. **Number-field place carriers.** The current carriers are indexed by
   rational primes (`RationalPrimePlace`) with local field `ℚ_[p]`. The paper's
   strips live over the places of the base number field of the Theta-data; the
   completion carriers `K_v` and their transport are not available (see the
   parked `finite-place-completion-*` records of `ABCBridge/Geometry`). This is
   consumed by the `OriginalInput` of `IUTIII/Theorem311/SourceOriginalInput.lean`.
3. **Categorical Frobenioid.** No Frobenioid category, value functor, or
   Frobenioid link is constructed; only the underlying value monoids and their
   unit evaluation are. This is consumed by the ordered-layer contract of
   `VerticalLogKummer` and by the MOD/mod realification boundary `K2`
   (`SourceK1K2Construction.lean:679`).
4. **Arithmetic Frobenius.** The Frobenius dynamics on the value monoid and
   its compatibility with the log-shell are not formalized; this is consumed by
   the upper-semi input of `VerticalLogKummerCorrespondence.upperSemi` and by
   `Ind3`.
5. **Divisorial/realified value structure.** The divisorial (fractional
   ideal) layer and the realification of the value monoid used by `K2` are not
   constructed.
-/

namespace Audit

def primeStripsConstructionKernel : Obligation :=
  { id := "IUT-II.prime-strip-construction-kernel"
    source := "IUT I, Definition 5.2; IUT II, Sections 3-6 (local prime-strip assembly)"
    status := VerificationStatus.provedKernel
    note :=
      "The concrete finite-interval and unrestricted prime-strip carriers are " ++
        "connected by indexed fiber links: finite unit strip to global unit strip, " ++
        "finite integral strip to global integral strip, the integral-to-unit " ++
        "evaluation, and their composite. Identity, composition, local and finite " ++
        "total degree transport, geometric-kernel transport, and toD alignment " ++
        "with the D-prime-strip carriers are proved. No Frobenioid category, " ++
        "etale fundamental group, arithmetic Frobenius, or number-field place " ++
        "carrier is constructed; those are recorded in the boundary obligation."
    dependsOn :=
      [ "IUT-I-II.prime-strip-core", "IUT-I-II.prime-strip-degree-kernel",
        "IUT-I-II.local-f-prime-strip-carrier", "IUT-I-II.local-prime-place-carrier" ] }

def primeStripsFrobenioidBoundary : Obligation :=
  { id := "IUT-II.prime-strips-frobenioid-boundary"
    source := "IUT II, Sections 3-6; IUT III, Proposition 3.5 / Theorem 3.11(ii)"
    status := VerificationStatus.pending
    note :=
      "Missing source primitives for `IUT-I-II.prime-strips-frobenioids`, in " ++
        "consumer order: (1) a nontrivial geometric fundamental group with a " ++
        "surjection to the local absolute Galois group (the current projection is " ++
        "the identity, so the geometric kernel is trivial), consumed by the " ++
        "Frobenioid input of VerticalLogKummer and the K1/K2 realization; " ++
        "(2) prime strips over the places of a general number field, not only " ++
        "over the p-adic places of Q; (3) the categorical Frobenioid with its " ++
        "value functor and links; (4) arithmetic Frobenius data compatible with " ++
        "the log-shell; (5) the divisorial/realified value-monoid structure used " ++
        "by the K2 realification. None of these can be obtained by choosing an " ++
        "arbitrary type: each is a source construction with its own arithmetic " ++
        "content."
    dependsOn :=
      [ "IUT-I-II.prime-strips-frobenioids",
        "IUT-II.vertical-log-kummer-correspondence" ] }

end Audit

end LeanFormal.IUT
