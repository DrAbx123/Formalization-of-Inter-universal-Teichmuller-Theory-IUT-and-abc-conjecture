import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorPresentation
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorLocalTensor
import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalIdealFamily

/-!
# Realization of degree-n torsor arrows by actual equivariant maps

Layer 3, faithful bridge.  A TorsorArrow between two torsor presentations is
coordinate data (degree n, global multiplier f, integrality at all places).
This file shows that such an arrow gives an actual F^x-equivariant map of
torsor powers

  alpha : (T_1)^oT n ---> T_2

together with the local integrality condition at every place, expressed through
the canonical local tensor point map phi_n : (T_1)_v -> ((T_1)^oT n)_v of
Example36TorsorLocalTensor.

Boundary: the tensor power is the contracted product with the i0-coordinate
residual action (any i0, as in Example36TorsorTensorPower); no claim is made
about the global Frobenioid category or source objects.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open GTorsorTensor
open IsDedekindDomain NumberField
open LocalTensorPoint
open scoped NumberField

universe u v

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. Equivariant maps of torsors and their induced contraction maps -/

/-- A homomorphism of F^x-torsors: an equivariant map of the underlying types. -/
structure TorsorHom (T₁ T₂ : GTorsor Fˣ) where
  /-- The underlying map. -/
  toFun : T₁.carrier → T₂.carrier
  /-- Equivariance with respect to the F^x-actions. -/
  map_smul : ∀ (g : Fˣ) (x : T₁.carrier), toFun (g • x) = g • toFun x

namespace TorsorHom

variable {T₁ T₂ T₃ : GTorsor Fˣ}

/-- The homomorphism determined by a base point of the source and a point of
the target. -/
def ofPoint (x₁ : T₁.carrier) (y₂ : T₂.carrier) : TorsorHom T₁ T₂ where
  toFun := GTorsor.equivariantMapOfPoint T₁ T₂ x₁ y₂
  map_smul := GTorsor.equivariantMapOfPoint_smul T₁ T₂ x₁ y₂

omit [NumberField F] in
@[ext]
theorem ext (h k : TorsorHom T₁ T₂) (hfun : h.toFun = k.toFun) : h = k := by
  cases h
  cases k
  simp only at hfun
  subst hfun
  rfl

omit [NumberField F] in
@[simp]
theorem ofPoint_apply (x₁ : T₁.carrier) (y₂ : T₂.carrier) (x : T₁.carrier) :
    (ofPoint (T₁ := T₁) (T₂ := T₂) x₁ y₂).toFun x =
      GTorsor.equivariantMapOfPoint T₁ T₂ x₁ y₂ x :=
  rfl

omit [NumberField F] in
@[simp]
theorem ofPoint_apply_base (x₁ : T₁.carrier) (y₂ : T₂.carrier) :
    (ofPoint (T₁ := T₁) (T₂ := T₂) x₁ y₂).toFun x₁ = y₂ :=
  GTorsor.equivariantMapOfPoint_base T₁ T₂ x₁ y₂

/- Two torsor homomorphisms with the same value at one base point are equal. -/
omit [NumberField F] in
theorem ext_of_base (h k : TorsorHom T₁ T₂) (x₁ : T₁.carrier)
    (hx : h.toFun x₁ = k.toFun x₁) : h = k := by
  have hh : h.toFun = GTorsor.equivariantMapOfPoint T₁ T₂ x₁ (h.toFun x₁) :=
    GTorsor.eq_equivariantMapOfPoint T₁ T₂ h.toFun h.map_smul x₁
  have hk : k.toFun = GTorsor.equivariantMapOfPoint T₁ T₂ x₁ (k.toFun x₁) :=
    GTorsor.eq_equivariantMapOfPoint T₁ T₂ k.toFun k.map_smul x₁
  have hfun : h.toFun = k.toFun := by
    rw [hh, hk, hx]
  exact TorsorHom.ext h k hfun

/-- The map on local contracted products induced by a torsor homomorphism. -/
def mapLocalContraction {Gamma : Type v} [AddCommGroup Gamma] (h : TorsorHom T₁ T₂)
    (D : LocalValueData F Gamma) :
    LocalContraction D T₁ → LocalContraction D T₂ :=
  Quotient.map (fun p : Gamma × T₁.carrier => (p.1, h.toFun p.2)) (by
    intro p q hrel
    obtain ⟨g, rfl⟩ := hrel
    refine ⟨g, ?_⟩
    ext
    · rfl
    · exact h.map_smul g p.2)

omit [NumberField F] in
@[simp]
theorem mapLocalContraction_mk {Gamma : Type v} [AddCommGroup Gamma]
    (h : TorsorHom T₁ T₂) (D : LocalValueData F Gamma) (γ : Gamma) (x : T₁.carrier) :
    h.mapLocalContraction (D := D) (localContractionMk D T₁ (γ, x)) =
      localContractionMk D T₂ (γ, h.toFun x) :=
  rfl

/- Coordinate law: the induced map on local contracted products preserves the
local coordinate relative to the image of the base point. -/
omit [NumberField F] in
theorem localCoord_mapLocalContraction {Gamma : Type v} [AddCommGroup Gamma]
    (h : TorsorHom T₁ T₂) (D : LocalValueData F Gamma)
    (t : T₁.carrier) (p : LocalContraction D T₁) :
    localCoord D T₂ (h.toFun t) (h.mapLocalContraction D p) =
      localCoord D T₁ t p := by
  induction p using Quotient.inductionOn with
  | h q =>
      rw [mapLocalContraction_mk, localCoord_mk, localCoord_mk]
      have hcoord : T₂.coordinate (h.toFun t) (h.toFun q.2) =
          T₁.coordinate t q.2 := by
        have hx : q.2 = T₁.coordinate t q.2 • t :=
          (GTorsor.coordinate_spec T₁ t q.2).symm
        have hfp : h.toFun q.2 = T₁.coordinate t q.2 • h.toFun t := by
          conv_lhs => rw [hx]
          rw [h.map_smul]
        rw [hfp, GTorsor.coordinate_smul, GTorsor.coordinate_self, mul_one]
      rw [hcoord]

end TorsorHom

/-! ## 2. An arrow gives an actual equivariant map of tensor powers -/

variable {D : GlobalPlaceData F}

/-- The standard index for the contracted product of degree n > 0. -/
abbrev tensorPowerAtOfIndex {n : ℕ} (hn : 0 < n) : Fin n := ⟨0, hn⟩

/-- The actual equivariant map alpha : (T_1)^oT n -> T_2 determined by an
arrow: the base point is sent to the multiplier point. -/
def TorsorArrow.toTorsorHom {P₁ P₂ : TorsorPresentation D} (φ : TorsorArrow P₁ P₂) :
    TorsorHom (tensorPowerAt P₁.T φ.degree (tensorPowerAtOfIndex φ.positive_degree))
      P₂.T :=
  TorsorHom.ofPoint
    (tensorPoint P₁.T φ.degree P₁.base)
    (φ.multiplier • P₂.base)

@[simp]
theorem TorsorArrow.toTorsorHom_apply_base {P₁ P₂ : TorsorPresentation D}
    (φ : TorsorArrow P₁ P₂) :
    (φ.toTorsorHom).toFun (tensorPoint P₁.T φ.degree P₁.base) =
      φ.multiplier • P₂.base :=
  TorsorHom.ofPoint_apply_base _ _

theorem TorsorArrow.toTorsorHom_localCondition_finite {P₁ P₂ : TorsorPresentation D}
    (φ : TorsorArrow P₁ P₂) (v : HeightOneSpectrum (𝓞 F)) :
    localCoord (D.finiteValue v) P₂.T P₂.base
        ((φ.toTorsorHom).mapLocalContraction (D := D.finiteValue v)
          (localTensorPointMap (D.finiteValue v) P₁.T φ.degree
            (tensorPowerAtOfIndex φ.positive_degree) (P₁.finitePoint v))) -
      localCoord (D.finiteValue v) P₂.T P₂.base (P₂.finitePoint v) ∈
        (D.finiteValue v).cone := by
  set n := φ.degree
  set i0 : Fin n := tensorPowerAtOfIndex φ.positive_degree
  set Dv := D.finiteValue v
  have hbase : localCoord Dv P₂.T P₂.base
      ((φ.toTorsorHom).mapLocalContraction Dv
        (localTensorPointMap Dv P₁.T n i0 (P₁.finitePoint v))) =
      localCoord Dv P₂.T (φ.multiplier • P₂.base)
        ((φ.toTorsorHom).mapLocalContraction Dv
          (localTensorPointMap Dv P₁.T n i0 (P₁.finitePoint v))) +
        Dv.deltaAdd φ.multiplier := by
    rw [localCoord_basePoint_change]
    abel
  rw [hbase]
  have hmap : localCoord Dv P₂.T (φ.multiplier • P₂.base)
      ((φ.toTorsorHom).mapLocalContraction Dv
        (localTensorPointMap Dv P₁.T n i0 (P₁.finitePoint v))) =
      localCoord Dv (tensorPowerAt P₁.T n i0) (tensorPoint P₁.T n P₁.base)
        (localTensorPointMap Dv P₁.T n i0 (P₁.finitePoint v)) := by
    have hb : (φ.toTorsorHom).toFun (tensorPoint P₁.T n P₁.base) =
        φ.multiplier • P₂.base :=
      φ.toTorsorHom_apply_base
    rw [← hb]
    exact TorsorHom.localCoord_mapLocalContraction φ.toTorsorHom Dv
      (tensorPoint P₁.T n P₁.base) (localTensorPointMap Dv P₁.T n i0 (P₁.finitePoint v))
  rw [hmap, localCoord_localTensorPointMap]
  change (n • P₁.finiteCoord v + Dv.deltaAdd φ.multiplier - P₂.finiteCoord v) ∈
    Dv.cone
  have hexpr : n • P₁.finiteCoord v + Dv.deltaAdd φ.multiplier -
      P₂.finiteCoord v =
      Dv.deltaAdd φ.multiplier + n • P₁.finiteCoord v - P₂.finiteCoord v := by
    abel
  rw [hexpr]
  simpa only [LocalValueData.localInclusion] using φ.finite_incl v

theorem TorsorArrow.toTorsorHom_localCondition_infinite {P₁ P₂ : TorsorPresentation D}
    (φ : TorsorArrow P₁ P₂) (w : NumberField.InfinitePlace F) :
    localCoord (D.infiniteValue w) P₂.T P₂.base
        ((φ.toTorsorHom).mapLocalContraction (D.infiniteValue w)
          (localTensorPointMap (D.infiniteValue w) P₁.T φ.degree
            (tensorPowerAtOfIndex φ.positive_degree) (P₁.infinitePoint w))) -
      localCoord (D.infiniteValue w) P₂.T P₂.base (P₂.infinitePoint w) ∈
        (D.infiniteValue w).cone := by
  set n := φ.degree
  set i0 : Fin n := tensorPowerAtOfIndex φ.positive_degree
  set Dw := D.infiniteValue w
  have hbase : localCoord Dw P₂.T P₂.base
      ((φ.toTorsorHom).mapLocalContraction Dw
        (localTensorPointMap Dw P₁.T n i0 (P₁.infinitePoint w))) =
      localCoord Dw P₂.T (φ.multiplier • P₂.base)
        ((φ.toTorsorHom).mapLocalContraction Dw
          (localTensorPointMap Dw P₁.T n i0 (P₁.infinitePoint w))) +
        Dw.deltaAdd φ.multiplier := by
    rw [localCoord_basePoint_change]
    ring
  rw [hbase]
  have hmap : localCoord Dw P₂.T (φ.multiplier • P₂.base)
      ((φ.toTorsorHom).mapLocalContraction Dw
        (localTensorPointMap Dw P₁.T n i0 (P₁.infinitePoint w))) =
      localCoord Dw (tensorPowerAt P₁.T n i0) (tensorPoint P₁.T n P₁.base)
        (localTensorPointMap Dw P₁.T n i0 (P₁.infinitePoint w)) := by
    have hb : (φ.toTorsorHom).toFun (tensorPoint P₁.T n P₁.base) =
        φ.multiplier • P₂.base :=
      φ.toTorsorHom_apply_base
    rw [← hb]
    exact TorsorHom.localCoord_mapLocalContraction φ.toTorsorHom Dw
      (tensorPoint P₁.T n P₁.base) (localTensorPointMap Dw P₁.T n i0 (P₁.infinitePoint w))
  rw [hmap, localCoord_localTensorPointMap]
  change (n • P₁.infiniteCoord w + Dw.deltaAdd φ.multiplier - P₂.infiniteCoord w) ∈
    Dw.cone
  have hexpr : n • P₁.infiniteCoord w + Dw.deltaAdd φ.multiplier -
      P₂.infiniteCoord w =
      Dw.deltaAdd φ.multiplier + n • P₁.infiniteCoord w - P₂.infiniteCoord w := by
    ring
  rw [hexpr]
  simpa only [LocalValueData.localInclusion] using φ.infinite_incl w

/-! ## 3. The converse: an actual equivariant map with local integrality gives an arrow -/

namespace TorsorArrow

variable {P₁ P₂ : TorsorPresentation D}

/-- The multiplier determined by an equivariant map of tensor powers: the
coordinate of the image of the tensor base point. -/
def multiplierOfHom {n : ℕ} {i0 : Fin n}
    (α : TorsorHom (tensorPowerAt P₁.T n i0) P₂.T) : Fˣ :=
  P₂.T.coordinate P₂.base (α.toFun (tensorPoint P₁.T n P₁.base))

/-- The multiplier point is the image of the tensor base point. -/
theorem multiplierOfHom_smul {n : ℕ} {i0 : Fin n}
    (α : TorsorHom (tensorPowerAt P₁.T n i0) P₂.T) :
    multiplierOfHom (P₁ := P₁) (P₂ := P₂) α • P₂.base =
      α.toFun (tensorPoint P₁.T n P₁.base) :=
  GTorsor.coordinate_spec P₂.T P₂.base
    (α.toFun (tensorPoint P₁.T n P₁.base))

/-- Local integrality at a finite place, for the map induced by an equivariant
map of tensor powers. -/
theorem ofTorsorHom_finite_incl {n : ℕ} {i0 : Fin n}
    (α : TorsorHom (tensorPowerAt P₁.T n i0) P₂.T)
    (v : HeightOneSpectrum (𝓞 F))
    (hcond : localCoord (D.finiteValue v) P₂.T P₂.base
        (α.mapLocalContraction (D.finiteValue v)
          (localTensorPointMap (D.finiteValue v) P₁.T n i0 (P₁.finitePoint v))) -
      localCoord (D.finiteValue v) P₂.T P₂.base (P₂.finitePoint v) ∈
        (D.finiteValue v).cone) :
    (D.finiteValue v).localInclusion n
      (multiplierOfHom (P₁ := P₁) (P₂ := P₂) α)
      (P₁.finiteCoord v) (P₂.finiteCoord v) := by
  set Dv := D.finiteValue v
  set f := multiplierOfHom (P₁ := P₁) (P₂ := P₂) α
  have hbase : localCoord Dv P₂.T P₂.base
      (α.mapLocalContraction Dv
        (localTensorPointMap Dv P₁.T n i0 (P₁.finitePoint v))) =
      localCoord Dv P₂.T (f • P₂.base)
        (α.mapLocalContraction Dv
          (localTensorPointMap Dv P₁.T n i0 (P₁.finitePoint v))) + Dv.deltaAdd f := by
    rw [localCoord_basePoint_change]
    abel
  have hmap : localCoord Dv P₂.T (f • P₂.base)
      (α.mapLocalContraction Dv
        (localTensorPointMap Dv P₁.T n i0 (P₁.finitePoint v))) =
      localCoord Dv (tensorPowerAt P₁.T n i0) (tensorPoint P₁.T n P₁.base)
        (localTensorPointMap Dv P₁.T n i0 (P₁.finitePoint v)) := by
    rw [multiplierOfHom_smul (P₁ := P₁) (P₂ := P₂) α]
    exact TorsorHom.localCoord_mapLocalContraction α Dv
      (tensorPoint P₁.T n P₁.base) (localTensorPointMap Dv P₁.T n i0 (P₁.finitePoint v))
  have hc := hcond
  rw [hbase, hmap, localCoord_localTensorPointMap] at hc
  change (n • P₁.finiteCoord v + Dv.deltaAdd f - P₂.finiteCoord v) ∈ Dv.cone at hc
  have hexpr : n • P₁.finiteCoord v + Dv.deltaAdd f - P₂.finiteCoord v =
      Dv.deltaAdd f + n • P₁.finiteCoord v - P₂.finiteCoord v := by
    abel
  rw [hexpr] at hc
  simpa only [LocalValueData.localInclusion] using hc

/-- Local integrality at an archimedean place, for the map induced by an
equivariant map of tensor powers. -/
theorem ofTorsorHom_infinite_incl {n : ℕ} {i0 : Fin n}
    (α : TorsorHom (tensorPowerAt P₁.T n i0) P₂.T)
    (w : NumberField.InfinitePlace F)
    (hcond : localCoord (D.infiniteValue w) P₂.T P₂.base
        (α.mapLocalContraction (D.infiniteValue w)
          (localTensorPointMap (D.infiniteValue w) P₁.T n i0 (P₁.infinitePoint w))) -
      localCoord (D.infiniteValue w) P₂.T P₂.base (P₂.infinitePoint w) ∈
        (D.infiniteValue w).cone) :
    (D.infiniteValue w).localInclusion n
      (multiplierOfHom (P₁ := P₁) (P₂ := P₂) α)
      (P₁.infiniteCoord w) (P₂.infiniteCoord w) := by
  set Dw := D.infiniteValue w
  set f := multiplierOfHom (P₁ := P₁) (P₂ := P₂) α
  have hbase : localCoord Dw P₂.T P₂.base
      (α.mapLocalContraction Dw
        (localTensorPointMap Dw P₁.T n i0 (P₁.infinitePoint w))) =
      localCoord Dw P₂.T (f • P₂.base)
        (α.mapLocalContraction Dw
          (localTensorPointMap Dw P₁.T n i0 (P₁.infinitePoint w))) + Dw.deltaAdd f := by
    rw [localCoord_basePoint_change]
    ring
  have hmap : localCoord Dw P₂.T (f • P₂.base)
      (α.mapLocalContraction Dw
        (localTensorPointMap Dw P₁.T n i0 (P₁.infinitePoint w))) =
      localCoord Dw (tensorPowerAt P₁.T n i0) (tensorPoint P₁.T n P₁.base)
        (localTensorPointMap Dw P₁.T n i0 (P₁.infinitePoint w)) := by
    rw [multiplierOfHom_smul (P₁ := P₁) (P₂ := P₂) α]
    exact TorsorHom.localCoord_mapLocalContraction α Dw
      (tensorPoint P₁.T n P₁.base) (localTensorPointMap Dw P₁.T n i0 (P₁.infinitePoint w))
  have hc := hcond
  rw [hbase, hmap, localCoord_localTensorPointMap] at hc
  change (n • P₁.infiniteCoord w + Dw.deltaAdd f - P₂.infiniteCoord w) ∈ Dw.cone at hc
  have hexpr : n • P₁.infiniteCoord w + Dw.deltaAdd f - P₂.infiniteCoord w =
      Dw.deltaAdd f + n • P₁.infiniteCoord w - P₂.infiniteCoord w := by
    ring
  rw [hexpr] at hc
  simpa only [LocalValueData.localInclusion] using hc

/-- The torsor arrow associated with an equivariant map of tensor powers and
its local integrality conditions. -/
def ofTorsorHom {n : ℕ} {i0 : Fin n}
    (α : TorsorHom (tensorPowerAt P₁.T n i0) P₂.T)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      localCoord (D.finiteValue v) P₂.T P₂.base
        (α.mapLocalContraction (D.finiteValue v)
          (localTensorPointMap (D.finiteValue v) P₁.T n i0 (P₁.finitePoint v))) -
      localCoord (D.finiteValue v) P₂.T P₂.base (P₂.finitePoint v) ∈
        (D.finiteValue v).cone)
    (hinf : ∀ w : NumberField.InfinitePlace F,
      localCoord (D.infiniteValue w) P₂.T P₂.base
        (α.mapLocalContraction (D.infiniteValue w)
          (localTensorPointMap (D.infiniteValue w) P₁.T n i0 (P₁.infinitePoint w))) -
      localCoord (D.infiniteValue w) P₂.T P₂.base (P₂.infinitePoint w) ∈
        (D.infiniteValue w).cone) :
    TorsorArrow P₁ P₂ where
  degree := n
  positive_degree := lt_of_le_of_lt (Nat.zero_le _) i0.isLt
  multiplier := multiplierOfHom (P₁ := P₁) (P₂ := P₂) α
  finite_incl v := ofTorsorHom_finite_incl α v (hfin v)
  infinite_incl w := ofTorsorHom_infinite_incl α w (hinf w)

end TorsorArrow

/-! ## 4. The two constructions are mutually inverse -/

namespace TorsorHom

omit [NumberField F] in
/-- A torsor homomorphism equals the homomorphism determined by any base point
and its image. -/
theorem eq_ofPoint_self {T₁ T₂ : GTorsor Fˣ} (α : TorsorHom T₁ T₂) (x : T₁.carrier) :
    α = TorsorHom.ofPoint x (α.toFun x) := by
  apply TorsorHom.ext
  funext y
  exact congrFun (GTorsor.eq_equivariantMapOfPoint T₁ T₂ α.toFun α.map_smul x) y

end TorsorHom

namespace TorsorArrow

variable {P₁ P₂ : TorsorPresentation D}

/-- The local integrality condition for an equivariant map of tensor powers. -/
def TensorHomLocalCondition {n : ℕ} {i0 : Fin n}
    (α : TorsorHom (tensorPowerAt P₁.T n i0) P₂.T) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 F),
    localCoord (D.finiteValue v) P₂.T P₂.base
      (α.mapLocalContraction (D.finiteValue v)
        (localTensorPointMap (D.finiteValue v) P₁.T n i0 (P₁.finitePoint v))) -
    localCoord (D.finiteValue v) P₂.T P₂.base (P₂.finitePoint v) ∈
      (D.finiteValue v).cone) ∧
  (∀ w : NumberField.InfinitePlace F,
    localCoord (D.infiniteValue w) P₂.T P₂.base
      (α.mapLocalContraction (D.infiniteValue w)
        (localTensorPointMap (D.infiniteValue w) P₁.T n i0 (P₁.infinitePoint w))) -
    localCoord (D.infiniteValue w) P₂.T P₂.base (P₂.infinitePoint w) ∈
      (D.infiniteValue w).cone)

/-- The local condition of the equivariant map of an arrow. -/
theorem arrowLocalCondition (φ : TorsorArrow P₁ P₂) :
    TensorHomLocalCondition (P₁ := P₁) (P₂ := P₂) φ.toTorsorHom := by
  unfold TensorHomLocalCondition
  exact ⟨fun v => φ.toTorsorHom_localCondition_finite v,
    fun w => φ.toTorsorHom_localCondition_infinite w⟩

/-- The arrow constructed from an equivariant map has the same equivariant map
(at the standard tensor index). -/
theorem toTorsorHom_ofTorsorHom {n : ℕ} (hn : 0 < n)
    (α : TorsorHom (tensorPowerAt P₁.T n (tensorPowerAtOfIndex hn)) P₂.T)
    (h : TensorHomLocalCondition (P₁ := P₁) (P₂ := P₂) α) :
    (ofTorsorHom (P₁ := P₁) (P₂ := P₂)
        (n := n) (i0 := tensorPowerAtOfIndex hn) α h.1 h.2).toTorsorHom = α := by
  rw [show (ofTorsorHom (P₁ := P₁) (P₂ := P₂)
        (n := n) (i0 := tensorPowerAtOfIndex hn) α h.1 h.2).toTorsorHom =
      TorsorHom.ofPoint (tensorPoint P₁.T n P₁.base)
        (multiplierOfHom (P₁ := P₁) (P₂ := P₂) α • P₂.base) from rfl]
  rw [multiplierOfHom_smul]
  exact (TorsorHom.eq_ofPoint_self α (tensorPoint P₁.T n P₁.base)).symm

/- The arrow constructed from the equivariant map of an arrow is the arrow itself.
Degree and multiplier agree; a TorsorArrow is determined by these two data. -/
theorem ofTorsorHom_toTorsorHom (φ : TorsorArrow P₁ P₂) :
    (ofTorsorHom (P₁ := P₁) (P₂ := P₂)
        (n := φ.degree) (i0 := tensorPowerAtOfIndex φ.positive_degree)
        φ.toTorsorHom
        (arrowLocalCondition (P₁ := P₁) (P₂ := P₂) φ).1
        (arrowLocalCondition (P₁ := P₁) (P₂ := P₂) φ).2) = φ := by
  apply TorsorArrow.ext
  · rfl
  · show multiplierOfHom (P₁ := P₁) (P₂ := P₂) φ.toTorsorHom = φ.multiplier
    rw [multiplierOfHom, TorsorArrow.toTorsorHom_apply_base]
    rw [GTorsor.coordinate_smul, GTorsor.coordinate_self, mul_one]

/-- The faithful dictionary: degree-n torsor arrows between two presentations
are exactly the equivariant maps of the standard n-fold tensor power together
with the local integrality condition at all places. -/
theorem exists_torsorArrow_iff_exists_torsorHom (n : ℕ) (hn : 0 < n) :
    (∃ φ : TorsorArrow P₁ P₂, φ.degree = n) ↔
      ∃ α : TorsorHom (tensorPowerAt P₁.T n (tensorPowerAtOfIndex hn)) P₂.T,
        TensorHomLocalCondition (P₁ := P₁) (P₂ := P₂) α := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨φ.toTorsorHom, arrowLocalCondition (P₁ := P₁) (P₂ := P₂) φ⟩
  · rintro ⟨α, h⟩
    exact ⟨ofTorsorHom (P₁ := P₁) (P₂ := P₂)
      (n := n) (i0 := tensorPowerAtOfIndex hn) α h.1 h.2, rfl⟩

end TorsorArrow

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
