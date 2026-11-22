import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Source-faithful times-mu prime-strips and their full poly-isomorphisms

IUT III, Theorem 3.11(i) and Remark 3.11.1(iii) (PDF 160-161) work with
F-turnstile-times-mu-prime-strips and with full poly-isomorphisms between
them; Corollary 3.12, Step (xi-b) (PDF 181-182) uses the same carrier for
the F-turnstile part of the link.  This file provides that carrier layer:

* `SourceFTimesMuPrimeStrip`: an F-prime-strip together with the O-times-mu
  fibers, the quotient link from the unit group with finite-order kernel,
  the descended action, and the realified degree;
* `SourceFTimesMuPrimeStripEquivalence` and the quotient type
  `SourceFTimesMuPrimeStripFullPolyIsomorphism`: full poly-isomorphism
  classes with their category laws and canonical lifting;
* `SourceFTimesMuPrimeStripPolyIsomorphismSquare`: the commuting square of
  Remark 3.11.1(iii), its upper-horizontal assembly, and the anchored
  squares `processionInclusionSquare` and `logThetaLatticeSquare` built from
  the procession and log-Theta lattice data of this repository.

* `SourceFTimesMuPrimeStripRem3102Diagram`: the conditional form of the
  Remark 3.10.2 diagram at the times-mu level, with the IPL composite
  `iplLink` and the intermediate-strip dual roles.

The clause "induced by operations in the algorithm" is not formalized here:
what is formalized is the conditional contract above; the algorithmic
provenance of its arrows and the named bridge to the source-level link
factorization remain gaps, recorded in the accompanying coordination report.
-/

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon ui

section UnitConversionLemmas

universe u1 u2 u3

/-- `Units.mapEquiv` turns composition into composition. -/
theorem unitsMapEquiv_trans {M : Type u1} {N : Type u2} {P : Type u3}
    [Monoid M] [Monoid N] [Monoid P] (e : M ≃* N) (f : N ≃* P) :
    Units.mapEquiv (e.trans f) = (Units.mapEquiv e).trans (Units.mapEquiv f) := by
  ext u
  simp only [Units.coe_mapEquiv, MulEquiv.trans_apply]

/-- `Units.mapEquiv` preserves the identity. -/
theorem unitsMapEquiv_refl {M : Type u1} [Monoid M] :
    Units.mapEquiv (MulEquiv.refl M) = MulEquiv.refl Mˣ := by
  ext u
  simp only [Units.coe_mapEquiv, MulEquiv.refl_apply]

end UnitConversionLemmas

variable {V : Type uv}

namespace FPrimeStripEquiv

variable {F F' : FPrimeStrip.{umon, uv, upi} V}

/-- Componentwise extensionality for `FPrimeStripEquiv`. -/
theorem ext_map {φ ψ : FPrimeStripEquiv F F'}
    (hPi : ∀ v, φ.isoPi v = ψ.isoPi v) (hG : ∀ v, φ.isoG v = ψ.isoG v)
    (hMon : ∀ v, φ.isoMon v = ψ.isoMon v) : φ = ψ := by
  cases φ
  cases ψ
  simp only at hPi hG hMon
  congr
  all_goals first
    | exact funext hPi
    | exact funext hG
    | exact funext hMon

/-- The unit-group action of an equivalence is compatible with the units of
    the mono-analytic action. -/
theorem unitsAction_compat (φ : FPrimeStripEquiv F F') (v : V)
    (g : F.toDPrimeStrip.Pi v) (u : (F.Mon v)ˣ) :
    Units.mapEquiv (φ.isoMon v) (FPrimeStrip.unitsAction F v g u) =
      FPrimeStrip.unitsAction F' v (φ.isoPi v g) (Units.mapEquiv (φ.isoMon v) u) := by
  ext
  simp only [Units.coe_mapEquiv, FPrimeStrip.unitsAction_val]
  exact φ.compatAction v g (u : F.Mon v)

theorem trans_symm (φ : FPrimeStripEquiv F F') :
    FPrimeStripEquiv.trans φ φ.symm = FPrimeStripEquiv.refl F := by
  apply ext_map
  · intro v
    show (φ.isoPi v).trans (φ.symm.isoPi v) = (FPrimeStripEquiv.refl F).isoPi v
    rw [show φ.symm.isoPi v = (φ.isoPi v).symm from rfl]
    exact MulEquiv.self_trans_symm (φ.isoPi v)
  · intro v
    show (φ.isoG v).trans (φ.symm.isoG v) = (FPrimeStripEquiv.refl F).isoG v
    rw [show φ.symm.isoG v = (φ.isoG v).symm from rfl]
    exact MulEquiv.self_trans_symm (φ.isoG v)
  · intro v
    show (φ.isoMon v).trans (φ.symm.isoMon v) = (FPrimeStripEquiv.refl F).isoMon v
    rw [show φ.symm.isoMon v = (φ.isoMon v).symm from rfl]
    exact MulEquiv.self_trans_symm (φ.isoMon v)

theorem symm_trans (φ : FPrimeStripEquiv F F') :
    FPrimeStripEquiv.trans φ.symm φ = FPrimeStripEquiv.refl F' := by
  apply ext_map
  · intro v
    show (φ.symm.isoPi v).trans (φ.isoPi v) = (FPrimeStripEquiv.refl F').isoPi v
    rw [show φ.symm.isoPi v = (φ.isoPi v).symm from rfl]
    exact MulEquiv.symm_trans_self (φ.isoPi v)
  · intro v
    show (φ.symm.isoG v).trans (φ.isoG v) = (FPrimeStripEquiv.refl F').isoG v
    rw [show φ.symm.isoG v = (φ.isoG v).symm from rfl]
    exact MulEquiv.symm_trans_self (φ.isoG v)
  · intro v
    show (φ.symm.isoMon v).trans (φ.isoMon v) = (FPrimeStripEquiv.refl F').isoMon v
    rw [show φ.symm.isoMon v = (φ.isoMon v).symm from rfl]
    exact MulEquiv.symm_trans_self (φ.isoMon v)

end FPrimeStripEquiv

namespace TimesMuQuotient

universe uM uM2 uM3

variable {U : Type uM} {U' : Type uM2} {U'' : Type uM3}
variable [CommGroup U] [CommGroup U'] [CommGroup U'']

/-- Transport of the torsion quotient along a multiplicative equivalence. -/
def congr (e : U ≃* U') : TimesMuQuotient U ≃* TimesMuQuotient U' :=
  QuotientGroup.congr (CommGroup.torsion U) (CommGroup.torsion U') e e.map_torsion

@[simp] theorem congr_quotientMap (e : U ≃* U') (u : U) :
    congr e (quotientMap u) = quotientMap (e u) := rfl

@[simp] theorem congr_refl :
    congr (MulEquiv.refl U) = MulEquiv.refl (TimesMuQuotient U) := by
  ext x
  refine Quotient.inductionOn x ?_
  intro u
  rfl

@[simp] theorem congr_trans (e : U ≃* U') (f : U' ≃* U'') :
    congr (e.trans f) = (congr e).trans (congr f) := by
  ext x
  refine Quotient.inductionOn x ?_
  intro u
  rfl

theorem congr_symm (e : U ≃* U') :
    congr e.symm = (congr e).symm := by
  ext x
  apply (congr e).injective
  rw [MulEquiv.apply_symm_apply]
  rw [← MulEquiv.trans_apply (congr e.symm) (congr e) x]
  rw [← congr_trans e.symm e, MulEquiv.symm_trans_self, congr_refl]
  exact MulEquiv.refl_apply x

end TimesMuQuotient

structure SourceFTimesMuPrimeStrip (V : Type uv)
    extends FPrimeStrip.{umon, uv, upi} V where
  timesMu : V → Type umon
  [commGroupTimesMu : ∀ v, CommGroup (timesMu v)]
  timesMuQuotientMap : ∀ v, (toFPrimeStrip.Mon v)ˣ →* timesMu v
  timesMuQuotientMap_surjective : ∀ v, Function.Surjective (timesMuQuotientMap v)
  timesMuQuotientMap_ker : ∀ v,
    MonoidHom.ker (timesMuQuotientMap v) =
      CommGroup.torsion ((toFPrimeStrip.Mon v)ˣ)
  timesMuAction : ∀ v, toFPrimeStrip.toDPrimeStrip.Pi v →* MulAut (timesMu v)
  timesMuAction_quotientMap : ∀ v (g : toFPrimeStrip.toDPrimeStrip.Pi v)
      (u : (toFPrimeStrip.Mon v)ˣ),
    timesMuAction v g (timesMuQuotientMap v u) =
      timesMuQuotientMap v (FPrimeStrip.unitsAction toFPrimeStrip v g u)
  timesMuDegree : ∀ v, timesMu v →* Multiplicative ℝ
  timesMuDegree_quotientMap : ∀ v (u : (toFPrimeStrip.Mon v)ˣ),
    timesMuDegree v (timesMuQuotientMap v u) =
      (toFPrimeStrip.degree v) (u : toFPrimeStrip.Mon v)

attribute [instance] SourceFTimesMuPrimeStrip.commGroupTimesMu

namespace SourceFTimesMuPrimeStrip

variable (S : SourceFTimesMuPrimeStrip V)

theorem timesMuQuotientMap_eq_one_iff (v : V) (u : (S.toFPrimeStrip.Mon v)ˣ) :
    S.timesMuQuotientMap v u = 1 ↔ IsOfFinOrder u := by
  rw [← MonoidHom.mem_ker, S.timesMuQuotientMap_ker v, CommGroup.mem_torsion]

end SourceFTimesMuPrimeStrip

namespace FPrimeStrip

variable (F : FPrimeStrip.{umon, uv, upi} V) (v : V)

/-- Torsion units have realified degree one. -/
theorem torsion_units_degree_eq_one (u : (F.Mon v)ˣ)
    (hu : u ∈ CommGroup.torsion (F.Mon v)ˣ) :
    (F.degree v) (u : F.Mon v) = 1 := by
  obtain ⟨n, hnpos, hn⟩ :=
    isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion u).mp hu)
  have hp : ((F.degree v) (u : F.Mon v)) ^ n = 1 := by
    have h := congrArg (fun w : (F.Mon v)ˣ => F.degree v (w : F.Mon v)) hn
    simpa only [map_pow, Units.val_pow_eq_pow_val, Units.val_one, map_one] using h
  exact (pow_eq_one_iff_left hnpos.ne').mp hp

/-- The realified degree homomorphism of the unit group. -/
def unitDegreeHom : (F.Mon v)ˣ →* Multiplicative ℝ where
  toFun u := F.degree v (u : F.Mon v)
  map_one' := by rw [Units.val_one, map_one]
  map_mul' a b := by rw [Units.val_mul, map_mul]

theorem unitDegreeHom_torsion_le :
    CommGroup.torsion (F.Mon v)ˣ ≤ MonoidHom.ker (unitDegreeHom F v) :=
  fun u hu => torsion_units_degree_eq_one F v u hu

/-- The descended realified degree on the torsion quotient. -/
def timesMuDegreeOfUnits : TimesMuQuotient (F.Mon v)ˣ →* Multiplicative ℝ :=
  QuotientGroup.lift (CommGroup.torsion (F.Mon v)ˣ) (unitDegreeHom F v)
    (unitDegreeHom_torsion_le F v)

theorem timesMuDegreeOfUnits_quotientMap (u : (F.Mon v)ˣ) :
    timesMuDegreeOfUnits F v (TimesMuQuotient.quotientMap u) =
      F.degree v (u : F.Mon v) := rfl

end FPrimeStrip

namespace SourceFTimesMuPrimeStrip

/-- The canonical times-mu prime-strip determined by an F-prime-strip: the
    O-times-mu fibers are the quotients of the unit groups by their torsion
    subgroups. -/
def canonical (F : FPrimeStrip.{umon, uv, upi} V) :
    SourceFTimesMuPrimeStrip V where
  toFPrimeStrip := F
  timesMu := fun v => TimesMuQuotient (F.Mon v)ˣ
  commGroupTimesMu := fun v => inferInstance
  timesMuQuotientMap := fun v => TimesMuQuotient.quotientMap
  timesMuQuotientMap_surjective := fun v => TimesMuQuotient.quotientMap_surjective
  timesMuQuotientMap_ker := fun v => TimesMuQuotient.quotientMap_ker
  timesMuAction := fun v => F.timesMuAction v
  timesMuAction_quotientMap := by
    intro v g u
    exact F.timesMuAction_quotientMap v g u
  timesMuDegree := fun v => F.timesMuDegreeOfUnits v
  timesMuDegree_quotientMap := by
    intro v u
    exact F.timesMuDegreeOfUnits_quotientMap v u

end SourceFTimesMuPrimeStrip

/-- A full-poly representative: a times-mu prime-strip equivalence. -/
structure SourceFTimesMuPrimeStripEquivalence (S T : SourceFTimesMuPrimeStrip V) where
  toF : FPrimeStripEquiv S.toFPrimeStrip T.toFPrimeStrip
  isoTimesMu : ∀ v, S.timesMu v ≃* T.timesMu v
  compatQuotientMap : ∀ v (u : (S.toFPrimeStrip.Mon v)ˣ),
    isoTimesMu v (S.timesMuQuotientMap v u) =
      T.timesMuQuotientMap v (Units.mapEquiv (toF.isoMon v) u)
  compatAction : ∀ v (g : S.toFPrimeStrip.toDPrimeStrip.Pi v)
      (x : S.timesMu v),
    isoTimesMu v (S.timesMuAction v g x) =
      T.timesMuAction v (toF.isoPi v g) (isoTimesMu v x)
  compatDegree : ∀ v (x : S.timesMu v),
    T.timesMuDegree v (isoTimesMu v x) = S.timesMuDegree v x

namespace SourceFTimesMuPrimeStripEquivalence

variable {S T U W : SourceFTimesMuPrimeStrip V}

def refl (S : SourceFTimesMuPrimeStrip V) :
    SourceFTimesMuPrimeStripEquivalence S S where
  toF := FPrimeStripEquiv.refl S.toFPrimeStrip
  isoTimesMu := fun v => MulEquiv.refl (S.timesMu v)
  compatQuotientMap := by
    intro v u
    have hmon : (FPrimeStripEquiv.refl S.toFPrimeStrip).isoMon v =
        MulEquiv.refl (S.toFPrimeStrip.Mon v) := rfl
    rw [hmon]
    have h : Units.mapEquiv (MulEquiv.refl (S.toFPrimeStrip.Mon v)) u = u := by
      rw [unitsMapEquiv_refl]
      exact MulEquiv.refl_apply u
    rw [h]
    exact MulEquiv.refl_apply _
  compatAction := by
    intro v g x
    rfl
  compatDegree := by
    intro v x
    rfl

def symm (φ : SourceFTimesMuPrimeStripEquivalence S T) :
    SourceFTimesMuPrimeStripEquivalence T S where
  toF := φ.toF.symm
  isoTimesMu := fun v => (φ.isoTimesMu v).symm
  compatQuotientMap := by
    intro v u
    apply (φ.isoTimesMu v).injective
    rw [MulEquiv.apply_symm_apply]
    rw [φ.compatQuotientMap]
    show T.timesMuQuotientMap v u =
      T.timesMuQuotientMap v
        (Units.mapEquiv (φ.toF.isoMon v)
          (Units.mapEquiv (φ.toF.isoMon v).symm u))
    rw [show Units.mapEquiv (φ.toF.isoMon v)
        (Units.mapEquiv (φ.toF.isoMon v).symm u) = u from by
      ext
      rw [Units.coe_mapEquiv, Units.coe_mapEquiv, MulEquiv.apply_symm_apply]]
  compatAction := by
    intro v g x
    have h := φ.compatAction v ((φ.toF.isoPi v).symm g) ((φ.isoTimesMu v).symm x)
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h
    apply (φ.isoTimesMu v).injective
    rw [MulEquiv.apply_symm_apply]
    exact h.symm
  compatDegree := by
    intro v x
    rw [← φ.compatDegree v ((φ.isoTimesMu v).symm x), MulEquiv.apply_symm_apply]

def trans (φ : SourceFTimesMuPrimeStripEquivalence S T)
    (ψ : SourceFTimesMuPrimeStripEquivalence T U) :
    SourceFTimesMuPrimeStripEquivalence S U where
  toF := φ.toF.trans ψ.toF
  isoTimesMu := fun v => (φ.isoTimesMu v).trans (ψ.isoTimesMu v)
  compatQuotientMap := by
    intro v u
    rw [MulEquiv.trans_apply, φ.compatQuotientMap, ψ.compatQuotientMap]
    congr 1
  compatAction := by
    intro v g x
    show ψ.isoTimesMu v (φ.isoTimesMu v (S.timesMuAction v g x)) =
      U.timesMuAction v (ψ.toF.isoPi v (φ.toF.isoPi v g))
        (ψ.isoTimesMu v (φ.isoTimesMu v x))
    rw [φ.compatAction, ψ.compatAction]
  compatDegree := by
    intro v x
    rw [MulEquiv.trans_apply, ψ.compatDegree, φ.compatDegree]

/-- Canonical lifting of an F-prime-strip equivalence to a times-mu
    prime-strip equivalence between the canonical instances. -/
def canonicalLift {F F' : FPrimeStrip.{umon, uv, upi} V}
    (φ : FPrimeStripEquiv F F') :
    SourceFTimesMuPrimeStripEquivalence
      (SourceFTimesMuPrimeStrip.canonical F)
      (SourceFTimesMuPrimeStrip.canonical F') where
  toF := φ
  isoTimesMu := fun v => TimesMuQuotient.congr (Units.mapEquiv (φ.isoMon v))
  compatQuotientMap := by
    intro v u
    exact TimesMuQuotient.congr_quotientMap (Units.mapEquiv (φ.isoMon v)) u
  compatAction := by
    intro v g x
    refine Quotient.inductionOn x ?_
    intro u
    show TimesMuQuotient.congr (Units.mapEquiv (φ.isoMon v))
        (F.timesMuAction v g (TimesMuQuotient.quotientMap u)) =
      F'.timesMuAction v (φ.isoPi v g)
        (TimesMuQuotient.congr (Units.mapEquiv (φ.isoMon v))
          (TimesMuQuotient.quotientMap u))
    simp only [TimesMuQuotient.congr_quotientMap,
      FPrimeStrip.timesMuAction_quotientMap]
    exact congrArg TimesMuQuotient.quotientMap
      (FPrimeStripEquiv.unitsAction_compat φ v g u)
  compatDegree := by
    intro v x
    refine Quotient.inductionOn x ?_
    intro u
    show F'.degree v ((Units.mapEquiv (φ.isoMon v) u : (F'.Mon v)ˣ) : F'.Mon v) =
      F.degree v (u : F.Mon v)
    rw [Units.coe_mapEquiv]
    exact φ.compatDegree v (u : F.Mon v)

/-- The times-mu component of a trans-composite of two canonical lifts, in
    the `congr`-bridge form used by the full poly-isomorphism laws: it is the
    trans of the torsion-quotient transports of the unit maps. -/
theorem isoTimesMu_canonicalLift_trans {F F' F'' : FPrimeStrip.{umon, uv, upi} V}
    (φ : FPrimeStripEquiv F F') (ψ : FPrimeStripEquiv F' F'') (v : V) :
    ((canonicalLift φ).trans (canonicalLift ψ)).isoTimesMu v =
      (TimesMuQuotient.congr (Units.mapEquiv (φ.isoMon v))).trans
        (TimesMuQuotient.congr (Units.mapEquiv (ψ.isoMon v))) :=
  rfl

/-- Two representatives are naturally isomorphic when they have the same
    F-prime-strip component and the same times-mu component. -/
structure NaturallyIsomorphic (φ ψ : SourceFTimesMuPrimeStripEquivalence S T) : Prop where
  toF_eq : φ.toF = ψ.toF
  isoTimesMu_eq : ∀ v, φ.isoTimesMu v = ψ.isoTimesMu v

namespace NaturallyIsomorphic

variable {φ ψ χ : SourceFTimesMuPrimeStripEquivalence S T}

theorem refl (φ : SourceFTimesMuPrimeStripEquivalence S T) :
    NaturallyIsomorphic φ φ where
  toF_eq := rfl
  isoTimesMu_eq := fun v => rfl

theorem symm (h : NaturallyIsomorphic φ ψ) : NaturallyIsomorphic ψ φ where
  toF_eq := h.toF_eq.symm
  isoTimesMu_eq := fun v => (h.isoTimesMu_eq v).symm

theorem trans (h₁ : NaturallyIsomorphic φ ψ) (h₂ : NaturallyIsomorphic ψ χ) :
    NaturallyIsomorphic φ χ where
  toF_eq := h₁.toF_eq.trans h₂.toF_eq
  isoTimesMu_eq := fun v => (h₁.isoTimesMu_eq v).trans (h₂.isoTimesMu_eq v)

theorem congr_symm (h : NaturallyIsomorphic φ ψ) :
    NaturallyIsomorphic φ.symm ψ.symm where
  toF_eq := congrArg FPrimeStripEquiv.symm h.toF_eq
  isoTimesMu_eq := fun v => congrArg MulEquiv.symm (h.isoTimesMu_eq v)

theorem comp {φ₁ φ₂ : SourceFTimesMuPrimeStripEquivalence S T}
    {ψ₁ ψ₂ : SourceFTimesMuPrimeStripEquivalence T U}
    (hφ : NaturallyIsomorphic φ₁ φ₂) (hψ : NaturallyIsomorphic ψ₁ ψ₂) :
    NaturallyIsomorphic (φ₁.trans ψ₁) (φ₂.trans ψ₂) where
  toF_eq := by
    show FPrimeStripEquiv.trans φ₁.toF ψ₁.toF =
      FPrimeStripEquiv.trans φ₂.toF ψ₂.toF
    rw [hφ.toF_eq, hψ.toF_eq]
  isoTimesMu_eq := fun v => by
    show (φ₁.isoTimesMu v).trans (ψ₁.isoTimesMu v) =
      (φ₂.isoTimesMu v).trans (ψ₂.isoTimesMu v)
    rw [hφ.isoTimesMu_eq v, hψ.isoTimesMu_eq v]

theorem id_comp (φ : SourceFTimesMuPrimeStripEquivalence S T) :
    NaturallyIsomorphic
      ((SourceFTimesMuPrimeStripEquivalence.refl S).trans φ) φ where
  toF_eq := rfl
  isoTimesMu_eq := fun v => rfl

theorem comp_id (φ : SourceFTimesMuPrimeStripEquivalence S T) :
    NaturallyIsomorphic
      (φ.trans (SourceFTimesMuPrimeStripEquivalence.refl T)) φ where
  toF_eq := rfl
  isoTimesMu_eq := fun v => rfl

theorem assoc (φ : SourceFTimesMuPrimeStripEquivalence S T)
    (ψ : SourceFTimesMuPrimeStripEquivalence T U)
    (χ : SourceFTimesMuPrimeStripEquivalence U W) :
    NaturallyIsomorphic ((φ.trans ψ).trans χ) (φ.trans (ψ.trans χ)) where
  toF_eq := rfl
  isoTimesMu_eq := fun v => rfl

/-- Two trans-composites of canonical lifts are naturally isomorphic as soon
    as their F-prime-strip composites agree; the intermediate F-prime-strips
    of the two composites may differ. -/
theorem congr_trans {F F₁ F₂ F'' : FPrimeStrip.{umon, uv, upi} V}
    {φ₁ : FPrimeStripEquiv F F₁} {ψ₁ : FPrimeStripEquiv F₁ F''}
    {φ₂ : FPrimeStripEquiv F F₂} {ψ₂ : FPrimeStripEquiv F₂ F''}
    (h : FPrimeStripEquiv.trans φ₁ ψ₁ = FPrimeStripEquiv.trans φ₂ ψ₂) :
    NaturallyIsomorphic
      ((SourceFTimesMuPrimeStripEquivalence.canonicalLift φ₁).trans
        (SourceFTimesMuPrimeStripEquivalence.canonicalLift ψ₁))
      ((SourceFTimesMuPrimeStripEquivalence.canonicalLift φ₂).trans
        (SourceFTimesMuPrimeStripEquivalence.canonicalLift ψ₂)) where
  toF_eq := h
  isoTimesMu_eq := fun v => by
    rw [isoTimesMu_canonicalLift_trans φ₁ ψ₁ v,
      isoTimesMu_canonicalLift_trans φ₂ ψ₂ v]
    have hmon := congrFun (congrArg FPrimeStripEquiv.isoMon h) v
    dsimp only [FPrimeStripEquiv.trans] at hmon
    have hcongr := congrArg TimesMuQuotient.congr (congrArg Units.mapEquiv hmon)
    rw [unitsMapEquiv_trans, unitsMapEquiv_trans, TimesMuQuotient.congr_trans,
      TimesMuQuotient.congr_trans] at hcongr
    exact hcongr

theorem canonicalLift_trans {F F' F'' : FPrimeStrip.{umon, uv, upi} V}
    (φ : FPrimeStripEquiv F F') (ψ : FPrimeStripEquiv F' F'') :
    NaturallyIsomorphic
      ((SourceFTimesMuPrimeStripEquivalence.canonicalLift φ).trans
        (SourceFTimesMuPrimeStripEquivalence.canonicalLift ψ))
      (SourceFTimesMuPrimeStripEquivalence.canonicalLift
        (FPrimeStripEquiv.trans φ ψ)) where
  toF_eq := rfl
  isoTimesMu_eq := fun v => by
    show (TimesMuQuotient.congr (Units.mapEquiv (φ.isoMon v))).trans
        (TimesMuQuotient.congr (Units.mapEquiv (ψ.isoMon v))) =
      TimesMuQuotient.congr (Units.mapEquiv ((φ.isoMon v).trans (ψ.isoMon v)))
    simp only [unitsMapEquiv_trans (φ.isoMon v) (ψ.isoMon v),
      TimesMuQuotient.congr_trans]

theorem canonicalLift_refl {F : FPrimeStrip.{umon, uv, upi} V} :
    NaturallyIsomorphic
      (SourceFTimesMuPrimeStripEquivalence.canonicalLift (FPrimeStripEquiv.refl F))
      (SourceFTimesMuPrimeStripEquivalence.refl
        (SourceFTimesMuPrimeStrip.canonical F)) where
  toF_eq := rfl
  isoTimesMu_eq := fun v => by
    show TimesMuQuotient.congr (Units.mapEquiv (MulEquiv.refl (F.Mon v))) =
      MulEquiv.refl (TimesMuQuotient (F.Mon v)ˣ)
    simp only [unitsMapEquiv_refl, TimesMuQuotient.congr_refl]

theorem canonicalLift_trans_symm {F F' : FPrimeStrip.{umon, uv, upi} V}
    (φ : FPrimeStripEquiv F F') :
    NaturallyIsomorphic
      ((SourceFTimesMuPrimeStripEquivalence.canonicalLift φ).trans
        (SourceFTimesMuPrimeStripEquivalence.canonicalLift φ.symm))
      (SourceFTimesMuPrimeStripEquivalence.refl
        (SourceFTimesMuPrimeStrip.canonical F)) where
  toF_eq := FPrimeStripEquiv.trans_symm φ
  isoTimesMu_eq := fun v => by
    show (TimesMuQuotient.congr (Units.mapEquiv (φ.isoMon v))).trans
        (TimesMuQuotient.congr (Units.mapEquiv ((φ.symm).isoMon v))) =
      MulEquiv.refl (TimesMuQuotient (F.Mon v)ˣ)
    rw [show (φ.symm).isoMon v = (φ.isoMon v).symm from rfl]
    rw [← Units.mapEquiv_symm (φ.isoMon v)]
    rw [TimesMuQuotient.congr_symm (Units.mapEquiv (φ.isoMon v))]
    exact MulEquiv.self_trans_symm _

theorem canonicalLift_symm_trans {F F' : FPrimeStrip.{umon, uv, upi} V}
    (φ : FPrimeStripEquiv F F') :
    NaturallyIsomorphic
      ((SourceFTimesMuPrimeStripEquivalence.canonicalLift φ.symm).trans
        (SourceFTimesMuPrimeStripEquivalence.canonicalLift φ))
      (SourceFTimesMuPrimeStripEquivalence.refl
        (SourceFTimesMuPrimeStrip.canonical F')) where
  toF_eq := FPrimeStripEquiv.symm_trans φ
  isoTimesMu_eq := fun v => by
    show (TimesMuQuotient.congr (Units.mapEquiv ((φ.symm).isoMon v))).trans
        (TimesMuQuotient.congr (Units.mapEquiv (φ.isoMon v))) =
      MulEquiv.refl (TimesMuQuotient (F'.Mon v)ˣ)
    rw [show (φ.symm).isoMon v = (φ.isoMon v).symm from rfl]
    rw [← Units.mapEquiv_symm (φ.isoMon v)]
    rw [TimesMuQuotient.congr_symm (Units.mapEquiv (φ.isoMon v))]
    exact MulEquiv.symm_trans_self _

/-- A general representative composed with its inverse is naturally
    isomorphic to the identity. -/
theorem trans_symm (φ : SourceFTimesMuPrimeStripEquivalence S T) :
    NaturallyIsomorphic (φ.trans φ.symm)
      (SourceFTimesMuPrimeStripEquivalence.refl S) where
  toF_eq := by
    cases φ
    simp [SourceFTimesMuPrimeStripEquivalence.trans,
      SourceFTimesMuPrimeStripEquivalence.symm,
      SourceFTimesMuPrimeStripEquivalence.refl,
      FPrimeStripEquiv.trans, FPrimeStripEquiv.symm, FPrimeStripEquiv.refl,
      MulEquiv.symm_trans_self, MulEquiv.self_trans_symm]
  isoTimesMu_eq := fun v => by
    show (φ.isoTimesMu v).trans ((φ.symm).isoTimesMu v) =
      MulEquiv.refl (S.timesMu v)
    rw [show (φ.symm).isoTimesMu v = (φ.isoTimesMu v).symm from rfl]
    exact MulEquiv.self_trans_symm _

/-- The inverse of a general representative composed with it is naturally
    isomorphic to the identity. -/
theorem symm_trans (φ : SourceFTimesMuPrimeStripEquivalence S T) :
    NaturallyIsomorphic (φ.symm.trans φ)
      (SourceFTimesMuPrimeStripEquivalence.refl T) where
  toF_eq := by
    cases φ
    simp [SourceFTimesMuPrimeStripEquivalence.trans,
      SourceFTimesMuPrimeStripEquivalence.symm,
      SourceFTimesMuPrimeStripEquivalence.refl,
      FPrimeStripEquiv.trans, FPrimeStripEquiv.symm, FPrimeStripEquiv.refl,
      MulEquiv.symm_trans_self, MulEquiv.self_trans_symm]
  isoTimesMu_eq := fun v => by
    show ((φ.symm).isoTimesMu v).trans (φ.isoTimesMu v) =
      MulEquiv.refl (T.timesMu v)
    rw [show (φ.symm).isoTimesMu v = (φ.isoTimesMu v).symm from rfl]
    exact MulEquiv.symm_trans_self _

end NaturallyIsomorphic

def naturallyIsomorphicSetoid (S T : SourceFTimesMuPrimeStrip V) :
    Setoid (SourceFTimesMuPrimeStripEquivalence S T) where
  r := NaturallyIsomorphic
  iseqv :=
    ⟨NaturallyIsomorphic.refl,
      fun h => h.symm,
      fun h₁ h₂ => h₁.trans h₂⟩

end SourceFTimesMuPrimeStripEquivalence

abbrev SourceFTimesMuPrimeStripFullPolyIsomorphism
    (S T : SourceFTimesMuPrimeStrip V) :=
  Quotient (SourceFTimesMuPrimeStripEquivalence.naturallyIsomorphicSetoid S T)

namespace SourceFTimesMuPrimeStripFullPolyIsomorphism

variable {S T U W : SourceFTimesMuPrimeStrip V}

def ofEquivalence (φ : SourceFTimesMuPrimeStripEquivalence S T) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism S T :=
  Quotient.mk _ φ

def id (S : SourceFTimesMuPrimeStrip V) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism S S :=
  ofEquivalence (SourceFTimesMuPrimeStripEquivalence.refl S)

def comp (first : SourceFTimesMuPrimeStripFullPolyIsomorphism S T)
    (second : SourceFTimesMuPrimeStripFullPolyIsomorphism T U) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism S U :=
  Quotient.map₂ SourceFTimesMuPrimeStripEquivalence.trans
    (fun _ _ hφ _ _ hψ =>
      SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.comp hφ hψ)
    first second

def symm (f : SourceFTimesMuPrimeStripFullPolyIsomorphism S T) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism T S :=
  Quotient.map SourceFTimesMuPrimeStripEquivalence.symm
    (fun _ _ h =>
      SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.congr_symm h) f

@[simp] theorem comp_ofEquivalence
    (φ : SourceFTimesMuPrimeStripEquivalence S T)
    (ψ : SourceFTimesMuPrimeStripEquivalence T U) :
    comp (ofEquivalence φ) (ofEquivalence ψ) = ofEquivalence (φ.trans ψ) :=
  rfl

@[simp] theorem id_comp (f : SourceFTimesMuPrimeStripFullPolyIsomorphism S T) :
    comp (id S) f = f := by
  refine Quotient.inductionOn f ?_
  intro φ
  apply Quotient.sound
  exact SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.id_comp φ

@[simp] theorem comp_id (f : SourceFTimesMuPrimeStripFullPolyIsomorphism S T) :
    comp f (id T) = f := by
  refine Quotient.inductionOn f ?_
  intro φ
  apply Quotient.sound
  exact SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.comp_id φ

theorem comp_assoc (f : SourceFTimesMuPrimeStripFullPolyIsomorphism S T)
    (g : SourceFTimesMuPrimeStripFullPolyIsomorphism T U)
    (h : SourceFTimesMuPrimeStripFullPolyIsomorphism U W) :
    comp (comp f g) h = comp f (comp g h) := by
  refine Quotient.inductionOn₃ f g h ?_
  intro φ ψ χ
  apply Quotient.sound
  exact SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.assoc φ ψ χ
/-- The right inverse law of the full poly-isomorphism groupoid. -/
theorem comp_symm (f : SourceFTimesMuPrimeStripFullPolyIsomorphism S T) :
    comp f (symm f) = id S := by
  refine Quotient.inductionOn f ?_
  intro φ
  apply Quotient.sound
  exact SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.trans_symm φ

/-- The left inverse law of the full poly-isomorphism groupoid. -/
theorem symm_comp (f : SourceFTimesMuPrimeStripFullPolyIsomorphism S T) :
    comp (symm f) f = id T := by
  refine Quotient.inductionOn f ?_
  intro φ
  apply Quotient.sound
  exact SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.symm_trans φ

theorem representative_exists
    (f : SourceFTimesMuPrimeStripFullPolyIsomorphism S T) :
    ∃ φ : SourceFTimesMuPrimeStripEquivalence S T, ofEquivalence φ = f := by
  obtain ⟨φ, rfl⟩ := Quotient.exists_rep f
  exact ⟨φ, rfl⟩

theorem nonempty_iff :
    Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism S T) ↔
      Nonempty (SourceFTimesMuPrimeStripEquivalence S T) := by
  constructor
  · rintro ⟨f⟩
    obtain ⟨φ, _⟩ := representative_exists f
    exact ⟨φ⟩
  · rintro ⟨φ⟩
    exact ⟨ofEquivalence φ⟩

theorem comp_inverse_assoc {B : SourceFTimesMuPrimeStrip V}
    (forward : SourceFTimesMuPrimeStripFullPolyIsomorphism S B)
    (reverse : SourceFTimesMuPrimeStripFullPolyIsomorphism B S)
    (inverse : comp forward reverse = id S)
    (next : SourceFTimesMuPrimeStripFullPolyIsomorphism S T) :
    comp forward (comp reverse next) = next := by
  rw [← comp_assoc, inverse, id_comp]

theorem canonical_trans {F F' F'' : FPrimeStrip.{umon, uv, upi} V}
    (φ : FPrimeStripEquiv F F') (ψ : FPrimeStripEquiv F' F'') :
    comp (ofEquivalence (SourceFTimesMuPrimeStripEquivalence.canonicalLift φ))
        (ofEquivalence (SourceFTimesMuPrimeStripEquivalence.canonicalLift ψ)) =
      ofEquivalence (SourceFTimesMuPrimeStripEquivalence.canonicalLift
        (FPrimeStripEquiv.trans φ ψ)) := by
  apply Quotient.sound
  exact SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.canonicalLift_trans φ ψ

theorem canonical_refl {F : FPrimeStrip.{umon, uv, upi} V} :
    ofEquivalence (SourceFTimesMuPrimeStripEquivalence.canonicalLift
        (FPrimeStripEquiv.refl F)) =
      id (SourceFTimesMuPrimeStrip.canonical F) := by
  apply Quotient.sound
  exact SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.canonicalLift_refl

theorem canonicalLift_inverse_left {F F' : FPrimeStrip.{umon, uv, upi} V}
    (φ : FPrimeStripEquiv F F') :
    comp (ofEquivalence (SourceFTimesMuPrimeStripEquivalence.canonicalLift φ))
        (ofEquivalence
          (SourceFTimesMuPrimeStripEquivalence.canonicalLift φ.symm)) =
      id (SourceFTimesMuPrimeStrip.canonical F) := by
  apply Quotient.sound
  exact SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.canonicalLift_trans_symm φ

theorem canonicalLift_inverse_right {F F' : FPrimeStrip.{umon, uv, upi} V}
    (φ : FPrimeStripEquiv F F') :
    comp (ofEquivalence
          (SourceFTimesMuPrimeStripEquivalence.canonicalLift φ.symm))
        (ofEquivalence (SourceFTimesMuPrimeStripEquivalence.canonicalLift φ)) =
      id (SourceFTimesMuPrimeStrip.canonical F') := by
  apply Quotient.sound
  exact SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.canonicalLift_symm_trans φ

end SourceFTimesMuPrimeStripFullPolyIsomorphism

local infixr:81 " ≫ₜ " =>
  SourceFTimesMuPrimeStripFullPolyIsomorphism.comp

/-- The commuting square of IUT III, Remark 3.11.1(iii): four corners and
    four full poly-isomorphisms, with the two-path equality and the
    two-sided existence of the opposite horizontal arrow. -/
structure SourceFTimesMuPrimeStripPolyIsomorphismSquare
    (upperLeft upperRight lowerLeft lowerRight : SourceFTimesMuPrimeStrip V) where
  upperHorizontal : SourceFTimesMuPrimeStripFullPolyIsomorphism upperLeft upperRight
  lowerHorizontal : SourceFTimesMuPrimeStripFullPolyIsomorphism lowerLeft lowerRight
  leftKummer : SourceFTimesMuPrimeStripFullPolyIsomorphism upperLeft lowerLeft
  rightKummer : SourceFTimesMuPrimeStripFullPolyIsomorphism upperRight lowerRight
  commutes : leftKummer ≫ₜ lowerHorizontal = upperHorizontal ≫ₜ rightKummer
  upperToLower :
    ∀ upper : SourceFTimesMuPrimeStripFullPolyIsomorphism upperLeft upperRight,
      ∃ lower : SourceFTimesMuPrimeStripFullPolyIsomorphism lowerLeft lowerRight,
        leftKummer ≫ₜ lower = upper ≫ₜ rightKummer
  lowerToUpper :
    ∀ lower : SourceFTimesMuPrimeStripFullPolyIsomorphism lowerLeft lowerRight,
      ∃ upper : SourceFTimesMuPrimeStripFullPolyIsomorphism upperLeft upperRight,
        leftKummer ≫ₜ lower = upper ≫ₜ rightKummer

namespace SourceFTimesMuPrimeStripPolyIsomorphismSquare

variable {upperLeft upperRight lowerLeft lowerRight : SourceFTimesMuPrimeStrip V}

/-- Assemble a square from an upper horizontal arrow and two mutually inverse
    Kummer pairs.  The lower horizontal arrow is forced by conjugation. -/
noncomputable def ofUpperHorizontal
    (upperHorizontal : SourceFTimesMuPrimeStripFullPolyIsomorphism upperLeft upperRight)
    (leftKummer : SourceFTimesMuPrimeStripFullPolyIsomorphism upperLeft lowerLeft)
    (leftKummerInverse : SourceFTimesMuPrimeStripFullPolyIsomorphism lowerLeft upperLeft)
    (leftToFrom : leftKummer ≫ₜ leftKummerInverse =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.id upperLeft)
    (rightKummer : SourceFTimesMuPrimeStripFullPolyIsomorphism upperRight lowerRight)
    (rightKummerInverse : SourceFTimesMuPrimeStripFullPolyIsomorphism lowerRight upperRight)
    (rightFromTo : rightKummerInverse ≫ₜ rightKummer =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.id lowerRight) :
    SourceFTimesMuPrimeStripPolyIsomorphismSquare
      upperLeft upperRight lowerLeft lowerRight where
  upperHorizontal := upperHorizontal
  lowerHorizontal := (leftKummerInverse ≫ₜ upperHorizontal) ≫ₜ rightKummer
  leftKummer := leftKummer
  rightKummer := rightKummer
  commutes := by
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
      leftKummerInverse upperHorizontal rightKummer]
    exact SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_inverse_assoc
      leftKummer leftKummerInverse leftToFrom (upperHorizontal ≫ₜ rightKummer)
  upperToLower upper := by
    refine ⟨(leftKummerInverse ≫ₜ upper) ≫ₜ rightKummer, ?_⟩
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
      leftKummerInverse upper rightKummer]
    exact SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_inverse_assoc
      leftKummer leftKummerInverse leftToFrom (upper ≫ₜ rightKummer)
  lowerToUpper lower := by
    refine ⟨(leftKummer ≫ₜ lower) ≫ₜ rightKummerInverse, ?_⟩
    symm
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
      (leftKummer ≫ₜ lower) rightKummerInverse rightKummer]
    rw [rightFromTo]
    exact SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_id _

end SourceFTimesMuPrimeStripPolyIsomorphismSquare

/-- The commutative diagram of IUT III, Remark 3.10.2 (`Inter-universal
    Teichmuller Theory III.txt` 9084-9133), at the times-mu prime-strip level
    of this file: the four `(n,m)`-level vertices `bottomEnv`, `bottomGau`,
    `bottomLGP`, `bottomLgp` (bottom row), the four `(n, o)`-level vertices
    `topEnv`, `topGau`, `topLGP`, `topLgp` (top row), the three lower and
    three upper horizontal arrows, the four vertical arrows, and the three
    commutativity laws, all as full poly-isomorphisms of
    F-turnstile-times-mu-prime-strips.

    Roles of the arrows (per the itemized list of the cited remark):
    * `lowerEnv` is the induced version of the evaluation isomorphism of
      [IUTchII], Corollary 4.10, (ii) (the "first lower horizontal arrow");
      `lowerGau` and `lowerLGP` are the induced versions of the tautological
      isomorphisms of Proposition 3.7, (iii), (iv);
    * `upperEnv` is the induced version of the etale-like evaluation
      isomorphism (the "first upper horizontal arrow"); `upperGau` and
      `upperLGP` are the induced versions of the natural isomorphisms of the
      second display of Proposition 3.10, (i);
    * `verticalEnv` is the induced version of the Kummer isomorphism of
      Proposition 2.1, (ii) (the "first vertical arrow"); `verticalGau`,
      `verticalLGP`, `verticalLgp` are the induced versions of the Kummer
      isomorphisms of the final display of Proposition 3.10, (i).

    Contract status: this is the conditional form of the (IPL) clause of
    Remark 3.11.1, (iii) (txt 9683-9698).  The existence of arrows with this
    provenance inside the construction algorithm of Theorem 3.11 is not
    constructed here: this file's dependency cone has no algorithm-indexed
    strip family and no source-level Kummer/evaluation strip arrows;
    consumers supply the diagram as data (report t2). -/
structure SourceFTimesMuPrimeStripRem3102Diagram
    (bottomEnv bottomGau bottomLGP bottomLgp topEnv topGau topLGP topLgp :
      SourceFTimesMuPrimeStrip V) where
  /-- first lower horizontal arrow (Cor. 4.10, (ii)) -/
  lowerEnv : SourceFTimesMuPrimeStripFullPolyIsomorphism bottomEnv bottomGau
  /-- second lower horizontal arrow (Prop. 3.7, (iii)) -/
  lowerGau : SourceFTimesMuPrimeStripFullPolyIsomorphism bottomGau bottomLGP
  /-- third lower horizontal arrow (Prop. 3.7, (iv)) -/
  lowerLGP : SourceFTimesMuPrimeStripFullPolyIsomorphism bottomLGP bottomLgp
  /-- first upper horizontal arrow (etale-like evaluation isomorphism) -/
  upperEnv : SourceFTimesMuPrimeStripFullPolyIsomorphism topEnv topGau
  /-- second upper horizontal arrow (Prop. 3.10, (i)) -/
  upperGau : SourceFTimesMuPrimeStripFullPolyIsomorphism topGau topLGP
  /-- third upper horizontal arrow (Prop. 3.10, (i)) -/
  upperLGP : SourceFTimesMuPrimeStripFullPolyIsomorphism topLGP topLgp
  /-- first vertical arrow (Kummer isomorphism, Prop. 2.1, (ii)) -/
  verticalEnv : SourceFTimesMuPrimeStripFullPolyIsomorphism bottomEnv topEnv
  /-- second vertical arrow (Kummer isomorphism, Prop. 3.10, (i)) -/
  verticalGau : SourceFTimesMuPrimeStripFullPolyIsomorphism bottomGau topGau
  /-- third vertical arrow (Kummer isomorphism, Prop. 3.10, (i)) -/
  verticalLGP : SourceFTimesMuPrimeStripFullPolyIsomorphism bottomLGP topLGP
  /-- fourth vertical arrow (Kummer isomorphism, Prop. 3.10, (i)) -/
  verticalLgp : SourceFTimesMuPrimeStripFullPolyIsomorphism bottomLgp topLgp
  /-- commutativity of the square in the `env` column -/
  commEnv : lowerEnv ≫ₜ verticalGau = verticalEnv ≫ₜ upperEnv
  /-- commutativity of the square in the `gau` column -/
  commGau : lowerGau ≫ₜ verticalLGP = verticalGau ≫ₜ upperGau
  /-- commutativity of the square in the `LGP` column -/
  commLGP : lowerLGP ≫ₜ verticalLgp = verticalLGP ≫ₜ upperLGP

namespace SourceFTimesMuPrimeStripRem3102Diagram

variable {bottomEnv bottomGau bottomLGP bottomLgp topEnv topGau topLGP topLgp :
  SourceFTimesMuPrimeStrip V}

/-- The IPL linking isomorphism of IUT III, Remark 3.11.1, (iii) (txt
    9701-9710), traversed from the intermediate `(n,m)`-level `LGP` strip to
    the `(n, o)`-level `lgp` strip: the inverses of the first two lower
    horizontal arrows of the Remark 3.10.2 diagram, followed by the first
    vertical arrow, followed by the three upper horizontal arrows. -/
def iplLink
    (D : SourceFTimesMuPrimeStripRem3102Diagram bottomEnv bottomGau bottomLGP
      bottomLgp topEnv topGau topLGP topLgp) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism bottomLGP topLgp :=
  D.lowerGau.symm ≫ₜ D.lowerEnv.symm ≫ₜ D.verticalEnv ≫ₜ D.upperEnv ≫ₜ
    D.upperGau ≫ₜ D.upperLGP

/-- The two-arrow cancellation in the `env` column: the inverse of the
    second lower horizontal arrow, then the first vertical and first upper
    horizontal arrows, compose to the second vertical arrow, by the
    commutativity of the `env` square. -/
theorem lowerEnv_symm_verticalEnv_upperEnv
    (D : SourceFTimesMuPrimeStripRem3102Diagram bottomEnv bottomGau bottomLGP
      bottomLgp topEnv topGau topLGP topLgp) :
    D.lowerEnv.symm ≫ₜ D.verticalEnv ≫ₜ D.upperEnv = D.verticalGau := by
  calc D.lowerEnv.symm ≫ₜ D.verticalEnv ≫ₜ D.upperEnv
      = D.lowerEnv.symm ≫ₜ (D.lowerEnv ≫ₜ D.verticalGau) := by
        rw [← D.commEnv]
    _ = (D.lowerEnv.symm ≫ₜ D.lowerEnv) ≫ₜ D.verticalGau :=
        (SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
          D.lowerEnv.symm D.lowerEnv D.verticalGau).symm
    _ = SourceFTimesMuPrimeStripFullPolyIsomorphism.id bottomGau ≫ₜ
          D.verticalGau := by
        rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.symm_comp D.lowerEnv]
    _ = D.verticalGau :=
        SourceFTimesMuPrimeStripFullPolyIsomorphism.id_comp D.verticalGau

/-- The two-arrow cancellation in the `gau` column, as in
    `lowerEnv_symm_verticalEnv_upperEnv`. -/
theorem lowerGau_symm_verticalGau_upperGau
    (D : SourceFTimesMuPrimeStripRem3102Diagram bottomEnv bottomGau bottomLGP
      bottomLgp topEnv topGau topLGP topLgp) :
    D.lowerGau.symm ≫ₜ D.verticalGau ≫ₜ D.upperGau = D.verticalLGP := by
  calc D.lowerGau.symm ≫ₜ D.verticalGau ≫ₜ D.upperGau
      = D.lowerGau.symm ≫ₜ (D.lowerGau ≫ₜ D.verticalLGP) := by
        rw [← D.commGau]
    _ = (D.lowerGau.symm ≫ₜ D.lowerGau) ≫ₜ D.verticalLGP :=
        (SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
          D.lowerGau.symm D.lowerGau D.verticalLGP).symm
    _ = SourceFTimesMuPrimeStripFullPolyIsomorphism.id bottomLGP ≫ₜ
          D.verticalLGP := by
        rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.symm_comp D.lowerGau]
    _ = D.verticalLGP :=
        SourceFTimesMuPrimeStripFullPolyIsomorphism.id_comp D.verticalLGP

/-- Collapse of the IPL composite in a commuting Remark 3.10.2 diagram: the
    six-factor composite equals the third vertical arrow followed by the
    third upper horizontal arrow. -/
theorem iplLink_eq_verticalLGP_upperLGP
    (D : SourceFTimesMuPrimeStripRem3102Diagram bottomEnv bottomGau bottomLGP
      bottomLgp topEnv topGau topLGP topLgp) :
    iplLink D = D.verticalLGP ≫ₜ D.upperLGP := by
  show D.lowerGau.symm ≫ₜ D.lowerEnv.symm ≫ₜ D.verticalEnv ≫ₜ D.upperEnv ≫ₜ
      D.upperGau ≫ₜ D.upperLGP = D.verticalLGP ≫ₜ D.upperLGP
  calc D.lowerGau.symm ≫ₜ D.lowerEnv.symm ≫ₜ D.verticalEnv ≫ₜ D.upperEnv ≫ₜ
        D.upperGau ≫ₜ D.upperLGP
      = D.lowerGau.symm ≫ₜ (D.lowerEnv.symm ≫ₜ ((D.verticalEnv ≫ₜ D.upperEnv) ≫ₜ
          (D.upperGau ≫ₜ D.upperLGP))) := by
        rw [← SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
          D.verticalEnv D.upperEnv (D.upperGau ≫ₜ D.upperLGP)]
    _ = D.lowerGau.symm ≫ₜ
          ((D.lowerEnv.symm ≫ₜ (D.verticalEnv ≫ₜ D.upperEnv)) ≫ₜ
          (D.upperGau ≫ₜ D.upperLGP)) := by
        rw [← SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
          D.lowerEnv.symm (D.verticalEnv ≫ₜ D.upperEnv)
          (D.upperGau ≫ₜ D.upperLGP)]
    _ = D.lowerGau.symm ≫ₜ (D.verticalGau ≫ₜ (D.upperGau ≫ₜ D.upperLGP)) := by
        rw [lowerEnv_symm_verticalEnv_upperEnv D]
    _ = D.lowerGau.symm ≫ₜ ((D.verticalGau ≫ₜ D.upperGau) ≫ₜ D.upperLGP) := by
        rw [← SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
          D.verticalGau D.upperGau D.upperLGP]
    _ = (D.lowerGau.symm ≫ₜ (D.verticalGau ≫ₜ D.upperGau)) ≫ₜ D.upperLGP := by
        rw [← SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
          D.lowerGau.symm (D.verticalGau ≫ₜ D.upperGau) D.upperLGP]
    _ = D.verticalLGP ≫ₜ D.upperLGP := by
        rw [lowerGau_symm_verticalGau_upperGau D]

/-- Intermediate-strip dual role at the `bottomGau` corner (IUT III, Remark
    3.11.1, (iii), txt 9688-9698): full poly-isomorphisms from the strip to
    the domain end (`bottomLGP`) and to the codomain end (`topLgp`) of the
    IPL composite both exist. -/
theorem bottomGau_dualRole
    (D : SourceFTimesMuPrimeStripRem3102Diagram bottomEnv bottomGau bottomLGP
      bottomLgp topEnv topGau topLGP topLgp) :
    Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism bottomGau bottomLGP) ∧
    Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism bottomGau topLgp) :=
  ⟨⟨D.lowerGau⟩,
    ⟨D.lowerEnv.symm ≫ₜ D.verticalEnv ≫ₜ D.upperEnv ≫ₜ D.upperGau ≫ₜ
      D.upperLGP⟩⟩

/-- Intermediate-strip dual role at the `bottomEnv` corner. -/
theorem bottomEnv_dualRole
    (D : SourceFTimesMuPrimeStripRem3102Diagram bottomEnv bottomGau bottomLGP
      bottomLgp topEnv topGau topLGP topLgp) :
    Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism bottomEnv bottomLGP) ∧
    Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism bottomEnv topLgp) :=
  ⟨⟨D.lowerEnv ≫ₜ D.lowerGau⟩,
    ⟨D.verticalEnv ≫ₜ D.upperEnv ≫ₜ D.upperGau ≫ₜ D.upperLGP⟩⟩

/-- Intermediate-strip dual role at the `topEnv` corner. -/
theorem topEnv_dualRole
    (D : SourceFTimesMuPrimeStripRem3102Diagram bottomEnv bottomGau bottomLGP
      bottomLgp topEnv topGau topLGP topLgp) :
    Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism topEnv bottomLGP) ∧
    Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism topEnv topLgp) :=
  ⟨⟨D.verticalEnv.symm ≫ₜ D.lowerEnv ≫ₜ D.lowerGau⟩,
    ⟨D.upperEnv ≫ₜ D.upperGau ≫ₜ D.upperLGP⟩⟩

/-- Intermediate-strip dual role at the `topGau` corner. -/
theorem topGau_dualRole
    (D : SourceFTimesMuPrimeStripRem3102Diagram bottomEnv bottomGau bottomLGP
      bottomLgp topEnv topGau topLGP topLgp) :
    Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism topGau bottomLGP) ∧
    Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism topGau topLgp) :=
  ⟨⟨D.verticalGau.symm ≫ₜ D.lowerGau⟩,
    ⟨D.upperGau ≫ₜ D.upperLGP⟩⟩

/-- Intermediate-strip dual role at the `topLGP` corner. -/
theorem topLGP_dualRole
    (D : SourceFTimesMuPrimeStripRem3102Diagram bottomEnv bottomGau bottomLGP
      bottomLgp topEnv topGau topLGP topLgp) :
    Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism topLGP bottomLGP) ∧
    Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism topLGP topLgp) :=
  ⟨⟨D.verticalLGP.symm⟩, ⟨D.upperLGP⟩⟩

end SourceFTimesMuPrimeStripRem3102Diagram

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive}

/-- The square of adjacent procession stages: its upper row is the stage-n
    link, its lower row is the stage-(n+1) link, and its vertical arrows are
    the components of the inclusion.  Commutation is the inclusion
    naturality, and the two-sided horizontal existence uses the inverse
    components. -/
noncomputable def processionInclusionSquare
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (P : H2FProcession I)
    (n : Nat) (i j : Fin (n + 1)) :
    SourceFTimesMuPrimeStripPolyIsomorphismSquare
      (SourceFTimesMuPrimeStrip.canonical ((P.stage n).strip i))
      (SourceFTimesMuPrimeStrip.canonical ((P.stage n).strip j))
      (SourceFTimesMuPrimeStrip.canonical
        ((P.stage (n + 1)).strip ((P.inclusion (Nat.le_succ n)).map i)))
      (SourceFTimesMuPrimeStrip.canonical
        ((P.stage (n + 1)).strip ((P.inclusion (Nat.le_succ n)).map j))) :=
  let E := P.inclusion (Nat.le_succ n)
  let upperHorizontal := SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift ((P.stage n).link i j))
  let lowerHorizontal := SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift
      ((P.stage (n + 1)).link (E.map i) (E.map j)))
  let leftKummer := SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift (E.component i))
  let rightKummer := SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift (E.component j))
  let leftKummerInverse := SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift (E.component i).symm)
  let rightKummerInverse := SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift (E.component j).symm)
  { upperHorizontal := upperHorizontal
    lowerHorizontal := lowerHorizontal
    leftKummer := leftKummer
    rightKummer := rightKummer
    commutes := (Quotient.sound
      (SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.congr_trans
        (E.naturality i j)).symm :
      SourceFTimesMuPrimeStripFullPolyIsomorphism.comp leftKummer lowerHorizontal =
        SourceFTimesMuPrimeStripFullPolyIsomorphism.comp upperHorizontal rightKummer)
    upperToLower := fun upper => ⟨(leftKummerInverse ≫ₜ upper) ≫ₜ rightKummer, by
      rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
        leftKummerInverse upper rightKummer]
      exact SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_inverse_assoc
        leftKummer leftKummerInverse
        (SourceFTimesMuPrimeStripFullPolyIsomorphism.canonicalLift_inverse_left
          (E.component i))
        (upper ≫ₜ rightKummer)⟩
    lowerToUpper := fun lower => ⟨(leftKummer ≫ₜ lower) ≫ₜ rightKummerInverse, by
      symm
      rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
        (leftKummer ≫ₜ lower) rightKummerInverse rightKummer]
      rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.canonicalLift_inverse_right
        (E.component j)]
      exact SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_id _⟩ }

/-- The square of the original log-Theta lattice at the vertices
    (n,m), (n+1,m), (n,m+1), (n+1,m+1): all four arrows are the source
    links, and commutation is the prime-strip square of the lattice. -/
noncomputable def logThetaLatticeSquare
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    SourceFTimesMuPrimeStripPolyIsomorphismSquare
      (SourceFTimesMuPrimeStrip.canonical (I.fPrimeStripAt n m))
      (SourceFTimesMuPrimeStrip.canonical (I.fPrimeStripAt (n + 1) m))
      (SourceFTimesMuPrimeStrip.canonical (I.fPrimeStripAt n (m + 1)))
      (SourceFTimesMuPrimeStrip.canonical (I.fPrimeStripAt (n + 1) (m + 1))) :=
  let upperHorizontal := SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift (I.fLinkAt n m (n + 1) m))
  let lowerHorizontal := SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift
      (I.fLinkAt n (m + 1) (n + 1) (m + 1)))
  let leftKummer := SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift (I.fLinkAt n m n (m + 1)))
  let rightKummer := SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift
      (I.fLinkAt (n + 1) m (n + 1) (m + 1)))
  let leftKummerInverse := SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift
      ((I.fLinkAt n m n (m + 1)).symm))
  let rightKummerInverse := SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift
      ((I.fLinkAt (n + 1) m (n + 1) (m + 1)).symm))
  have hsquare : FPrimeStripEquiv.trans (I.fLinkAt n m (n + 1) m)
      (I.fLinkAt (n + 1) m (n + 1) (m + 1)) =
      FPrimeStripEquiv.trans (I.fLinkAt n m n (m + 1))
        (I.fLinkAt n (m + 1) (n + 1) (m + 1)) := by
    rw [I.fLinkAt_trans n m (n + 1) m (n + 1) (m + 1),
      I.fLinkAt_trans n m n (m + 1) (n + 1) (m + 1)]
  { upperHorizontal := upperHorizontal
    lowerHorizontal := lowerHorizontal
    leftKummer := leftKummer
    rightKummer := rightKummer
    commutes := (Quotient.sound
      (SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.congr_trans
        hsquare).symm :
      SourceFTimesMuPrimeStripFullPolyIsomorphism.comp leftKummer lowerHorizontal =
        SourceFTimesMuPrimeStripFullPolyIsomorphism.comp upperHorizontal rightKummer)
    upperToLower := fun upper => ⟨(leftKummerInverse ≫ₜ upper) ≫ₜ rightKummer, by
      rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
        leftKummerInverse upper rightKummer]
      exact SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_inverse_assoc
        leftKummer leftKummerInverse
        (SourceFTimesMuPrimeStripFullPolyIsomorphism.canonicalLift_inverse_left
          (I.fLinkAt n m n (m + 1)))
        (upper ≫ₜ rightKummer)⟩
    lowerToUpper := fun lower => ⟨(leftKummer ≫ₜ lower) ≫ₜ rightKummerInverse, by
      symm
      rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc
        (leftKummer ≫ₜ lower) rightKummerInverse rightKummer]
      rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.canonicalLift_inverse_right
        (I.fLinkAt (n + 1) m (n + 1) (m + 1))]
      exact SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_id _⟩ }

end OriginalInput

end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceFTimesMuPrimeStripPolyIsomorphism : Obligation :=
  { id := "IUT-III.source-ftimes-mu-prime-strip-poly-isomorphism"
    source := "IUT III, Theorem 3.11(i); Remark 3.11.1(iii); Corollary 3.12, Step (xi-b)"
    status := VerificationStatus.provedKernel
    note :=
      "The times-mu prime-strip carrier over an F-prime-strip, its canonical " ++
        "instance from the torsion quotient of the unit groups, the full " ++
        "poly-isomorphism classes with their category laws and canonical " ++
        "lifting, the poly-isomorphism square with its upper-horizontal " ++
        "assembly, and the two anchored squares from the procession and the " ++
        "log-Theta lattice are proved, and the conditional contract of the " ++
        "algorithm-induced output links of the cited remark is formalized " ++
        "as SourceFTimesMuPrimeStripRem3102Diagram (the Remark 3.10.2 " ++
        "diagram structure, the IPL composite, and the intermediate dual " ++
        "roles).  The algorithmic provenance of those links and the named " ++
        "bridge to the source-level link factorization remain a named gap."
    dependsOn :=
      [ "IUT-I-II.prime-strips-frobenioids",
        "IUT-II.times-mu-torsion-quotient" ] }

end LeanFormal.IUT.Audit
