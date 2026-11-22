/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S1965FDoublePlusStripActual
import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitMultiplicativeCurve
import LeanFormal.IUT.Foundations.Geometry.WeierstrassVariableChangePoints

/-!
# S2037: the geometric part of the actual F-double-plus-prime-strip

Layer: O (original Theta-link / q-pilot), on the actual S1895 input and the
actual local O^× carrier of S1978.

## The paper object

For the initial Theta-data of IUT I, Definition 3.1, the local geometric part
of the F-double-plus-prime-strip at a place v is the tempered fundamental group
Pi_v of the once-punctured Tate curve X_v (bad v), respectively the etale
fundamental group of X_v^-> (good v), together with the arithmetic projection

  Pi_v --> G_v = Gal(K_v^bar/K_v)

and the action of Pi_v on the local value monoid through this projection.  The
geometric kernel is the fundamental group of the once-punctured elliptic curve
over K_v^bar; it is nontrivial and nonabelian (free profinite of rank two in
the etale case), and it is emphatically *not* the trivial kernel of the
arithmetic number-field F-prime-strip.

## What this file does

1.  It records the exact missing local datum as a structure CurvePi1Family:
    an actual once-punctured elliptic curve at every place, the total
    tempered/etale group Pi_v, the projection to the actual local total group
    Pi of the base strip (whose projection to G_v is the actual local Galois
    projection), and the nontrivial, nonabelian geometric kernel.  No
    inhabitant is constructed.

2.  It constructs the operation FPrimeStrip.replacePi, which replaces the
    total group of an existing actual F-prime-strip by the curve group while
    keeping the actual local value monoid, the actual local action (composed
    with the projection to the old total group), and the actual degree.  The
    resulting projection to G is the composite of the old projection and the
    curve projection; its action is proved to factor through the projection,
    and its degree is proved invariant under the action.

3.  It attaches the curve component to the actual F-double-plus-carrier
    FDoublePlusPrimeStrip of S1965:

    * paperCurveFDoublePlus D C is the carrier over the actual
      NumberFieldPlace (PaperFmod D) with global realified Frobenioid
      C-mod, actual local divisor monoids and rho_v, and with fDagger replaced
      by the curve F-prime-strip;
    * paperCurveOneColumnFDoublePlus D e C is the same attachment over the
      one-column index PaperV = FinitePrimePlace 2 7, using S1978's actual
      local O^× carrier and its actual local Galois action.

    In both cases the geometric kernel at v is *proved* to be exactly the
    kernel of the composite arithmetic projection, hence nontrivial and
    nonabelian.

4.  It proves the non-fakeability results:

    * the actual number-field F-double-plus-carrier paperModFDoublePlus D has
      trivial geometric kernel at every place, so it cannot be the paper
      object;
    * the reduced Z/2 anabelioid strip has abelian geometric kernel, so it
      cannot be equivalent to the actual curve kernel;
    * any carrier whose geometric kernel is abelian (respectively trivial)
      cannot satisfy the curve component.

## The exact first missing

The first missing object is S2037FirstMissing D, the family of actual local
curve fundamental groups with their arithmetic projections and nontrivial
nonabelian geometric kernels.  The tree contains the actual once-punctured
curve schemes, the actual finite etale cover categories and the actual free
profinite group on two generators, but it does not contain the fundamental
group of a curve, nor the identification of the free profinite group with the
geometric fundamental group of the once-punctured curve (see
Example36FreeProfinitePi.PuncturedCurveGeometricPiCard, which is a frozen
card with no inhabitant).  This file therefore records the missing datum and
proves the attachment and the obstruction; it does not fabricate a curve
group.

No sorry, axiom, True/PUnit slot, empty type, arbitrary inhabitant or
assumption-only Nonempty gate is used to close a result.  The missing object
is recorded as a structure with no inhabitant.  The only classical inputs are
the ones already used by S1965/S1978 (propext, Classical.choice, Quot.sound).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open LeanFormal.IUT

/-! ## 2. Replacing the total group of an F-prime-strip -/

namespace LeanFormal.IUT.FPrimeStrip

/-- Replace the total group Pi of an F-prime-strip by a new group family Pi',
keeping the actual local value monoids and degree, composing the actual local
action with the new projection to the old total group, and projecting to G by
the composite of the old projection and the new projection. -/
noncomputable def replacePi {V : Type*} (S : FPrimeStrip V) (Pi' : V → Type*)
    [groupPi' : ∀ v, Group (Pi' v)]
    (proj' : ∀ v, Pi' v →* S.Pi v)
    (surj' : ∀ v, Function.Surjective ((S.proj v).comp (proj' v))) :
    FPrimeStrip V where
  Pi := Pi'
  groupPi := groupPi'
  G := S.G
  groupG := S.groupG
  proj := fun v => (S.proj v).comp (proj' v)
  proj_surjective := surj'
  Mon := S.Mon
  commMonoidMon := S.commMonoidMon
  action := fun v => (S.action v).comp (proj' v)
  degree := S.degree

variable {V : Type*} {S : FPrimeStrip V}

@[simp] theorem replacePi_Pi (S : FPrimeStrip V) (Pi' : V → Type*)
    [groupPi' : ∀ v, Group (Pi' v)]
    (proj' : ∀ v, Pi' v →* S.Pi v)
    (surj' : ∀ v, Function.Surjective ((S.proj v).comp (proj' v))) :
    (S.replacePi Pi' proj' surj').Pi = Pi' := rfl

@[simp] theorem replacePi_Mon (S : FPrimeStrip V) (Pi' : V → Type*)
    [groupPi' : ∀ v, Group (Pi' v)]
    (proj' : ∀ v, Pi' v →* S.Pi v)
    (surj' : ∀ v, Function.Surjective ((S.proj v).comp (proj' v))) :
    (S.replacePi Pi' proj' surj').Mon = S.Mon := rfl

@[simp] theorem replacePi_degree (S : FPrimeStrip V) (Pi' : V → Type*)
    [groupPi' : ∀ v, Group (Pi' v)]
    (proj' : ∀ v, Pi' v →* S.Pi v)
    (surj' : ∀ v, Function.Surjective ((S.proj v).comp (proj' v))) :
    (S.replacePi Pi' proj' surj').degree = S.degree := rfl

theorem replacePi_action_apply (S : FPrimeStrip V) (Pi' : V → Type*)
    [groupPi' : ∀ v, Group (Pi' v)]
    (proj' : ∀ v, Pi' v →* S.Pi v)
    (surj' : ∀ v, Function.Surjective ((S.proj v).comp (proj' v)))
    (v : V) (g : Pi' v) (m : S.Mon v) :
    (S.replacePi Pi' proj' surj').action v g m = S.action v (proj' v g) m := rfl

theorem replacePi_proj_apply (S : FPrimeStrip V) (Pi' : V → Type*)
    [groupPi' : ∀ v, Group (Pi' v)]
    (proj' : ∀ v, Pi' v →* S.Pi v)
    (surj' : ∀ v, Function.Surjective ((S.proj v).comp (proj' v)))
    (v : V) (g : Pi' v) :
    (S.replacePi Pi' proj' surj').proj v g = S.proj v (proj' v g) := rfl

theorem replacePi_geometric (S : FPrimeStrip V) (Pi' : V → Type*)
    [groupPi' : ∀ v, Group (Pi' v)]
    (proj' : ∀ v, Pi' v →* S.Pi v)
    (surj' : ∀ v, Function.Surjective ((S.proj v).comp (proj' v))) (v : V) :
    (S.replacePi Pi' proj' surj').geometric v =
      ((S.proj v).comp (proj' v)).ker := rfl

theorem replacePi_geometric_nontrivial (S : FPrimeStrip V) (Pi' : V → Type*)
    [groupPi' : ∀ v, Group (Pi' v)]
    (proj' : ∀ v, Pi' v →* S.Pi v)
    (surj' : ∀ v, Function.Surjective ((S.proj v).comp (proj' v)))
    (h : ∀ v, ∃ x : ((S.proj v).comp (proj' v)).ker, x ≠ 1) :
    ∀ v, (S.replacePi Pi' proj' surj').geometric v ≠ ⊥ := by
  intro v
  rw [replacePi_geometric]
  obtain ⟨x, hx⟩ := h v
  intro hbot
  apply hx
  apply Subtype.ext
  exact Subgroup.mem_bot.mp (hbot ▸ x.2)

theorem replacePi_geometric_nonabelian (S : FPrimeStrip V) (Pi' : V → Type*)
    [groupPi' : ∀ v, Group (Pi' v)]
    (proj' : ∀ v, Pi' v →* S.Pi v)
    (surj' : ∀ v, Function.Surjective ((S.proj v).comp (proj' v)))
    (h : ∀ v, ∃ x y : ((S.proj v).comp (proj' v)).ker, x * y ≠ y * x) :
    ∀ v, ∃ x y : (S.replacePi Pi' proj' surj').geometric v, x * y ≠ y * x := by
  intro v
  obtain ⟨x, y, hxy⟩ := h v
  refine ⟨⟨x.1, ?_⟩, ⟨y.1, ?_⟩, ?_⟩
  · rw [replacePi_geometric]; exact x.2
  · rw [replacePi_geometric]; exact y.2
  · intro hcontra
    apply hxy
    apply Subtype.ext
    exact congrArg Subtype.val hcontra

theorem replacePi_degree_action (S : FPrimeStrip V) (Pi' : V → Type*)
    [groupPi' : ∀ v, Group (Pi' v)]
    (proj' : ∀ v, Pi' v →* S.Pi v)
    (surj' : ∀ v, Function.Surjective ((S.proj v).comp (proj' v)))
    (hdeg : ∀ v (g : S.Pi v) (m : S.Mon v),
      S.degree v (S.action v g m) = S.degree v m)
    (v : V) (g : Pi' v) (m : S.Mon v) :
    (S.replacePi Pi' proj' surj').degree v
        ((S.replacePi Pi' proj' surj').action v g m) =
      (S.replacePi Pi' proj' surj').degree v m := by
  change S.degree v (S.action v (proj' v g) m) = S.degree v m
  exact hdeg v (proj' v g) m

end LeanFormal.IUT.FPrimeStrip

namespace LeanFormal.IUT.XiFPaper.S2037FDoublePlusPi1Actual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual.Realified
open LeanFormal.IUT.XiFPaper.S1965FDoublePlusStripActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open IsDedekindDomain NumberField
open WeierstrassCurve

universe u v



/-! ## 0. The actual local field at a place of Fmod -/

/-- The actual local field at a place of the S1895 Fmod: the completion at a
finite place, respectively the archimedean completion at an infinite place. -/
noncomputable abbrev PaperLocalField (D : S1895PaperInput)
    (v : NumberFieldPlace (PaperFmod D)) : Type :=
  match v with
  | .finite p => p.maximalIdeal.adicCompletion (PaperFmod D)
  | .infinite w => w.Completion

/-- The actual local field is a field at every place. -/
instance paperLocalFieldField (D : S1895PaperInput) :
    ∀ v : NumberFieldPlace (PaperFmod D), Field (PaperLocalField D v)
  | .finite p => inferInstance
  | .infinite w => inferInstance

/-! ## 1. The exact missing local curve pi-1 component -/

/-- The geometric part of a local F-double-plus-prime-strip at a place: an
actual once-punctured elliptic curve over the local field K, the total
tempered/etale fundamental group Pi, the arithmetic projection to the actual
local total group Pi of the base strip, and the geometric kernel (the kernel
of the composite projection to G).

The field kernel_nonabelian is the mathematical property of the geometric
fundamental group of a once-punctured elliptic curve over an algebraically
closed field (free profinite of rank two in the etale case).  It is recorded
here as part of the actual datum, not derived from a reduced model. -/
structure CurvePi1Family (V : Type*) (K : V → Type*) [fieldK : ∀ v, Field (K v)]
    (S : FPrimeStrip V) where
  /-- the actual once-punctured local curve at each place -/
  curve : ∀ v, PuncturedEllipticCurve (K v)
  /-- the total tempered/etale fundamental group -/
  total : V → Type
  [groupTotal : ∀ v, Group (total v)]
  /-- the arithmetic projection to the actual local total group of the base
  strip (the old total group, which already projects to G) -/
  proj : ∀ v, total v →* S.Pi v
  /-- the composite projection to the actual local Galois group is surjective -/
  proj_surjective : ∀ v, Function.Surjective ((S.proj v).comp (proj v))
  /-- the geometric kernel is nontrivial -/
  kernel_nontrivial : ∀ v,
    ∃ x : ((S.proj v).comp (proj v)).ker, x ≠ 1
  /-- the geometric kernel is nonabelian: this rules out the reduced Z/2
  model and every abelian-kernel substitute -/
  kernel_nonabelian : ∀ v,
    ∃ x y : ((S.proj v).comp (proj v)).ker, x * y ≠ y * x

attribute [instance] CurvePi1Family.groupTotal

namespace CurvePi1Family

variable {V : Type*} {K : V → Type*} [fieldK : ∀ v, Field (K v)]
variable {S : FPrimeStrip V} (C : CurvePi1Family V K S)

/-! ## 2. The curve F-prime-strip -/

/-- The curve F-prime-strip obtained by replacing the total group of S by the
curve group family C, keeping the actual local value monoid and degree. -/
noncomputable def toFPrimeStrip (C : CurvePi1Family V K S) : FPrimeStrip V :=
  S.replacePi C.total C.proj C.proj_surjective

@[simp] theorem toFPrimeStrip_Pi (C : CurvePi1Family V K S) :
    C.toFPrimeStrip.Pi = C.total := rfl

@[simp] theorem toFPrimeStrip_Mon (C : CurvePi1Family V K S) :
    C.toFPrimeStrip.Mon = S.Mon := rfl

@[simp] theorem toFPrimeStrip_degree (C : CurvePi1Family V K S) :
    C.toFPrimeStrip.degree = S.degree := rfl

theorem toFPrimeStrip_proj_apply (C : CurvePi1Family V K S) (v : V)
    (g : C.total v) :
    C.toFPrimeStrip.proj v g = S.proj v (C.proj v g) := rfl

theorem toFPrimeStrip_geometric (C : CurvePi1Family V K S) (v : V) :
    C.toFPrimeStrip.geometric v = ((S.proj v).comp (C.proj v)).ker := rfl

theorem toFPrimeStrip_geometric_nontrivial (C : CurvePi1Family V K S) (v : V) :
    C.toFPrimeStrip.geometric v ≠ ⊥ :=
  FPrimeStrip.replacePi_geometric_nontrivial S C.total C.proj
    C.proj_surjective C.kernel_nontrivial v

theorem toFPrimeStrip_geometric_nonabelian (C : CurvePi1Family V K S) (v : V) :
    ∃ x y : C.toFPrimeStrip.geometric v, x * y ≠ y * x :=
  FPrimeStrip.replacePi_geometric_nonabelian S C.total C.proj
    C.proj_surjective C.kernel_nonabelian v

theorem toFPrimeStrip_action_apply (C : CurvePi1Family V K S) (v : V)
    (g : C.total v) (m : S.Mon v) :
    C.toFPrimeStrip.action v g m = S.action v (C.proj v g) m := rfl

theorem toFPrimeStrip_degree_action (C : CurvePi1Family V K S)
    (hdeg : ∀ v (g : S.Pi v) (m : S.Mon v),
      S.degree v (S.action v g m) = S.degree v m)
    (v : V) (g : C.total v) (m : S.Mon v) :
    C.toFPrimeStrip.degree v (C.toFPrimeStrip.action v g m) =
      C.toFPrimeStrip.degree v m :=
  FPrimeStrip.replacePi_degree_action S C.total C.proj C.proj_surjective
    hdeg v g m

end CurvePi1Family

/-! ## 3. The actual local curve over the one-column places -/

/-- The concrete split multiplicative curve y^2 + xy = x^3 + 5 as a
once-punctured elliptic curve, with the puncture at the origin. -/
noncomputable def concreteSplitPuncturedCurve (K : Type*) [Field K] [Algebra ℚ K] :
    PuncturedEllipticCurve K where
  curve := concreteSplitCurve.baseChange K
  isElliptic := inferInstance
  puncture := (WeierstrassCurve.Affine.Point.zero :
    (concreteSplitCurve.baseChange K).toAffine.Point).toProjective

/-- The actual local curve at a one-column place v: the base change of the
concrete split multiplicative source curve to Q_[v.1]. -/
noncomputable def paperVCurve (v : PaperV) : PuncturedEllipticCurve ℚ_[v.1] := by
  letI : Fact (Nat.Prime v.1) := ⟨v.prime⟩
  exact concreteSplitPuncturedCurve ℚ_[v.1]

instance paperVField : ∀ v : PaperV, Field ℚ_[v.1]
  | v => by
      letI : Fact (Nat.Prime v.1) := ⟨v.prime⟩
      exact inferInstance

/-- The actual local O^× F-prime-strip of S1978 carries the actual local
value monoid, the actual local Galois action, and the actual norm-log degree.
The missing curve family below is relative to this actual strip. -/
abbrev ActualPaperVCurvePi1 : Type :=
  CurvePi1Family PaperV (fun v : PaperV => ℚ_[v.1]) localOFieldStrip

/-- The norm-log degree of a local O^× unit is trivial: every integral unit
has norm one. -/
theorem unitNormLogDegree_eq_ofAdd_norm (K : Type*) [NormedField K] (u : Kˣ) :
    unitNormLogDegree K u = Multiplicative.ofAdd (Real.log ‖(u : K)‖) := rfl

/-- The actual norm-log degree of the local O^× carrier is trivial. -/
theorem localOFieldUnitsDegree_apply_eq_one (p : Nat) [Fact (Nat.Prime p)]
    (u : LocalOFieldUnits p) : localOFieldUnitsDegree p u = 1 := by
  have hsub : ((Units.map
      (LocalFieldIntegralUnits.Integers (AlgebraicClosure ℚ_[p])).subtype.toMonoidHom u :
      (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]) =
      ((u : (LocalFieldIntegralUnits.Integers (AlgebraicClosure ℚ_[p]))) :
        AlgebraicClosure ℚ_[p]) := rfl
  rw [localOFieldUnitsDegree, MonoidHom.comp_apply, localUnitNormDegreeFor,
    unitNormLogDegree_eq_ofAdd_norm, hsub,
    LocalFieldIntegralUnits.norm_unit_eq_one u, Real.log_one]
  rfl

/-- The degree of the actual local O^× strip is trivial. -/
theorem localOFieldStrip_degree_apply_eq_one (v : PaperV)
    (x : localOFieldStrip.Mon v) : localOFieldStrip.degree v x = 1 :=
  localOFieldUnitsDegree_apply_eq_one v.1 x

/-- The actual local action preserves the (trivial) degree. -/
theorem localOFieldStrip_degree_action (v : PaperV)
    (g : localOFieldStrip.Pi v) (x : localOFieldStrip.Mon v) :
    localOFieldStrip.degree v (localOFieldStrip.action v g x) =
      localOFieldStrip.degree v x := by
  rw [localOFieldStrip_degree_apply_eq_one, localOFieldStrip_degree_apply_eq_one]

/-! ## 4. Attachment to the actual F-double-plus-carrier of S1965 -/

/-- The actual F-double-plus-carrier with the curve geometric part, over the
actual NumberFieldPlace (PaperFmod D) index.  The global realified Frobenioid,
the local divisor monoids and rho_v are exactly S1965's actual C-mod data;
only fDagger is replaced by the curve F-prime-strip. -/
noncomputable def paperCurveFDoublePlus (D : S1895PaperInput)
    (C : CurvePi1Family (NumberFieldPlace (PaperFmod D))
      (fun v => PaperLocalField D v)
      (numberFieldPrimeStripOnPlaces (F := PaperFmod D))) :
    FDoublePlusPrimeStrip (NumberFieldPlace (PaperFmod D)) :=
  { paperModFDoublePlus D with fDagger := C.toFPrimeStrip }

/-- The global realified Frobenioid of the curve carrier is the actual
C-mod of S1965. -/
@[simp] theorem paperCurveFDoublePlus_global (D : S1895PaperInput)
    (C : CurvePi1Family (NumberFieldPlace (PaperFmod D))
      (fun v => PaperLocalField D v)
      (numberFieldPrimeStripOnPlaces (F := PaperFmod D))) :
    (paperCurveFDoublePlus D C).global = paperGlobalRealifiedFrobenioid D := rfl

/-- Its F-dagger part is the curve F-prime-strip. -/
@[simp] theorem paperCurveFDoublePlus_fDagger (D : S1895PaperInput)
    (C : CurvePi1Family (NumberFieldPlace (PaperFmod D))
      (fun v => PaperLocalField D v)
      (numberFieldPrimeStripOnPlaces (F := PaperFmod D))) :
    (paperCurveFDoublePlus D C).fDagger = C.toFPrimeStrip := rfl

/-- Its local divisor monoid is still the actual place component. -/
@[simp] theorem paperCurveFDoublePlus_localDivisor (D : S1895PaperInput)
    (C : CurvePi1Family (NumberFieldPlace (PaperFmod D))
      (fun v => PaperLocalField D v)
      (numberFieldPrimeStripOnPlaces (F := PaperFmod D)))
    (v : NumberFieldPlace (PaperFmod D)) :
    (paperCurveFDoublePlus D C).localDivisor v =
      placeComponent (F := PaperFmod D) v := rfl

/-- The rho_v normalization of the curve carrier is still the actual
S1965 normalization. -/
theorem paperCurveFDoublePlus_rho_prime (D : S1895PaperInput)
    (C : CurvePi1Family (NumberFieldPlace (PaperFmod D))
      (fun v => PaperLocalField D v)
      (numberFieldPrimeStripOnPlaces (F := PaperFmod D)))
    (v : NumberFieldPlace (PaperFmod D)) :
    (paperCurveFDoublePlus D C).rho v
        (Multiplicative.ofAdd (placeComponentPrime (F := PaperFmod D) v)) =
      Multiplicative.ofAdd (1 : NNReal) :=
  paperModFDoublePlus_rho_prime D v

/-- The geometric kernel of the curve carrier is the kernel of the composite
arithmetic projection. -/
theorem paperCurveFDoublePlus_geometric (D : S1895PaperInput)
    (C : CurvePi1Family (NumberFieldPlace (PaperFmod D))
      (fun v => PaperLocalField D v)
      (numberFieldPrimeStripOnPlaces (F := PaperFmod D)))
    (v : NumberFieldPlace (PaperFmod D)) :
    (paperCurveFDoublePlus D C).fDagger.geometric v =
      (((numberFieldPrimeStripOnPlaces (F := PaperFmod D)).proj v).comp
        (C.proj v)).ker :=
  C.toFPrimeStrip_geometric v

/-- The curve carrier has nontrivial geometric kernel at every place. -/
theorem paperCurveFDoublePlus_geometric_nontrivial (D : S1895PaperInput)
    (C : CurvePi1Family (NumberFieldPlace (PaperFmod D))
      (fun v => PaperLocalField D v)
      (numberFieldPrimeStripOnPlaces (F := PaperFmod D)))
    (v : NumberFieldPlace (PaperFmod D)) :
    (paperCurveFDoublePlus D C).fDagger.geometric v ≠ ⊥ :=
  C.toFPrimeStrip_geometric_nontrivial v

/-- The curve carrier has nonabelian geometric kernel at every place. -/
theorem paperCurveFDoublePlus_geometric_nonabelian (D : S1895PaperInput)
    (C : CurvePi1Family (NumberFieldPlace (PaperFmod D))
      (fun v => PaperLocalField D v)
      (numberFieldPrimeStripOnPlaces (F := PaperFmod D)))
    (v : NumberFieldPlace (PaperFmod D)) :
    ∃ x y : (paperCurveFDoublePlus D C).fDagger.geometric v, x * y ≠ y * x :=
  C.toFPrimeStrip_geometric_nonabelian v

/-- The curve action factors through the actual local action on the actual
local value monoid. -/
theorem paperCurveFDoublePlus_action_apply
    (D : S1895PaperInput)
    (C : CurvePi1Family (NumberFieldPlace (PaperFmod D))
      (fun v => PaperLocalField D v)
      (numberFieldPrimeStripOnPlaces (F := PaperFmod D)))
    (v : NumberFieldPlace (PaperFmod D)) (g : C.total v)
    (m : (numberFieldPrimeStripOnPlaces (F := PaperFmod D)).Mon v) :
    (paperCurveFDoublePlus D C).fDagger.action v g m =
      (numberFieldPrimeStripOnPlaces (F := PaperFmod D)).action v
        (C.proj v g) m :=
  C.toFPrimeStrip_action_apply v g m

/-- The actual number-field strip has trivial action, hence trivial degree
invariance. -/
theorem numberFieldPrimeStripOnPlaces_action_apply (F : Type u) [Field F]
    [NumberField F] (v : NumberFieldPlace F)
    (g : (numberFieldPrimeStripOnPlaces (F := F)).Pi v)
    (m : (numberFieldPrimeStripOnPlaces (F := F)).Mon v) :
    (numberFieldPrimeStripOnPlaces (F := F)).action v g m = m := by
  cases v with
  | finite p =>
      change (1 : MulAut ((numberFieldPrimeStripOnPlaces (F := F)).Mon
        (NumberFieldPlace.finite p))) m = m
      rfl
  | infinite w =>
      change (1 : MulAut ((numberFieldPrimeStripOnPlaces (F := F)).Mon
        (NumberFieldPlace.infinite w))) m = m
      rfl

/-- The actual number-field action preserves the degree. -/
theorem numberFieldPrimeStripOnPlaces_degree_action (F : Type u) [Field F]
    [NumberField F] (v : NumberFieldPlace F)
    (g : (numberFieldPrimeStripOnPlaces (F := F)).Pi v)
    (m : (numberFieldPrimeStripOnPlaces (F := F)).Mon v) :
    (numberFieldPrimeStripOnPlaces (F := F)).degree v
        ((numberFieldPrimeStripOnPlaces (F := F)).action v g m) =
      (numberFieldPrimeStripOnPlaces (F := F)).degree v m := by
  rw [numberFieldPrimeStripOnPlaces_action_apply]

/-- The curve action on the actual local value monoid preserves the actual
degree. -/
theorem paperCurveFDoublePlus_degree_action
    (D : S1895PaperInput)
    (C : CurvePi1Family (NumberFieldPlace (PaperFmod D))
      (fun v => PaperLocalField D v)
      (numberFieldPrimeStripOnPlaces (F := PaperFmod D)))
    (v : NumberFieldPlace (PaperFmod D)) (g : C.total v)
    (m : (numberFieldPrimeStripOnPlaces (F := PaperFmod D)).Mon v) :
    (paperCurveFDoublePlus D C).fDagger.degree v
        ((paperCurveFDoublePlus D C).fDagger.action v g m) =
      (paperCurveFDoublePlus D C).fDagger.degree v m :=
  C.toFPrimeStrip_degree_action
    (numberFieldPrimeStripOnPlaces_degree_action (F := PaperFmod D)) v g m

/-! ## 5. The one-column attachment using S1978's actual O^× carrier -/

/-- The curve F-prime-strip on the S1978 actual local O^× strip. -/
noncomputable def paperVCurveFPrimeStrip (C : ActualPaperVCurvePi1) :
    FPrimeStrip PaperV :=
  C.toFPrimeStrip

/-- The one-column F-double-plus-carrier with the curve geometric part, on
S1965's actual one-column carrier and S1978's actual local O^× strip.  The
equivalence e is S1965's separate one-column reindexing datum. -/
noncomputable def paperCurveOneColumnFDoublePlus (D : S1895PaperInput)
    (e : NumberFieldPlace (PaperFmod D) ≃ PaperV) (C : ActualPaperVCurvePi1) :
    FDoublePlusPrimeStrip PaperV :=
  { paperOneColumnDoublePlus D e with fDagger := C.toFPrimeStrip }

/-- The one-column curve carrier keeps the actual C-mod global Frobenioid. -/
@[simp] theorem paperCurveOneColumnFDoublePlus_global
    (D : S1895PaperInput) (e : NumberFieldPlace (PaperFmod D) ≃ PaperV)
    (C : ActualPaperVCurvePi1) :
    (paperCurveOneColumnFDoublePlus D e C).global =
      paperGlobalRealifiedFrobenioid D := rfl

/-- Its F-dagger part is the S1978-monoid curve strip. -/
@[simp] theorem paperCurveOneColumnFDoublePlus_fDagger
    (D : S1895PaperInput) (e : NumberFieldPlace (PaperFmod D) ≃ PaperV)
    (C : ActualPaperVCurvePi1) :
    (paperCurveOneColumnFDoublePlus D e C).fDagger =
      paperVCurveFPrimeStrip C := rfl

/-- The one-column curve carrier has nontrivial geometric kernel. -/
theorem paperCurveOneColumnFDoublePlus_geometric_nontrivial
    (D : S1895PaperInput) (e : NumberFieldPlace (PaperFmod D) ≃ PaperV)
    (C : ActualPaperVCurvePi1) (v : PaperV) :
    (paperCurveOneColumnFDoublePlus D e C).fDagger.geometric v ≠ ⊥ :=
  C.toFPrimeStrip_geometric_nontrivial v

/-- The one-column curve carrier has nonabelian geometric kernel. -/
theorem paperCurveOneColumnFDoublePlus_geometric_nonabelian
    (D : S1895PaperInput) (e : NumberFieldPlace (PaperFmod D) ≃ PaperV)
    (C : ActualPaperVCurvePi1) (v : PaperV) :
    ∃ x y : (paperCurveOneColumnFDoublePlus D e C).fDagger.geometric v,
      x * y ≠ y * x :=
  C.toFPrimeStrip_geometric_nonabelian v

/-- The one-column curve action is the actual local O^× action composed with
the curve projection. -/
theorem paperCurveOneColumnFDoublePlus_action_apply
    (D : S1895PaperInput) (e : NumberFieldPlace (PaperFmod D) ≃ PaperV)
    (C : ActualPaperVCurvePi1) (v : PaperV) (g : C.total v)
    (m : localOFieldStrip.Mon v) :
    (paperCurveOneColumnFDoublePlus D e C).fDagger.action v g m =
      localOFieldStrip.action v (C.proj v g) m :=
  C.toFPrimeStrip_action_apply v g m

/-- The one-column curve action preserves the actual local O^× degree. -/
theorem paperCurveOneColumnFDoublePlus_degree_action
    (D : S1895PaperInput) (e : NumberFieldPlace (PaperFmod D) ≃ PaperV)
    (C : ActualPaperVCurvePi1) (v : PaperV) (g : C.total v)
    (m : localOFieldStrip.Mon v) :
    (paperCurveOneColumnFDoublePlus D e C).fDagger.degree v
        ((paperCurveOneColumnFDoublePlus D e C).fDagger.action v g m) =
      (paperCurveOneColumnFDoublePlus D e C).fDagger.degree v m :=
  C.toFPrimeStrip_degree_action localOFieldStrip_degree_action v g m

/-! ## 6. Non-fakeability of the trivial and reduced substitutes -/

/-- The actual number-field F-double-plus-carrier of S1965 has trivial
geometric kernel at every place.  It is therefore not the paper's
F-double-plus-prime-strip. -/
theorem paperModFDoublePlus_geometric_eq_bot (D : S1895PaperInput)
    (v : NumberFieldPlace (PaperFmod D)) :
    (paperModFDoublePlus D).fDagger.geometric v = ⊥ := by
  change (numberFieldPrimeStripOnPlaces (F := PaperFmod D)).geometric v = ⊥
  cases v with
  | finite p =>
      change (numberFieldPrimeStrip (F := PaperFmod D)).geometric
        (Sum.inl p.maximalIdeal) = ⊥
      exact numberFieldPrimeStrip_geometric_finite (F := PaperFmod D) p.maximalIdeal
  | infinite w =>
      change (numberFieldPrimeStrip (F := PaperFmod D)).geometric
        (Sum.inr w) = ⊥
      exact numberFieldPrimeStrip_geometric_infinite (F := PaperFmod D) w

/-- The actual number-field carrier cannot have the nontrivial geometric
kernel required by the paper. -/
theorem paperModFDoublePlus_not_geometric_nontrivial (D : S1895PaperInput)
    (v : NumberFieldPlace (PaperFmod D)) :
    ¬ (paperModFDoublePlus D).fDagger.geometric v ≠ ⊥ := by
  intro h
  exact h (paperModFDoublePlus_geometric_eq_bot D v)

/-- A curve component cannot have a trivial geometric kernel. -/
theorem CurvePi1Family.not_trivial_kernel {V : Type*} {K : V → Type*}
    [fieldK : ∀ v, Field (K v)] {S : FPrimeStrip V}
    (C : CurvePi1Family V K S) (v : V)
    (h : ((S.proj v).comp (C.proj v)).ker = ⊥) : False := by
  obtain ⟨x, hx⟩ := C.kernel_nontrivial v
  apply hx
  apply Subtype.ext
  exact Subgroup.mem_bot.mp (h ▸ x.2)

/-- A curve component cannot have an abelian geometric kernel. -/
theorem CurvePi1Family.not_abelian_kernel {V : Type*} {K : V → Type*}
    [fieldK : ∀ v, Field (K v)] {S : FPrimeStrip V}
    (C : CurvePi1Family V K S) (v : V)
    (h : ∀ x y : ((S.proj v).comp (C.proj v)).ker, x * y = y * x) : False := by
  obtain ⟨x, y, hxy⟩ := C.kernel_nonabelian v
  exact hxy (h x y)

/-- The reduced Z/2 anabelioid strip has commutative geometric kernel. -/
theorem localAnabelioidDPrimeStrip_geometric_commutative
    (v : RationalPrimePlace) :
    ∀ x y : localAnabelioidDPrimeStrip.geometric v, x * y = y * x := by
  intro x y
  apply (localAnabelioidDPrimeStrip_geometricMulEquiv v).injective
  rw [map_mul, map_mul, mul_comm]

/-- The reduced Z/2 geometric kernel cannot be equivalent to the geometric
kernel of an actual curve component. -/
theorem reducedGeometric_not_curveKernel {V : Type*} {K : V → Type*}
    [fieldK : ∀ v, Field (K v)] {S : FPrimeStrip V}
    (C : CurvePi1Family V K S) (v : V) (w : RationalPrimePlace)
    (h : Nonempty (((S.proj v).comp (C.proj v)).ker ≃*
      (localAnabelioidDPrimeStrip.geometric w))) : False := by
  rcases h with ⟨e⟩
  apply C.not_abelian_kernel v
  intro x y
  apply e.injective
  rw [map_mul, map_mul]
  exact localAnabelioidDPrimeStrip_geometric_commutative w (e x) (e y)

/-! ## 7. The exact first missing -/

/-- The exact first missing paper object: the family of actual local curve
fundamental groups with their arithmetic projections and nontrivial
nonabelian geometric kernels, over the actual C-mod places.  No inhabitant
is constructed. -/
def S2037FirstMissing (D : S1895PaperInput) : Prop :=
  Nonempty (CurvePi1Family (NumberFieldPlace (PaperFmod D))
    (fun v => PaperLocalField D v)
    (numberFieldPrimeStripOnPlaces (F := PaperFmod D)))

/-- The exact first missing is precisely the curve family: an inhabitant gives
the actual F-double-plus-carrier with nontrivial curve kernel. -/
theorem paperCurveFDoublePlus_of_firstMissing (D : S1895PaperInput)
    (h : S2037FirstMissing D) :
    ∃ P : FDoublePlusPrimeStrip (NumberFieldPlace (PaperFmod D)),
      P.global = paperGlobalRealifiedFrobenioid D ∧
      (∀ v, P.fDagger.geometric v ≠ ⊥) ∧
      (∀ v, ∃ x y : P.fDagger.geometric v, x * y ≠ y * x) := by
  rcases h with ⟨C⟩
  exact ⟨paperCurveFDoublePlus D C, rfl,
    paperCurveFDoublePlus_geometric_nontrivial D C,
    paperCurveFDoublePlus_geometric_nonabelian D C⟩

/-! ## 8. Axiom probes -/

#print axioms CurvePi1Family.toFPrimeStrip_geometric_nontrivial
#print axioms CurvePi1Family.toFPrimeStrip_geometric_nonabelian
#print axioms CurvePi1Family.toFPrimeStrip_degree_action
#print axioms paperCurveFDoublePlus
#print axioms paperCurveFDoublePlus_geometric_nontrivial
#print axioms paperCurveFDoublePlus_geometric_nonabelian
#print axioms paperCurveOneColumnFDoublePlus_geometric_nontrivial
#print axioms paperCurveOneColumnFDoublePlus_geometric_nonabelian
#print axioms localOFieldUnitsDegree_apply_eq_one
#print axioms paperModFDoublePlus_geometric_eq_bot
#print axioms localAnabelioidDPrimeStrip_geometric_commutative
#print axioms reducedGeometric_not_curveKernel
#print axioms paperCurveFDoublePlus_of_firstMissing

end LeanFormal.IUT.XiFPaper.S2037FDoublePlusPi1Actual
