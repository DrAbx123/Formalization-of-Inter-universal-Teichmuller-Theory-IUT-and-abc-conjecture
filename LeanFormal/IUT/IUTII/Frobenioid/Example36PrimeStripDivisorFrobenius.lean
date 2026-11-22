/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36FrobeniusValueAction
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge

/-!
# The Frobenius degree action on the prime-strip divisor side of Example 3.6

This module extends the value-monoid bridge of
Example36PrimeStripBridge.lean to the divisor side of the prime strip.  The
value side of item (4) of the frozen boundary card is the Frobenius power
dynamics valueFrobeniusPower (x |-> x^n) of
PrimeStripFrobenioidCategorySkeleton.lean; the present file supplies the
matching divisor-side dynamics on the concrete prime-strip divisor/value
coordinates and proves its degree and realification laws, together with the
comparison to the value-side dynamics.

The concrete prime-strip divisor coordinates are the explicit value
coordinates of the places of the number field: a finitely supported integer
valuation exponent at every finite place and the archimedean coordinate
-log (w .) at every infinite place.  This is the type
SourceModelBackend.ExplicitDivisor of the model-Frobenioid backend, which is
also the coordinate type of a global ideal family of Example 3.6.

Contents.

1. The degree-n Frobenius action divisorFrobenius n on the divisor coordinates:
   the finite exponent is multiplied by n and the archimedean coordinate is
   multiplied by n.  It is an additive endomorphism (the additive form of the
   n-th tensor power on divisor coordinates), it composes as
   divisorFrobenius (m*n) = divisorFrobenius m . divisorFrobenius n, and it is
   the additive form of the skeleton value-side power
   valueFrobeniusPower n on the multiplicative encoding
   Multiplicative (ExplicitDivisor F).
2. The action is induced by x |-> x^n on the global unit group through the
   prime-strip value maps of Example36PrimeStripBridge.lean: the finite
   coordinate of the action on the principal divisor of f is the value-side
   Frobenius power of the finite-place local value of the embedded global
   unit, and the archimedean coordinate is the value-side Frobenius power of
   the archimedean value.  On the value coordinates of a global ideal family
   the action agrees with GlobalIdealFamily.nsmul (the n-th tensor power),
   and on the principal divisor it agrees with the principal-divisor scaling
   div (f^n) = n . div f proved in Example36FrobeniusValueAction.lean.
3. Compatibility with the backend principal divisor map
   SourceModelBackend.principalDivisorExplicit: applying the Frobenius action
   to the explicit principal divisor of a rational function is the explicit
   principal divisor of the natural multiple n . u, and on the principal
   divisor of a global unit it is the explicit principal divisor of f^n.
4. Degree and realification laws for the divisor-side action (the missing
   divisor-side half of boundary card (4)).  At a finite place the divisor
   degree of a coordinate is the log-volume -d_v * log #(O_F / v), packaged
   as a FrobenioidValueKernel on the multiplicative encoding of the divisor
   coordinates; its degree and realification laws under the Frobenius action
   are proved, including the compatibility with valueFrobeniusPower.  At an
   archimedean place the divisor degree is the coordinate itself (the
   realified value -log (w .)), again packaged as a FrobenioidValueKernel
   with its power law.
5. The action preserves the effective cone: the concrete prime-strip
   effective cone of nonnegative coordinates (constructed from the actual
   finite exponents and archimedean radii) is preserved by the action, it is
   exactly the image of the constructed backend effective divisor monoid
   EffectiveDivisor under effectiveToExplicit, and the action agrees with the
   nsmul of that effective monoid.  The existing effective-cone closure
   results of Example36FrobeniusValueAction.lean are reused rather than
   reproved.

Boundary (honest).  What remains of the arithmetic-Frobenius card is the
log-shell compatibility: the source Frobenius carrier on the log-shell, its
commutation with the log-shell inclusions, and the upper-semi statements of
the vertical log-Kummer correspondence are NOT constructed here, and no field
of the reduced FrobenioidValueKernel record carries them (that record only
has degree, realification, unit, effective and transport data).  The card
remains the one recorded in the audit note of
PrimeStripFrobenioidCategorySkeleton.lean (boundary item (4), consumers
VerticalLogKummerCorrespondence.upperSemi and Ind3), and this file does not
claim it.  Also not constructed: the categorical Frobenioid C_v / C_vdash /
C_mod (card CAT), the V_K transport and rho_v normalization (boundary item
(2)), the D-prime-strip/Galois side and the geometric kernel pi_1^geo
(boundary item (1)), and any theta-pilot, q-pilot, Tate-uniformization or
Hodge-theater identification.  The Frobenius degrees here are the degree-n
power dynamics on the concrete value/divisor coordinates only; they are not
the source arithmetic Frobenius.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36
namespace PrimeStripDivisorFrobenius

open LeanFormal.IUT (FrobenioidValueKernel valueFrobeniusPower
  valueFrobeniusPower_degree valueFrobeniusPower_realification)
open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. The degree-n Frobenius action on the divisor coordinates -/

/-- The concrete prime-strip divisor/value coordinates: a finitely supported
finite-place integer exponent together with the archimedean coordinate
-log (w .) at every infinite place.  This is the explicit divisor coordinate
type of the model-Frobenioid backend and of a global ideal family. -/
abbrev PrimeStripDivisorCoordinates (F : Type u) [Field F] [NumberField F] : Type u :=
  SourceModelBackend.ExplicitDivisor F

/-- Natural multiples commute with iterated natural multiples:
(m * n) . d = m . (n . d) on the divisor coordinates. -/
theorem nsmul_nsmul_eq (m n : ℕ) (d : PrimeStripDivisorCoordinates F) :
    (m * n) • d = m • (n • d) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_mul, add_nsmul, ih, succ_nsmul]

/-- The degree-n Frobenius action on the concrete prime-strip divisor
coordinates, induced by x |-> x^n on the global unit group: at every finite
place the valuation exponent is multiplied by n, at every archimedean place
the coordinate -log (w .) is multiplied by n.  It is written as one additive
endomorphism of the coordinate group. -/
noncomputable def divisorFrobenius (n : ℕ) :
    PrimeStripDivisorCoordinates F →+ PrimeStripDivisorCoordinates F where
  toFun d := n • d
  map_zero' := nsmul_zero n
  map_add' := fun x y => nsmul_add x y n

/-- The Frobenius action is natural multiplication of the coordinate
group. -/
@[simp]
theorem divisorFrobenius_apply (n : ℕ) (d : PrimeStripDivisorCoordinates F) :
    divisorFrobenius (F := F) n d = n • d :=
  rfl

/-- The finite coordinate of the Frobenius action is the exponent multiplied
by n. -/
@[simp]
theorem divisorFrobenius_fst (n : ℕ) (d : PrimeStripDivisorCoordinates F)
    (v : HeightOneSpectrum (𝓞 F)) :
    (divisorFrobenius (F := F) n d).1 v = n • d.1 v :=
  rfl

/-- The archimedean coordinate of the Frobenius action is the coordinate
-log (w .) multiplied by n. -/
@[simp]
theorem divisorFrobenius_snd (n : ℕ) (d : PrimeStripDivisorCoordinates F)
    (w : NumberField.InfinitePlace F) :
    (divisorFrobenius (F := F) n d).2 w = n • d.2 w :=
  rfl

/-- Composition of the Frobenius degree actions: the degree-(m*n) action is
the composite of the degree-m and degree-n actions. -/
theorem divisorFrobenius_mul (m n : ℕ) :
    divisorFrobenius (F := F) (m * n) =
      (divisorFrobenius (F := F) m).comp (divisorFrobenius (F := F) n) := by
  apply AddMonoidHom.ext
  intro d
  rw [AddMonoidHom.comp_apply, divisorFrobenius_apply, divisorFrobenius_apply,
    divisorFrobenius_apply]
  exact nsmul_nsmul_eq (F := F) m n d

/-- The degree-one action is the identity. -/
theorem divisorFrobenius_one :
    divisorFrobenius (F := F) 1 = AddMonoidHom.id (PrimeStripDivisorCoordinates F) := by
  apply AddMonoidHom.ext
  intro d
  rw [divisorFrobenius_apply, one_nsmul]
  rfl

/-- The divisor-side action is the additive form of the value-side skeleton
Frobenius power on the multiplicative encoding of the divisor coordinates:
divisorFrobenius n d is the additive readback of valueFrobeniusPower n applied
to Multiplicative.ofAdd d. -/
theorem divisorFrobenius_eq_valueFrobeniusPower (n : ℕ+)
    (d : PrimeStripDivisorCoordinates F) :
    divisorFrobenius (F := F) (n : ℕ) d =
      (valueFrobeniusPower n (Multiplicative.ofAdd d)).toAdd := by
  rw [divisorFrobenius_apply, valueFrobeniusPower_apply, toAdd_pow, toAdd_ofAdd]

/-! ## 2. Induction by x |-> x^n on the global unit group -/

/-- **Finite-place coordinate of the action.**  The finite coordinate of the
Frobenius action on the explicit principal divisor of a global unit f is the
value-side Frobenius power of the finite-place local value of the embedded
global unit: this is the sense in which the divisor-side action is induced by
x |-> x^n on units through the prime-strip value map of
Example36PrimeStripBridge.lean. -/
theorem divisorFrobenius_principal_fst_valueFrobeniusPower
    (f : Fˣ) (n : ℕ+) (v : HeightOneSpectrum (𝓞 F)) :
    (divisorFrobenius (F := F) (n : ℕ)
        (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f))).1 v =
      (valueFrobeniusPower n
        (finitePlaceLocalValue (F := F) v
          (finitePlaceGlobalUnitValue (F := F) v f))).toAdd := by
  rw [divisorFrobenius_fst, SourceModelBackendDocking.principalDivisorExplicit_fst,
    valueFrobeniusPower_apply, toAdd_pow, finitePlaceLocalValue_apply, toAdd_ofAdd,
    finitePlaceGlobalUnitValue_exponent]
  simp

/-- **Archimedean coordinate of the action.**  The archimedean coordinate of
the Frobenius action on the explicit principal divisor of a global unit f is
the value-side Frobenius power of the archimedean prime-strip value
-log (w f); the minus sign of the archimedean coordinate is kept. -/
theorem divisorFrobenius_principal_snd_valueFrobeniusPower
    (f : Fˣ) (n : ℕ+) (w : NumberField.InfinitePlace F) :
    (divisorFrobenius (F := F) (n : ℕ)
        (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f))).2 w =
      (valueFrobeniusPower n (archimedeanPlaceValueUnit (F := F) w f)).toAdd := by
  rw [divisorFrobenius_snd, SourceModelBackendDocking.principalDivisorExplicit_snd,
    valueFrobeniusPower_apply, toAdd_pow, archimedeanPlaceValueUnit_apply, toAdd_ofAdd]
  unfold archimedeanPlaceValue
  simp only [toMul_ofMul]

/-- The divisor coordinates of a global ideal family: its finite-place
exponents and its archimedean coordinates. -/
noncomputable def idealFamilyDivisorCoordinates (J : GlobalIdealFamily F) :
    PrimeStripDivisorCoordinates F :=
  (J.finite, J.infinite)

/-- The finite coordinate of the divisor coordinates of a global ideal
family. -/
@[simp]
theorem idealFamilyDivisorCoordinates_fst (J : GlobalIdealFamily F) :
    (idealFamilyDivisorCoordinates (F := F) J).1 = J.finite :=
  rfl

/-- The archimedean coordinate of the divisor coordinates of a global ideal
family. -/
@[simp]
theorem idealFamilyDivisorCoordinates_snd (J : GlobalIdealFamily F)
    (w : NumberField.InfinitePlace F) :
    (idealFamilyDivisorCoordinates (F := F) J).2 w = J.infinite w :=
  rfl

/-- **Agreement with GlobalIdealFamily.nsmul.**  The divisor-side Frobenius
action on the coordinates of a global ideal family is the coordinatewise
natural multiple n . J, i.e. the n-th tensor power of the ideal family. -/
theorem idealFamilyDivisorCoordinates_nsmul (n : ℕ) (J : GlobalIdealFamily F) :
    idealFamilyDivisorCoordinates (F := F) (n • J) =
      divisorFrobenius (F := F) n (idealFamilyDivisorCoordinates (F := F) J) :=
  rfl

/-- **Agreement with principal-divisor scaling.**  On the value coordinates of
Example 3.6, the Frobenius action on the principal divisor of f^n is the
principal divisor of f scaled by the same factor n: this is
GlobalIdealFamily.nsmul applied to div f, via the principal-divisor scaling
div (f^n) = n . div f of Example36FrobeniusValueAction.lean. -/
theorem idealFamilyDivisorCoordinates_sourceModelPrincipalDivisor_pow
    (D : GlobalPlaceData F) (hD : D.HasFiniteSupport) (f : Fˣ) (n : ℕ) :
    idealFamilyDivisorCoordinates (F := F) (sourceModelPrincipalDivisor D hD (f ^ n)) =
      divisorFrobenius (F := F) n
        (idealFamilyDivisorCoordinates (F := F) (sourceModelPrincipalDivisor D hD f)) := by
  rw [FrobeniusValueAction.sourceModelPrincipalDivisor_pow, idealFamilyDivisorCoordinates_nsmul]

/-- **Compatibility with the backend principal divisor map.**  Applying the
Frobenius action to the explicit principal divisor of a rational function u is
the explicit principal divisor of the natural multiple n . u. -/
theorem divisorFrobenius_principalDivisorExplicit (u : Additive Fˣ) (n : ℕ) :
    divisorFrobenius (F := F) n (SourceModelBackend.principalDivisorExplicit (F := F) u) =
      SourceModelBackend.principalDivisorExplicit (F := F) (n • u) := by
  rw [divisorFrobenius_apply, map_nsmul]

/-- **Compatibility with the backend principal divisor map, unit form.**  The
Frobenius action on the explicit principal divisor of a global unit f is the
explicit principal divisor of f^n. -/
theorem divisorFrobenius_principalDivisorExplicit_ofMul_pow (f : Fˣ) (n : ℕ) :
    divisorFrobenius (F := F) n
        (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) =
      SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul (f ^ n)) := by
  rw [divisorFrobenius_principalDivisorExplicit, ofMul_pow]

/-! ## 3. Degree and realification laws of the divisor-side action -/

/-- The realified finite-place divisor degree of a divisor coordinate: the
log-volume -d_v * log #(O_F / v), with the normalization by the actual
residue-field cardinality of the prime-strip value layer. -/
noncomputable def finiteDivisorRealification (v : HeightOneSpectrum (𝓞 F))
    (d : PrimeStripDivisorCoordinates F) : ℝ :=
  -(d.1 v : ℝ) * Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))

/-- **Finite-place realification law.**  The realified finite-place divisor
degree of the degree-n Frobenius action is n times the realified degree of the
coordinate. -/
theorem finiteDivisorRealification_frobenius (v : HeightOneSpectrum (𝓞 F))
    (n : ℕ) (d : PrimeStripDivisorCoordinates F) :
    finiteDivisorRealification (F := F) v (divisorFrobenius (F := F) n d) =
      (n : ℝ) * finiteDivisorRealification (F := F) v d := by
  unfold finiteDivisorRealification
  rw [divisorFrobenius_fst, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
  ring

/-- The realified archimedean divisor degree of a divisor coordinate: the
archimedean coordinate -log (w .) itself. -/
noncomputable def archimedeanDivisorRealification (w : NumberField.InfinitePlace F)
    (d : PrimeStripDivisorCoordinates F) : ℝ :=
  d.2 w

/-- **Archimedean realification law.**  The realified archimedean divisor
degree of the degree-n Frobenius action is n times the realified degree of the
coordinate, with the minus sign of -log (w .) kept. -/
theorem archimedeanDivisorRealification_frobenius (w : NumberField.InfinitePlace F)
    (n : ℕ) (d : PrimeStripDivisorCoordinates F) :
    archimedeanDivisorRealification (F := F) w (divisorFrobenius (F := F) n d) =
      (n : ℝ) * archimedeanDivisorRealification (F := F) w d := by
  unfold archimedeanDivisorRealification
  rw [divisorFrobenius_snd, nsmul_eq_mul]

/-- The finite-place divisor coordinate as a monoid homomorphism on the
multiplicative encoding of the divisor coordinates: the valuation exponent at
the finite place v. -/
noncomputable def finiteDivisorCoordinate (v : HeightOneSpectrum (𝓞 F)) :
    Multiplicative (PrimeStripDivisorCoordinates F) →* Multiplicative ℤ where
  toFun m := Multiplicative.ofAdd (m.toAdd.1 v)
  map_one' := by simp
  map_mul' := by intro x y; simp [toAdd_mul, ofAdd_add]

/-- The finite divisor coordinate of a coordinate is its exponent at v. -/
@[simp]
theorem finiteDivisorCoordinate_apply (v : HeightOneSpectrum (𝓞 F))
    (m : Multiplicative (PrimeStripDivisorCoordinates F)) :
    finiteDivisorCoordinate (F := F) v m = Multiplicative.ofAdd (m.toAdd.1 v) :=
  rfl

/-- The degree map of the finite-place divisor side: the finite-place
value-group degree composed with the finite divisor coordinate. -/
noncomputable def finiteDivisorDegree (v : HeightOneSpectrum (𝓞 F)) :
    Multiplicative (PrimeStripDivisorCoordinates F) →* Multiplicative ℝ :=
  (finitePlaceValueGroupDegree (F := F) v).comp (finiteDivisorCoordinate (F := F) v)

/-- The finite divisor degree of a divisor coordinate is the normalized
log-volume of its exponent at v. -/
@[simp]
theorem finiteDivisorDegree_apply (v : HeightOneSpectrum (𝓞 F))
    (m : Multiplicative (PrimeStripDivisorCoordinates F)) :
    finiteDivisorDegree (F := F) v m = Multiplicative.ofAdd
      (-((m.toAdd.1 v : ℤ) : ℝ) *
        Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ))) := by
  rw [finiteDivisorDegree, MonoidHom.comp_apply, finiteDivisorCoordinate_apply,
    finitePlaceValueGroupDegree_apply, toAdd_ofAdd]

/-- The finite-place degree kernel of the divisor-side action: a
FrobenioidValueKernel on the multiplicative encoding of the divisor
coordinates whose degree is the finite-place log-volume and whose
realification is its additive form. -/
noncomputable def finiteDivisorKernel (v : HeightOneSpectrum (𝓞 F)) :
    FrobenioidValueKernel (Multiplicative (PrimeStripDivisorCoordinates F)) where
  degree := finiteDivisorDegree (F := F) v
  realification := fun m => finiteDivisorRealification (F := F) v m.toAdd
  realification_mul := by
    intro x y
    rw [toAdd_mul]
    unfold finiteDivisorRealification
    have h : (((x.toAdd + y.toAdd).1 v : ℤ) : ℝ) =
        (x.toAdd.1 v : ℝ) + (y.toAdd.1 v : ℝ) := by simp
    rw [h]
    ring
  degree_realification := by
    intro m
    rfl
  unit := 1
  unit_realification := by
    simp [finiteDivisorRealification]
  effective := fun _ => True
  effective_proved := fun _ => trivial
  transport := id
  transport_degree := by intro m; rfl

/-- The realification of the finite-place divisor kernel is the finite-place
log-volume of the underlying coordinate. -/
@[simp]
theorem finiteDivisorKernel_realification (v : HeightOneSpectrum (𝓞 F))
    (m : Multiplicative (PrimeStripDivisorCoordinates F)) :
    (finiteDivisorKernel (F := F) v).realification m =
      finiteDivisorRealification (F := F) v m.toAdd :=
  rfl

/-- The archimedean divisor coordinate as a monoid homomorphism on the
multiplicative encoding of the divisor coordinates: the coordinate -log (w .)
at the infinite place w. -/
noncomputable def archimedeanDivisorCoordinate (w : NumberField.InfinitePlace F) :
    Multiplicative (PrimeStripDivisorCoordinates F) →* archimedeanValueGroup where
  toFun m := Multiplicative.ofAdd (m.toAdd.2 w)
  map_one' := by simp
  map_mul' := by intro x y; simp [toAdd_mul, ofAdd_add]

/-- The archimedean divisor coordinate of a coordinate is its value at w. -/
@[simp]
theorem archimedeanDivisorCoordinate_apply (w : NumberField.InfinitePlace F)
    (m : Multiplicative (PrimeStripDivisorCoordinates F)) :
    archimedeanDivisorCoordinate (F := F) w m =
      Multiplicative.ofAdd (m.toAdd.2 w) :=
  rfl

/-- The archimedean degree kernel of the divisor-side action: a
FrobenioidValueKernel whose degree is the archimedean coordinate
-log (w .) in the value group and whose realification is its additive form. -/
noncomputable def archimedeanDivisorKernel (w : NumberField.InfinitePlace F) :
    FrobenioidValueKernel (Multiplicative (PrimeStripDivisorCoordinates F)) where
  degree := archimedeanDivisorCoordinate (F := F) w
  realification := fun m => m.toAdd.2 w
  realification_mul := by
    intro x y
    rw [toAdd_mul]
    rfl
  degree_realification := by
    intro m
    rfl
  unit := 1
  unit_realification := by simp
  effective := fun _ => True
  effective_proved := fun _ => trivial
  transport := id
  transport_degree := by intro m; rfl

/-- The realification of the archimedean divisor kernel is the archimedean
coordinate of the underlying divisor. -/
@[simp]
theorem archimedeanDivisorKernel_realification (w : NumberField.InfinitePlace F)
    (m : Multiplicative (PrimeStripDivisorCoordinates F)) :
    (archimedeanDivisorKernel (F := F) w).realification m = m.toAdd.2 w :=
  rfl

/-- **Finite-place degree law, value-side form.**  The degree of the n-th
skeleton Frobenius power in the finite-place divisor kernel is the n-th power
of the degree of the coordinate. -/
theorem finiteDivisorDegree_valueFrobeniusPower (v : HeightOneSpectrum (𝓞 F))
    (n : ℕ+) (m : Multiplicative (PrimeStripDivisorCoordinates F)) :
    (finiteDivisorKernel (F := F) v).degree (valueFrobeniusPower n m) =
      ((finiteDivisorKernel (F := F) v).degree m) ^ (n : ℕ) :=
  valueFrobeniusPower_degree (finiteDivisorKernel (F := F) v) n m

/-- **Finite-place degree law.**  The finite-place divisor degree of the
degree-n Frobenius action is the n-th power of the finite-place divisor degree
of the coordinate.  This is the divisor-side degree law matching the value-side
valueFrobeniusPower degree law. -/
theorem finiteDivisorDegree_frobenius (v : HeightOneSpectrum (𝓞 F))
    (n : ℕ+) (d : PrimeStripDivisorCoordinates F) :
    finiteDivisorDegree (F := F) v
        (Multiplicative.ofAdd (divisorFrobenius (F := F) (n : ℕ) d)) =
      (finiteDivisorDegree (F := F) v (Multiplicative.ofAdd d)) ^ (n : ℕ) := by
  rw [divisorFrobenius_eq_valueFrobeniusPower]
  exact finiteDivisorDegree_valueFrobeniusPower (F := F) v n (Multiplicative.ofAdd d)

/-- **Archimedean realification law.**  The realified archimedean divisor
degree of the n-th skeleton Frobenius power is n times the realified degree of
the coordinate; this is the additive form of the archimedean degree law. -/
theorem archimedeanDivisorKernel_valueFrobeniusPower (w : NumberField.InfinitePlace F)
    (n : ℕ+) (m : Multiplicative (PrimeStripDivisorCoordinates F)) :
    (archimedeanDivisorKernel (F := F) w).realification (valueFrobeniusPower n m) =
      (n : ℝ) * (archimedeanDivisorKernel (F := F) w).realification m :=
  valueFrobeniusPower_realification (archimedeanDivisorKernel (F := F) w) m n

/-- **Archimedean degree law.**  The archimedean divisor degree of the
degree-n Frobenius action is the n-th power of the archimedean divisor degree
of the coordinate. -/
theorem archimedeanDivisorDegree_frobenius (w : NumberField.InfinitePlace F)
    (n : ℕ+) (d : PrimeStripDivisorCoordinates F) :
    (archimedeanDivisorKernel (F := F) w).degree
        (Multiplicative.ofAdd (divisorFrobenius (F := F) (n : ℕ) d)) =
      ((archimedeanDivisorKernel (F := F) w).degree
        (Multiplicative.ofAdd d)) ^ (n : ℕ) := by
  rw [divisorFrobenius_eq_valueFrobeniusPower]
  exact valueFrobeniusPower_degree (archimedeanDivisorKernel (F := F) w) n
    (Multiplicative.ofAdd d)

/-! ## 4. The effective cone under the Frobenius action -/

/-- **Effective cone preservation.**  The nonnegative cone of the explicit
divisor group (the effective cone of the model-Frobenioid backend) is
preserved by the degree-n Frobenius action; this reuses the nsmul_mem closure
of Example36FrobeniusValueAction.lean. -/
theorem divisorFrobenius_explicitNonneg (n : ℕ) {d : PrimeStripDivisorCoordinates F}
    (h : SourceModelBackend.explicitNonneg d) :
    SourceModelBackend.explicitNonneg (divisorFrobenius (F := F) n d) := by
  rw [divisorFrobenius_apply]
  exact FrobeniusValueAction.explicitNonneg_nsmul n h

/-- **Agreement with the effective divisor monoid.**  On the image of the
constructed backend effective divisor monoid, the Frobenius action is the
nsmul of the effective monoid, i.e. the n-th tensor power of effective
divisors. -/
theorem divisorFrobenius_effectiveToExplicit (n : ℕ)
    (m : SourceModelBackend.EffectiveDivisor F) :
    divisorFrobenius (F := F) n (SourceModelBackend.effectiveToExplicit (F := F) m) =
      SourceModelBackend.effectiveToExplicit (F := F) (n • m) := by
  rw [divisorFrobenius_apply, map_nsmul]

/-- The concrete prime-strip effective cone: the nonnegative divisor
coordinates, constructed from the actual finite exponents and archimedean
radii of Example 3.6. -/
def primeStripEffectiveCone : AddSubmonoid (PrimeStripDivisorCoordinates F) where
  carrier := {d | SourceModelBackend.explicitNonneg d}
  zero_mem' := ⟨fun _ => le_refl 0, fun _ => le_refl 0⟩
  add_mem' := fun ha hb => SourceModelBackend.explicitNonneg_add ha hb

/-- Membership in the concrete prime-strip effective cone is coordinatewise
nonnegativity. -/
@[simp]
theorem mem_primeStripEffectiveCone {d : PrimeStripDivisorCoordinates F} :
    d ∈ primeStripEffectiveCone (F := F) ↔ SourceModelBackend.explicitNonneg d :=
  Iff.rfl

/-- **The effective cone is preserved by the Frobenius action (nsmul_mem).** -/
theorem divisorFrobenius_primeStripEffectiveCone (n : ℕ)
    {d : PrimeStripDivisorCoordinates F}
    (h : d ∈ primeStripEffectiveCone (F := F)) :
    divisorFrobenius (F := F) n d ∈ primeStripEffectiveCone (F := F) :=
  divisorFrobenius_explicitNonneg (F := F) n h

/-- **The concrete effective divisor monoid of the prime strip.**  The
prime-strip effective cone is exactly the image of the constructed backend
effective divisor monoid EffectiveDivisor under effectiveToExplicit: this is
the divisor monoid built from the actual finite exponents and archimedean
radii, and its nsmul is the Frobenius action. -/
theorem mem_primeStripEffectiveCone_iff_exists_effectiveDivisor
    (d : PrimeStripDivisorCoordinates F) :
    d ∈ primeStripEffectiveCone (F := F) ↔
      ∃ m : SourceModelBackend.EffectiveDivisor F,
        SourceModelBackend.effectiveToExplicit (F := F) m = d := by
  constructor
  · rintro ⟨hfin, hinf⟩
    let m : SourceModelBackend.EffectiveDivisor F :=
      (Finsupp.onFinset d.1.support (fun v => (d.1 v).toNat)
          (fun v hv => Finsupp.mem_support_iff.mpr
            (fun h => hv (by rw [h]; rfl))),
        fun w => (d.2 w).toNNReal)
    refine ⟨m, ?_⟩
    apply Prod.ext
    · ext v
      change (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) m.1) v = d.1 v
      rw [Finsupp.mapRange_apply, Finsupp.onFinset_apply]
      exact Int.toNat_of_nonneg (hfin v)
    · funext w
      change ((d.2 w).toNNReal : ℝ) = d.2 w
      rw [Real.toNNReal_of_nonneg (hinf w)]
      rfl
  · rintro ⟨m, rfl⟩
    exact SourceModelBackend.effectiveToExplicit_nonneg (F := F) m

end PrimeStripDivisorFrobenius
end Example36
end LeanFormal.IUT.IUTII.Frobenioid
