import tmp.sheaf.xif.paper.S2296TateBaseUnitActual
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# S2420: the l-torsion coprime representative of the D6 branch

## Target

`S2296LCoprimeRepresentative T b` (`S2296TateBaseUnitActual`, line 574) is the
D6 `l`-torsion input of the K-side Tate comparison: a Galois-fixed `l`-torsion
point `P` of the K-side Tate point group together with a unit `x` of the
completion `K_v` such that

`pointEquiv (mk (unitsMap x)) = ofAdd P`, `x ^ l = q_v ^ m`, `Nat.Coprime l m.natAbs`.

The representative `x` lives in `(Kv T b)ˣ`, not in the algebraic closure.

## Main result: the target is equivalent to the paper's l-th power condition

This file proves the converse of S2296's
`S2190QLthPowerSource_of_LCoprimeRepresentative` and hence the equivalence

`S2296LCoprimeRepresentative T b ↔ S2190QLthPowerSource T b`

(`LCoprimeRepresentative_iff_lthPowerSource`).  The same arithmetic is localized
on the Tate side as

`S2296LCoprimeRepresentative T b ↔
  ∃ x : (LK T b)ˣ, (x : LK T b) ^ l = algebraMap q_v ∧ IsGaloisFixed (class of x)`

(`LCoprimeRepresentative_iff_exists_fixed_root`): the target says exactly that
one `l`-th root of `q_v` in the closure has a Galois-fixed Tate class.

Consequence for the D6 branch: no construction of `l`-torsion points alone can
produce the target.  S2296 already constructs representatives for every
Galois-fixed `l`-torsion point (`tateDescent`) and extracts a coprime exponent
from `l + 1` distinct such points (`LCoprimeRepresentative_of_many_lTorsion`);
what the target additionally carries is `q_v ∈ K_v ^ l`.

## The paper route, reduced to one local input

The paper derives `q_v ^ (1/l) ∈ K_v` from clause (c) (`K = F(E[l])`) through
the Tate uniformization: `K ⊆ K_v` makes every `l`-torsion point of the K-side
Tate group `K_v`-rational, hence Galois fixed; the Tate class of `q_v ^ (1/l)`
is one of them; and an `l`-th root of `q_v` with Galois-fixed Tate class is
itself in `K_v`.  That last Tate--Kummer step is proved here:

* `exists_lthRoot_in_Kv_of_fixed_class`: if `x ^ l = q_v` in the closure and the
  Tate class of `x` is Galois fixed, then `q_v` is an `l`-th power in `K_v`.
  (`sigma x / x` is then both an `l`-th root of unity and an integral power of
  the Tate unit, and `q_v ^ Z ∩ mu_l = 1` by `tateUnit_zpow_eq_one_of_pow_eq_one`.)

The single local input used by the paper route is therefore

`S2420ModLTrivial T b : ∀ P, l • P = 0 → IsGaloisFixed T b P`

and the reduction is `LCoprimeRepresentative_of_modLTrivial`, with the composite
`QLthPowerSource_of_modLTrivial`.  This input is *not* derived here; Section 6
records the three API gaps between clause (c) and it, and the named missing
statements `S2420LTorsionCardMissing`, `S2420KernelFieldBridgeMissing`.

## Content

1. Tate classes of units of `K_v` are Galois fixed.
2. An `l`-th root of `q_v` in the closure has an `l`-torsion Tate class.
3. The Tate--Kummer step and the target from an `l`-th root of `q_v`.
4. The equivalence with `S2190QLthPowerSource` and the local-input reduction.
5. The counting route (`S2420FixedLTorsionCard`, S2296).
6. The exact missing API, with `#check`s of the existing neighbouring API.
7. Axiom audit.

No `sorry`, no `axiom`, no `True`/`PUnit` slot, no `Nonempty` gate, and no
assumption is added to the target.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2420LCoprimeRepresentativeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S436KSideQVActual
open LeanFormal.IUT.XiFPaper.S1550TatePointComparisonFromClosureActual
open LeanFormal.IUT.XiFPaper.S2223TateBridgeActual
open LeanFormal.IUT.XiFPaper.S2190RootSourceConditionsActual
open LeanFormal.IUT.XiFPaper.S2296TateBaseUnitActual
open WeierstrassCurve

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. Tate classes of units of the completion are Galois fixed -/

/-- The image in the closure of a unit of the completion is fixed by every
K_v-automorphism of the closure. -/
theorem unitsMap_galois_fixed (sigma : GalK T b) (x : (Kv T b)ˣ) :
    Units.map sigma.toRingEquiv.toMonoidHom (unitsMap T b x) = unitsMap T b x := by
  apply Units.ext
  rw [Units.coe_map, Units.coe_map]
  exact sigma.commutes (x : Kv T b)

/-- Every Tate class coming from a unit of the completion K_v is Galois fixed. -/
theorem isGaloisFixed_pointEquiv_mk (x : (Kv T b)ˣ) :
    IsGaloisFixed T b (pointEquiv T b (QuotientGroup.mk (unitsMap T b x))).toAdd := by
  intro sigma
  have h := pointEquiv_galois_naturality (T := T) (b := b) sigma (unitsMap T b x)
  rw [unitsMap_galois_fixed T b sigma x] at h
  exact (congrArg Multiplicative.toAdd h).symm

/-! ## 2. The l-th roots of q_v have l-torsion Tate classes -/

/-- If the l-th power of a unit of the closure is the image of q_v, then its Tate
class is l-torsion. -/
theorem lTorsion_pointEquiv_mk (x : (LK T b)ˣ)
    (hx : (x : LK T b) ^ l.value = algebraMap (Kv T b) (LK T b) (tateQ T b)) :
    l.value • (pointEquiv T b (QuotientGroup.mk x)).toAdd = 0 := by
  have hx' : x ^ l.value =
      unitsMap T b (Units.mk0 (tateQ T b) (LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual.sectionQ T b).q_ne_zero) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hx
  have hmk : (QuotientGroup.mk x : DeckK T b) ^ l.value = 1 := by
    rw [← QuotientGroup.mk_pow, hx']
    simpa using mk_unitsMap_tateQ_zpow T b 1
  have h2 : (pointEquiv T b (QuotientGroup.mk x)) ^ l.value = 1 := by
    rw [← map_pow (pointEquiv T b) (QuotientGroup.mk x) l.value, hmk, map_one]
  have h3 : Multiplicative.ofAdd
      (l.value • (pointEquiv T b (QuotientGroup.mk x)).toAdd) = 1 := by
    rw [ofAdd_nsmul]
    exact h2
  simpa using congrArg Multiplicative.toAdd h3

/-! ## 3. The Tate--Kummer step -/

/-- **The Tate--Kummer step.**  An l-th root of q_v in the closure whose Tate
class is Galois fixed is already defined over K_v; equivalently q_v is an l-th
power of the completion. -/
theorem exists_lthRoot_in_Kv_of_fixed_class (x : (LK T b)ˣ)
    (hx : (x : LK T b) ^ l.value = algebraMap (Kv T b) (LK T b) (tateQ T b))
    (hfix : IsGaloisFixed T b (pointEquiv T b (QuotientGroup.mk x)).toAdd) :
    S2190QLthPowerSource T b := by
  classical
  have hx' : x ^ l.value =
      unitsMap T b (Units.mk0 (tateQ T b) (LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual.sectionQ T b).q_ne_zero) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hx
  -- fixedness of the class means sigma x / x lies in q_v ^ Z
  have hclass : forall sigma : GalK T b,
      QuotientGroup.mk (Units.map sigma.toRingEquiv.toMonoidHom x) =
        (QuotientGroup.mk x : DeckK T b) := by
    intro sigma
    apply (pointEquiv T b).injective
    have h := pointEquiv_galois_naturality (T := T) (b := b) sigma x
    rw [hfix sigma] at h
    simpa using h
  have hdiv : forall sigma : GalK T b, exists j : Int,
      Units.map sigma.toRingEquiv.toMonoidHom x / x = (tateUnit T b) ^ j := by
    intro sigma
    obtain ⟨j, hj⟩ :=
      Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq_iff_div_mem.mp (hclass sigma))
    exact ⟨j, hj.symm⟩
  -- and it is an l-th root of unity
  have hroot : forall sigma : GalK T b,
      (Units.map sigma.toRingEquiv.toMonoidHom x / x) ^ l.value = 1 := by
    intro sigma
    have hsigmapow : (Units.map sigma.toRingEquiv.toMonoidHom x) ^ l.value =
        x ^ l.value := by
      rw [← map_pow (Units.map sigma.toRingEquiv.toMonoidHom) x l.value, hx']
      exact unitsMap_galois_fixed T b sigma
        (Units.mk0 (tateQ T b) (LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual.sectionQ T b).q_ne_zero)
    rw [div_pow, hsigmapow]
    simp
  -- so q_v ^ Z intersection mu_l is trivial, forcing sigma x = x
  have hone : forall sigma : GalK T b,
      Units.map sigma.toRingEquiv.toMonoidHom x = x := by
    intro sigma
    obtain ⟨j, hj⟩ := hdiv sigma
    have hjpow : ((tateUnit T b) ^ j) ^ l.value = 1 := by
      have h := hroot sigma
      rwa [hj] at h
    have hj0 : j = 0 := tateUnit_zpow_eq_one_of_pow_eq_one T b l.prime.pos hjpow
    have h1 : Units.map sigma.toRingEquiv.toMonoidHom x / x = 1 := by
      rw [hj, hj0, zpow_zero]
    exact div_eq_one.mp h1
  -- hence x is fixed by the absolute Galois group and lies in K_v
  have hrange : (x : LK T b) ∈ Set.range (algebraMap (Kv T b) (LK T b)) := by
    refine (InfiniteGalois.mem_range_algebraMap_iff_fixed (x : LK T b)).mpr ?_
    intro sigma
    have h1 := congrArg Units.val (hone sigma)
    simpa using h1
  obtain ⟨a, ha⟩ := hrange
  refine ⟨a, ?_⟩
  have h : (algebraMap (Kv T b) (LK T b)) (a ^ l.value) =
      (algebraMap (Kv T b) (LK T b)) (tateQ T b) := by
    rw [map_pow, ha]
    exact hx
  exact (algebraMap (Kv T b) (LK T b)).injective h

/-! ## 4. The target from an l-th root of q_v -/

/-- A unit of the completion whose l-th power is q_v gives the target with
exponent m = 1. -/
theorem LCoprimeRepresentative_of_unit_pow_eq (x : (Kv T b)ˣ)
    (hx : (x : Kv T b) ^ l.value = tateQ T b) :
    S2296LCoprimeRepresentative T b := by
  have hxL : ((unitsMap T b x : (LK T b)ˣ) : LK T b) ^ l.value =
      algebraMap (Kv T b) (LK T b) (tateQ T b) := by
    have h1 : ((unitsMap T b x : (LK T b)ˣ) : LK T b) =
        algebraMap (Kv T b) (LK T b) (x : Kv T b) := rfl
    rw [h1, ← map_pow (algebraMap (Kv T b) (LK T b)) (x : Kv T b) l.value, hx]
  refine ⟨(pointEquiv T b (QuotientGroup.mk (unitsMap T b x))).toAdd, x, 1,
    isGaloisFixed_pointEquiv_mk T b x,
    lTorsion_pointEquiv_mk T b (unitsMap T b x) hxL, rfl, ?_, ?_⟩
  · rw [zpow_one]
    exact hx
  · rw [show (1 : Int).natAbs = 1 from rfl]
    exact (Nat.coprime_one_right_iff l.value).mpr trivial

/-- An l-th root of q_v in the closure with Galois-fixed Tate class gives the
target. -/
theorem LCoprimeRepresentative_of_fixed_root (x : (LK T b)ˣ)
    (hx : (x : LK T b) ^ l.value = algebraMap (Kv T b) (LK T b) (tateQ T b))
    (hfix : IsGaloisFixed T b (pointEquiv T b (QuotientGroup.mk x)).toAdd) :
    S2296LCoprimeRepresentative T b := by
  obtain ⟨a, ha⟩ := exists_lthRoot_in_Kv_of_fixed_class T b x hx hfix
  have ha0 : a ≠ 0 := by
    intro h0
    apply (LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual.sectionQ T b).q_ne_zero
    rw [← ha, h0]
    exact zero_pow l.prime.pos.ne'
  exact LCoprimeRepresentative_of_unit_pow_eq T b (Units.mk0 a ha0) (by
    rw [Units.val_mk0]
    exact ha)

/-- The target from the paper source condition S2190QLthPowerSource. -/
theorem LCoprimeRepresentative_of_lthPowerSource (h : S2190QLthPowerSource T b) :
    S2296LCoprimeRepresentative T b := by
  obtain ⟨r, hr⟩ := h
  have hr0 : r ≠ 0 := by
    intro h0
    apply (LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual.sectionQ T b).q_ne_zero
    rw [← hr, h0]
    exact zero_pow l.prime.pos.ne'
  exact LCoprimeRepresentative_of_unit_pow_eq T b (Units.mk0 r hr0) (by
    rw [Units.val_mk0]
    exact hr)

/-- **The D6 l-torsion input is equivalent to the paper's l-th power condition.**
The unit representative of S2296LCoprimeRepresentative is a unit of K_v, so the
target carries exactly the arithmetic content of q_v in K_v ^ l. -/
theorem LCoprimeRepresentative_iff_lthPowerSource :
    S2296LCoprimeRepresentative T b ↔ S2190QLthPowerSource T b :=
  ⟨S2190QLthPowerSource_of_LCoprimeRepresentative T b,
    LCoprimeRepresentative_of_lthPowerSource T b⟩

/-- The target is also exactly the fixedness of the Tate class of an l-th root of
q_v in the closure. -/
theorem LCoprimeRepresentative_iff_exists_fixed_root :
    S2296LCoprimeRepresentative T b ↔
      ∃ x : (LK T b)ˣ,
        (x : LK T b) ^ l.value = algebraMap (Kv T b) (LK T b) (tateQ T b) ∧
          IsGaloisFixed T b (pointEquiv T b (QuotientGroup.mk x)).toAdd := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := S2190QLthPowerSource_of_LCoprimeRepresentative T b h
    have hr0 : r ≠ 0 := by
      intro h0
      apply (LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual.sectionQ T b).q_ne_zero
      rw [← hr, h0]
      exact zero_pow l.prime.pos.ne'
    refine ⟨unitsMap T b (Units.mk0 r hr0), ?_,
      isGaloisFixed_pointEquiv_mk T b (Units.mk0 r hr0)⟩
    have h1 : ((unitsMap T b (Units.mk0 r hr0) : (LK T b)ˣ) : LK T b) =
        algebraMap (Kv T b) (LK T b) r := rfl
    rw [h1, ← map_pow (algebraMap (Kv T b) (LK T b)) r l.value, hr]
  · rintro ⟨x, hx, hfix⟩
    exact LCoprimeRepresentative_of_fixed_root T b x hx hfix

/-! ## 5. The paper route from the local l-torsion triviality -/

/-- The local l-torsion triviality of the K-side Tate group: every l-torsion class
is fixed by the absolute Galois group of K_v.  This is the local consequence of
clause (c) (K = F(E[l]), hence K a subfield of K_v) used by the paper through the
Tate uniformization.  It is the exact missing input of this branch and is not
derived in this file (see Section 6). -/
def S2420ModLTrivial : Prop :=
  forall P : SideKPoint T b, l.value • P = 0 -> IsGaloisFixed T b P

/-- **The paper route: local l-torsion triviality gives the D6 target.**
Take the Tate class of an l-th root of q_v in the closure; it is l-torsion by
Section 2 and hence fixed by hypothesis, and Section 3 puts the root in K_v. -/
theorem LCoprimeRepresentative_of_modLTrivial (h : S2420ModLTrivial T b) :
    S2296LCoprimeRepresentative T b := by
  obtain ⟨z, hz⟩ :=
    IsAlgClosed.exists_pow_nat_eq (algebraMap (Kv T b) (LK T b) (tateQ T b))
      l.prime.pos
  have hz0 : z ≠ 0 := by
    intro h0
    have h1 : (algebraMap (Kv T b) (LK T b)) (tateQ T b) = 0 := by
      rw [← hz, h0, zero_pow l.prime.pos.ne']
    exact (LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual.sectionQ T b).q_ne_zero
      ((algebraMap (Kv T b) (LK T b)).injective (by simpa using h1))
  have hx : ((Units.mk0 z hz0 : (LK T b)ˣ) : LK T b) ^ l.value =
      algebraMap (Kv T b) (LK T b) (tateQ T b) := by
    rw [Units.val_mk0]
    exact hz
  have htors := lTorsion_pointEquiv_mk T b (Units.mk0 z hz0) hx
  exact LCoprimeRepresentative_of_fixed_root T b (Units.mk0 z hz0) hx
    (h _ htors)

/-- Consequently the local l-torsion triviality gives the paper source condition
that q_v is an l-th power in K_v. -/
theorem QLthPowerSource_of_modLTrivial (h : S2420ModLTrivial T b) :
    S2190QLthPowerSource T b :=
  (LCoprimeRepresentative_iff_lthPowerSource T b).mp
    (LCoprimeRepresentative_of_modLTrivial T b h)

/-- The counting form of the geometric input: l + 1 distinct Galois-fixed
l-torsion points of the K-side Tate group.  This is the input of S2296's
LCoprimeRepresentative_of_many_lTorsion. -/
def S2420FixedLTorsionCard : Prop :=
  ∃ S : Finset (SideKPoint T b), l.value < S.card ∧
    ∀ P ∈ S, l.value • P = 0 ∧ IsGaloisFixed T b P

/-- The counting input gives the D6 target (S2296, repackaged). -/
theorem LCoprimeRepresentative_of_fixedLTorsionCard
    (h : S2420FixedLTorsionCard T b) :
    S2296LCoprimeRepresentative T b := by
  obtain ⟨S, hcard, hS⟩ := h
  exact LCoprimeRepresentative_of_many_lTorsion T b S hcard
    (fun P hP => (hS P hP).1) (fun P hP => (hS P hP).2)

/-! ## 6. The exact missing API

### 6.1 What the tree already supplies (checked below)

* galoisLTorsionKernelField_fixingSubgroup, galoisLTorsionMatrixRepresentation_acts:
  the kernel of the mod-l representation fixes every l-torsion point.  This is the
  pointwise form of clause (c)'s K = F(E[l]) at the level of the global closure
  AlgebraicClosure T.arithmetic.F.
* S2190RootSourceConditionsActual.actual_kernel_field_data: the actual clause-(c)
  identification T.arithmetic.K ≃_F galoisLTorsionKernelField l torsion_basis.
* S1493KSideTateTransportActual.baseChange_curve_map_eq: the F_v/K_v curve
  comparison realizing the K-side curve.
* InitialThetaSource.PuncturedEllipticCurve.initialThetaKToFTorsionTransport: the
  *global* closure transport of the l-torsion, from AlgebraicClosure K to
  AlgebraicClosure F; its audit note explicitly says that no descent of torsion
  points to K is claimed.
* tateDescent, LCoprimeRepresentative_of_many_lTorsion, exists_coprime_of_card_gt
  (S2296): once l + 1 distinct fixed l-torsion points are given, the target
  follows.  Also tateUnit_zpow_eq_one_of_pow_eq_one (q_v ^ Z ∩ mu_l = 1), used in
  Section 3.

### 6.2 What is missing

1. S2420LTorsionCardMissing: the cardinality of the l-torsion of the K-side Tate
   point group over the closure.  The tree only has the geometric 2- and 3-torsion
   counts (S1704, through the 2- and 3-division polynomials); there is no
   l-division polynomial API and no proof that E[l] is (ZMod l)^2 for general l.
   Without it the counting route cannot even be started from clause (c) alone.
2. A base-change comparison of the l-torsion along K -> K_v -> LK with the
   pointEquiv/DeckK model: every l-torsion class over the closure is the base
   change of an l-torsion point over Completion (sectionKPlace T b).
   initialThetaKToFTorsionTransport compares the two *global* closures only; the
   local section place and the identification of its completion with the DeckK
   quotient are not part of it.
3. S2420KernelFieldBridgeMissing: the step from clause (c)'s
   kernel_field_identification to S2420ModLTrivial, combining 1 and 2 with the
   compatibility of the section place K -> K_v with the embedding of K into the
   closure used by galoisLTorsionKernelField.

With (3) the paper route closes with no further input:

S2420ModLTrivial T b -> S2296LCoprimeRepresentative T b -> S2190QLthPowerSource T b

(LCoprimeRepresentative_of_modLTrivial, QLthPowerSource_of_modLTrivial).
-/

/-- Missing API 1: the l-torsion of the K-side Tate point group over the closure
has l^2 elements.  True for an elliptic curve over an algebraically closed field
of characteristic zero, but not available in the tree for general l (only the 2-
and 3-torsion counts of S1704 exist). -/
def S2420LTorsionCardMissing : Prop :=
  Nat.card { P : SideKPoint T b // l.value • P = 0 } = l.value ^ 2

/-- Missing API 3: the bridge from clause (c)'s kernel-field identification to the
local l-torsion triviality S2420ModLTrivial.  The proposition is stated as an
implication whose antecedent is the actual clause-(c) data; its proof would need
the two base-change and cardinality items above. -/
def S2420KernelFieldBridgeMissing : Prop :=
  (T.arithmetic.K ≃ₐ[T.arithmetic.F]
      T.arithmetic.curve.galoisLTorsionKernelField l T.clauseC.torsion_basis) ->
    S2420ModLTrivial T b

/-- The exact missing bridge, applied to the actual clause-(c) data, would give the
local triviality; recorded here so that the remaining gap is a single named
statement. -/
theorem modLTrivial_of_kernelFieldBridge
    (h : S2420KernelFieldBridgeMissing T b) : S2420ModLTrivial T b :=
  h T.clauseC.kernel_field_identification

#check PuncturedEllipticCurve.LTorsion
#check PuncturedEllipticCurve.galoisActionOnPoint
#check PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation_acts
#check PuncturedEllipticCurve.galoisLTorsionKernelField_fixingSubgroup
#check S2190RootSourceConditionsActual.actual_kernel_field_data
#check S1493KSideTateTransportActual.baseChange_curve_map_eq
#check InitialThetaSource.PuncturedEllipticCurve.initialThetaKToFTorsionTransport
#check S2296TateBaseUnitActual.tateDescent
#check S2296TateBaseUnitActual.exists_coprime_of_card_gt
#check S2296TateBaseUnitActual.LCoprimeRepresentative_of_many_lTorsion
#check S2296TateBaseUnitActual.tateUnit_zpow_eq_one_of_pow_eq_one

/-! ## 7. Axiom audit -/

#print axioms unitsMap_galois_fixed
#print axioms isGaloisFixed_pointEquiv_mk
#print axioms lTorsion_pointEquiv_mk
#print axioms exists_lthRoot_in_Kv_of_fixed_class
#print axioms LCoprimeRepresentative_of_unit_pow_eq
#print axioms LCoprimeRepresentative_of_fixed_root
#print axioms LCoprimeRepresentative_of_lthPowerSource
#print axioms LCoprimeRepresentative_iff_lthPowerSource
#print axioms LCoprimeRepresentative_iff_exists_fixed_root
#print axioms LCoprimeRepresentative_of_modLTrivial
#print axioms QLthPowerSource_of_modLTrivial
#print axioms LCoprimeRepresentative_of_fixedLTorsionCard
#print axioms modLTrivial_of_kernelFieldBridge

end LeanFormal.IUT.XiFPaper.S2420LCoprimeRepresentativeActual
