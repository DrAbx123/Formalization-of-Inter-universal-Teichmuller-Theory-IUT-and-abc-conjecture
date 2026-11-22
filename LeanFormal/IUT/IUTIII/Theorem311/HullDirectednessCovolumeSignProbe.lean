import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2CardReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import Mathlib.Tactic

/-!
# Probes for the candidate routes T2 / T4 / T6 (run hull-presentation-routes-20261016)

This file records machine-checked toy/conditional probes for three candidate routes
proposed in `logs/coordination/wild-brainstorm-20261017.md` (Meitner), each aiming at
the frozen `hpres` / R9 / ②-wall gaps:

* T4 (`K1K2Realization` section): the directedness / principal-filter characterization
  of `LogShellRayPresentation`, the "finite union of rays" relaxation, and a fresh
  single-witness separation for the ray presentation.
* T2 (`CovolumeGapToy` section): a box/covolume toy for the lattice reading of R9
  (candidate reading G1, `hull = O_Kv-span`), with the exact gap formula, the
  boundary-order bound, and the zero gap in the span (no-overshoot) case.
* T6 (`HullSignAudit` section): the `ENNReal.toReal` top gate, the single-point
  dominator reduction for the certificate premise `ofReal q ≤ logVolume imageSet`,
  and the sign case analysis of `-|log q|`.

Honesty boundary: every statement below is a toy or conditional probe in its own
toy vocabulary.  No claim is made about the real log-shell carrier, about reading G1
(which remains candidate/needs-verification), or about the paper's original text.
The T4 transfer theorems are stated for arbitrary `(P, Q, L)`, so they sharpen the
interface level; the T2 numbers are box numbers, not the paper's log-volumes.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace LeanFormal.IUT

universe u v

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain
open MeasureTheory

namespace K1K2Realization

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## T4. Directedness / principal-filter characterization of `LogShellRayPresentation` -/

/-- **T4, necessity of directedness.**  Under a ray presentation the possible-image
family is directed for the inclusion order: any two images are contained in a third
image of the same family (in fact in one of the two).  This is Meitner's directedness
half of the proposed characterization, in the "upper bound in the family" form. -/
theorem logShellRayPresentation_directed
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h) (c c' : Choice) :
    ∃ k : Choice, Q.possibleImage c ≤ Q.possibleImage k ∧
      Q.possibleImage c' ≤ Q.possibleImage k := by
  rcases le_total (h c) (h c') with hle | hle
  · refine ⟨c, subset_rfl, fun x hx => ?_⟩
    rw [hpres c'] at hx
    rw [hpres c]
    exact ⟨hx.1, le_trans hle hx.2⟩
  · refine ⟨c', fun x hx => ?_, subset_rfl⟩
    rw [hpres c] at hx
    rw [hpres c']
    exact ⟨hx.1, le_trans hle hx.2⟩

/-- **T4, necessity of principal-filter compatibility.**  Under a ray presentation
every possible image is up-closed inside `L`: membership is preserved when moving up
inside `L`.  Singletons (and any non-up-closed image) therefore obstruct the ray
presentation, without needing a second image. -/
theorem logShellRayPresentation_image_upClosedIn
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h) (c : Choice) :
    ∀ x, x ∈ Q.possibleImage c → ∀ y, y ∈ L → x ≤ y → y ∈ Q.possibleImage c := by
  intro x hx y hyL hxy
  rw [hpres c] at hx
  rw [hpres c]
  exact ⟨hyL, le_trans hx.2 hxy⟩

/-- **T4, single-witness separation.**  If one image is a singleton `{v}` and `L`
contains a point `y` above `v` (with `y` not equal to `v`), then no ray presentation
exists.  Sharper than the two-singleton separation `not_logShellRayPresentation_of_two_singletonImages`
(which assumes two singleton images and no `L`-membership): here one image plus one
`L`-witness suffices. -/
theorem not_logShellRayPresentation_of_singletonImage_witness
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    {c : Choice} {v y : Real} (hc : Q.possibleImage c = {v})
    (hyL : y ∈ L) (hvy : v ≤ y) (hyv : y ≠ v) :
    ¬ (LogShellRayPresentation Q L h) := by
  intro hpres
  have hv : v ∈ L ∩ Set.Ici (h c) := by
    rw [← hpres c, hc]
    exact Set.mem_singleton v
  have hy : y ∈ L ∩ Set.Ici (h c) := ⟨hyL, le_trans hv.2 hvy⟩
  rw [← hpres c, hc] at hy
  exact hyv (Set.mem_singleton_iff.mp hy)

/-- **T4, general single-witness separation.**  Any image failing to be up-closed
inside `L` obstructs the ray presentation (contrapositive of the necessity lemma). -/
theorem not_logShellRayPresentation_of_not_upClosedIn
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    {c : Choice} {x y : Real} (hx : x ∈ Q.possibleImage c)
    (hyL : y ∈ L) (hxy : x ≤ y) (hy : y ∉ Q.possibleImage c) :
    ¬ (LogShellRayPresentation Q L h) :=
  fun hpres => hy (logShellRayPresentation_image_upClosedIn Q L h hpres c x hx y hyL hxy)

/-- **T4, ray-union collapse.**  A finite nonempty union of upper rays inside a set
is again a single upper ray: the union of the `Set.Ici t` over `t ∈ S` is
`Set.Ici (S.min' hS)`.  Hence "finite union of rays" adds nothing over a single ray. -/
theorem iUnion_Ici_eq_Ici_min' (S : Finset Real) (hS : S.Nonempty) :
    (⋃ t ∈ (S : Set Real), Set.Ici t) = Set.Ici (S.min' hS) := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_Ici] at hx ⊢
    obtain ⟨t, htS, htx⟩ := hx
    exact le_trans ((Finset.isLeast_min' S hS).2 htS) htx
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_Ici] at hx ⊢
    exact ⟨S.min' hS, by simpa using Finset.min'_mem S hS, hx⟩

/-- **T4, the finite-ray-union presentation candidate.**  Each possible image is
presented as `L` intersected with a finite union of upper rays, with a finite
(nonempty) height set per choice. -/
def FiniteRayUnionPresentation {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) (L : Set Real) : Prop :=
  ∃ S : Choice → Finset Real, (∀ c, (S c).Nonempty) ∧
    ∀ c, Q.possibleImage c = L ∩ ⋃ t ∈ (S c : Set Real), Set.Ici t

/-- **T4, the relaxation is vacuous.**  The finite-ray-union presentation exists if
and only if some height function gives an ordinary ray presentation: finite unions
of upper rays collapse to a single ray (previous lemma), and a single ray is the
one-element union.  So the "finite union of rays" alternative does not widen the
class of presentable families. -/
theorem finiteRayUnionPresentation_iff_exists_rayPresentation
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) :
    FiniteRayUnionPresentation Q L ↔
      ∃ h : Choice → Real, LogShellRayPresentation Q L h := by
  constructor
  · rintro ⟨S, hS, hpres⟩
    refine ⟨fun c => (S c).min' (hS c), fun c => ?_⟩
    rw [hpres c, iUnion_Ici_eq_Ici_min' (S c) (hS c)]
  · rintro ⟨h, hpres⟩
    refine ⟨fun c => {h c}, fun c => Finset.singleton_nonempty _, fun c => ?_⟩
    rw [hpres c]
    congr 1
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ici]
    constructor
    · intro hx
      exact ⟨h c, by simp, hx⟩
    · rintro ⟨t, ht, htx⟩
      have ht' : t = h c := by simpa [Finset.mem_singleton] using ht
      rwa [ht'] at htx

/-- **T4, transfer to the relaxation.**  Two strictly ordered singleton images kill
the finite-ray-union presentation as well (for every `L`), by the collapse
equivalence and the frozen two-singleton separation. -/
theorem not_finiteRayUnionPresentation_of_two_singletonImages
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) {c c' : Choice} {v v' : Real} (hvv' : v < v')
    (hc : Q.possibleImage c = {v}) (hc' : Q.possibleImage c' = {v'}) :
    ¬ (FiniteRayUnionPresentation Q L) := by
  rintro ⟨S, hS, hpres⟩
  obtain ⟨h, hh⟩ :=
    (finiteRayUnionPresentation_iff_exists_rayPresentation Q L).mp ⟨S, hS, hpres⟩
  exact not_logShellRayPresentation_of_two_singletonImages P Q L h hvv' hc hc' hh

/-- **T4, single-witness transfer to the relaxation.** -/
theorem not_finiteRayUnionPresentation_of_singletonImage_witness
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) {c : Choice} {v y : Real} (hc : Q.possibleImage c = {v})
    (hyL : y ∈ L) (hvy : v ≤ y) (hyv : y ≠ v) :
    ¬ (FiniteRayUnionPresentation Q L) := by
  rintro ⟨S, hS, hpres⟩
  obtain ⟨h, hh⟩ :=
    (finiteRayUnionPresentation_iff_exists_rayPresentation Q L).mp ⟨S, hS, hpres⟩
  exact not_logShellRayPresentation_of_singletonImage_witness Q L h hc hyL hvy hyv hh

/-! ### T4 toy: directed + up-closed does not imply ray-presentable

The two-member family `{Ioi 0, Ioi (-1)}` of open rays is directed and every member
is up-closed in `univ`, yet it has no ray-cut presentation: the height `0` is not
attained by `Ioi 0`, i.e. the missing ingredient is attainment of the principal
generator, not directedness.  This refutes the "if and only if" direction of the
proposed characterization as stated (directedness plus up-closure alone). -/

/-- The two-member open-ray family: `false ↦ Ioi 0`, `true ↦ Ioi (-1)`. -/
def openRayFamily (b : Bool) : Set Real :=
  if b then Set.Ioi (-1) else Set.Ioi (0 : Real)

theorem openRayFamily_subset_true (b : Bool) : openRayFamily b ≤ openRayFamily true := by
  intro x hx
  cases b
  · simp [openRayFamily] at hx ⊢
    linarith
  · simpa [openRayFamily] using hx

/-- The open-ray family is directed for the inclusion order. -/
theorem openRayFamily_directed (b b' : Bool) :
    ∃ k : Bool, openRayFamily b ≤ openRayFamily k ∧
      openRayFamily b' ≤ openRayFamily k :=
  ⟨true, openRayFamily_subset_true b, openRayFamily_subset_true b'⟩

/-- Every member of the open-ray family is up-closed in `univ`. -/
theorem openRayFamily_upClosed (b : Bool) :
    ∀ x, x ∈ openRayFamily b → ∀ y : Real, x ≤ y → y ∈ openRayFamily b := by
  intro x hx y hxy
  cases b
  · simp [openRayFamily] at hx ⊢
    linarith
  · simp [openRayFamily] at hx ⊢
    linarith

/-- The open-ray family has no presentation as a family of closed ray cuts:
`Ioi 0` is not of the form `Set.Ici t` for any `t`. -/
theorem not_openRayFamily_single_rayCut :
    ¬ (∃ t : Bool → Real, ∀ b, openRayFamily b = Set.Ici (t b)) := by
  rintro ⟨t, ht⟩
  have hpos : (0 : Real) < t false := by
    have h : t false ∈ openRayFamily false := by
      rw [ht false]
      exact Set.mem_Ici.mpr le_rfl
    simpa [openRayFamily] using h
  have hmem : t false / 2 ∈ openRayFamily false := by
    simp [openRayFamily]
    linarith
  rw [ht false] at hmem
  have hle : t false ≤ t false / 2 := hmem
  linarith

end K1K2Realization

namespace CovolumeGapToy

/-! ## T2. Box/covolume toy for the R9 lattice reading (candidate reading G1)

Reading: `hull = O_Kv-span` (a lattice, covolume = size of a fundamental domain)
and `image = union/edge box`; R9 becomes a covolume/exponent comparison.  In this
toy the hull is the axis box of side `N` (the fundamental domain of `N . Z^d`, of
covolume `N^d`) and the image is the overhanging edge box of side `N + epsilon`.
The gap `covolume(image) - covolume(hull)` is then `(N + epsilon)^d - N^d`, a
boundary-order term bounded by `d * (N + epsilon)^(d-1) * epsilon`, and it is `0`
in the span case (no overshoot, `epsilon = 0`).  Mapping these numbers to the
paper's log-volumes still depends on reading G1 (candidate/needs-verification). -/

/-- The axis box of side `N` in `Real^d`: the fundamental domain of the lattice
`N . Z^d` (covolume `N^d`), standing for the `O_Kv`-span hull in the toy reading. -/
def hullBox (d : Nat) (N : Real) : Set (Fin d → Real) :=
  Set.Icc (0 : Fin d → Real) fun _ => N

/-- The overhanging edge box of side `N + epsilon`: the "union/edge box" image in
the toy reading. -/
def edgeBox (d : Nat) (N eps : Real) : Set (Fin d → Real) :=
  Set.Icc (0 : Fin d → Real) fun _ => N + eps

theorem hullBox_volume_toReal (d : Nat) (N : Real) (hN : 0 ≤ N) :
    (volume (hullBox d N)).toReal = N ^ d := by
  have hvol : (volume (Set.Icc (0 : Fin d → Real) (fun _ => N))).toReal =
      ∏ _ : Fin d, N := by
    simpa using Real.volume_Icc_pi_toReal (a := (0 : Fin d → Real)) (b := fun _ => N)
      (h := fun _ => hN)
  rw [hullBox, hvol]
  simp [Finset.prod_const]

theorem edgeBox_volume_toReal (d : Nat) (N eps : Real) (hN : 0 ≤ N) (heps : 0 ≤ eps) :
    (volume (edgeBox d N eps)).toReal = (N + eps) ^ d := by
  have hvol : (volume (Set.Icc (0 : Fin d → Real) (fun _ => N + eps))).toReal =
      ∏ _ : Fin d, (N + eps) := by
    simpa using Real.volume_Icc_pi_toReal (a := (0 : Fin d → Real)) (b := fun _ => N + eps)
      (h := fun _ => add_nonneg hN heps)
  rw [edgeBox, hvol]
  simp [Finset.prod_const]

/-- The span case: the edge box without overshoot is the hull box itself. -/
theorem edgeBox_zero_eq_hullBox (d : Nat) (N : Real) : edgeBox d N 0 = hullBox d N := by
  unfold edgeBox hullBox
  congr 1
  ext i
  simp

/-- **T2 (a), exact gap formula.**  The covolume gap is exactly the binomial
difference `(N + eps)^d - N^d`. -/
theorem gap_eq (d : Nat) {N eps : Real} (hN : 0 ≤ N) (heps : 0 ≤ eps) :
    (volume (edgeBox d N eps)).toReal - (volume (hullBox d N)).toReal =
      (N + eps) ^ d - N ^ d := by
  rw [edgeBox_volume_toReal d N eps hN heps, hullBox_volume_toReal d N hN]

/-- Pure algebra: for `0 ≤ y ≤ x`, `x^d - y^d ≤ d * x^(d-1) * (x - y)`, the
mean-value form of the binomial expansion; this is Mathlib's `abs_pow_sub_pow_le`
(`Mathlib/Algebra/Order/Ring/Abs.lean`) specialised to the case `0 ≤ y ≤ x`. -/
theorem pow_sub_pow_le_mul {x y : Real} {d : Nat} (hd : 1 ≤ d) (hy : 0 ≤ y)
    (hyx : y ≤ x) :
    x ^ d - y ^ d ≤ (d : Real) * x ^ (d - 1) * (x - y) := by
  have hx : 0 ≤ x := le_trans hy hyx
  have hle : 0 ≤ x - y := sub_nonneg.mpr hyx
  have hpow : y ^ d ≤ x ^ d := pow_le_pow_left₀ hy hyx d
  have h := abs_pow_sub_pow_le (a := x) (b := y) (n := d)
  rw [abs_of_nonneg (sub_nonneg.mpr hpow), abs_of_nonneg hle, abs_of_nonneg hx,
    abs_of_nonneg hy, max_eq_left hyx] at h
  calc x ^ d - y ^ d ≤ (x - y) * (d : Real) * x ^ (d - 1) := h
    _ = (d : Real) * x ^ (d - 1) * (x - y) := by ring

/-- **T2 (a), boundary-order bound.**  The gap is a boundary-order term: it is at
most `d * (N + eps)^(d-1) * eps`, one power of `eps` above the bulk `N^d`. -/
theorem gap_le_overshoot_boundary (d : Nat) (hd : 1 ≤ d) {N eps : Real}
    (hN : 0 ≤ N) (heps : 0 ≤ eps) :
    (volume (edgeBox d N eps)).toReal - (volume (hullBox d N)).toReal <=
      d * (N + eps) ^ (d - 1) * eps := by
  rw [gap_eq d hN heps]
  have h := pow_sub_pow_le_mul (x := N + eps) (y := N) hd hN (le_add_of_nonneg_right heps)
  rwa [add_sub_cancel_left] at h

/-- **T2 (b), zero gap in the span case.**  With no overshoot the covolume gap
vanishes (the edge box is the hull box). -/
theorem gap_eq_zero_of_no_overshoot (d : Nat) {N : Real} (hN : 0 ≤ N) :
    (volume (edgeBox d N 0)).toReal - (volume (hullBox d N)).toReal = 0 := by
  rw [edgeBox_volume_toReal d N 0 hN (le_refl 0), hullBox_volume_toReal d N hN]
  simp

end CovolumeGapToy

namespace HullSignAudit

/-! ## T6. `toReal`-top gate, single-point dominator, and the `-|log|` sign table

Audit targets: (a) the `ENNReal.toReal` channel sends `top` to `0`, so a positive
`.toReal`-level lower bound certifies finiteness (gate below); (b) the certificate
premise `ofReal q ≤ logVolume imageSet` can be witnessed by a single dominating
point, so only a dominator search is needed; (c) the sign of `-|log q|` requires
case analysis over `q >= 1` / `q ≤ 1` (both one-step rewrites fail). -/

/-- **T6 (a), top gate.**  If a positive real `c` is bounded by `v.toReal`, then
`v` is not `top`; in particular the `.toReal` channel carries no silent zero for
certified positive lower bounds. -/
theorem toReal_positive_lower_bound_forces_ne_top {c : Real} {v : ENNReal}
    (hc : 0 < c) (h : c ≤ v.toReal) : v ≠ ⊤ := by
  intro hv
  rw [hv, ENNReal.toReal_top] at h
  linarith

/-- **T6 (b), single-point dominator.**  The certificate premise
`ofReal q ≤ logVolume imageSet` follows from a single dominating point
`x ∈ imageSet` with `ofReal q ≤ logVolume {x}`: the singleton is contained in the
image union, so monotonicity of `logVolume` closes the gap.  Signature allows the
single-witness route; only the dominator search remains. -/
theorem ofReal_le_logVolume_imageSet_of_singleton_dominator {X : Type u}
    (W : IQHullLogVolumeInterface X) {x : X} {q : Real}
    (hx : x ∈ W.imageSet) (h : ENNReal.ofReal q ≤ W.logVolume {x}) :
    ENNReal.ofReal q ≤ W.logVolume W.imageSet :=
  le_trans h (W.logVolume_mono (Set.singleton_subset_iff.mpr hx))

/-- The signed quantity of the ②-wall interface, read as `qSigned = -|log q|`. -/
noncomputable def signedLog (q : Real) : Real := -(|Real.log q|)

/-- `-|log q|` is always nonpositive (the leading minus survives the absolute
value, regardless of the side of `1`). -/
theorem signedLog_nonpos (q : Real) : signedLog q ≤ 0 := by
  rw [signedLog]
  exact neg_nonpos.mpr (abs_nonneg _)

/-- `-|log q|` vanishes exactly on `{0, 1, -1}` (Mathlib convention
`Real.log 0 = 0` and `Real.log (-1) = 0` included). -/
theorem signedLog_eq_zero_iff {q : Real} :
    signedLog q = 0 ↔ q = 0 ∨ q = 1 ∨ q = -1 := by
  rw [signedLog, neg_eq_zero, abs_eq_zero, Real.log_eq_zero]

/-- Double negation recovers the absolute value: `-(-|log q|) = |log q|`. -/
theorem neg_signedLog (q : Real) : -signedLog q = |Real.log q| := by
  simp [signedLog]

/-- Case `1 ≤ q`: `-|log q| = -log q`. -/
theorem signedLog_eq_neg_log_of_one_le {q : Real} (hq : 1 ≤ q) :
    signedLog q = -Real.log q := by
  rw [signedLog, abs_of_nonneg (Real.log_nonneg hq)]

/-- Case `0 < q ≤ 1`: `-|log q| = log q`. -/
theorem signedLog_eq_log_of_pos_of_le_one {q : Real} (h0 : 0 < q) (h1 : q ≤ 1) :
    signedLog q = Real.log q := by
  rw [signedLog, abs_of_nonpos (Real.log_nonpos h0.le h1), neg_neg]

/-- **T6 (c), no single rewrite (negative branch).**  `-|log q| = -log q` is not a
valid single rewrite: it fails at `q = 1/2`.  The `-|log|` sign requires case
analysis. -/
theorem not_forall_signedLog_eq_neg_log :
    ¬ (∀ q : Real, signedLog q = -Real.log q) := by
  intro h
  have hhalf : Real.log (1 / 2 : Real) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hcontra : Real.log (1 / 2 : Real) = 0 := by
    have := h (1 / 2)
    rw [signedLog, abs_of_neg (Real.log_neg (by norm_num) (by norm_num))] at this
    linarith
  exact hhalf hcontra

/-- **T6 (c), no single rewrite (positive branch).**  `-|log q| = log q` is not a
valid single rewrite either: it fails at `q = 2`. -/
theorem not_forall_signedLog_eq_log :
    ¬ (∀ q : Real, signedLog q = Real.log q) := by
  intro h
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := h 2
  rw [signedLog, abs_of_nonneg hpos.le] at this
  linarith

end HullSignAudit

end LeanFormal.IUT
