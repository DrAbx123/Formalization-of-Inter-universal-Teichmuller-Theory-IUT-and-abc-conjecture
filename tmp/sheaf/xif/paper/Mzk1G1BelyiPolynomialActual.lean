/- PORTED DONOR FILE (grace): TauCeti closure {RingTheory/AdjoinRoot/Minpoly, FieldTheory/Minpoly/BelyiReduction,
   Data/Rat/AbcTriple, Algebra/Polynomial/CriticalValues, Algebra/Polynomial/Belyi}.lean (TauCeti, Apache-2.0).
   Changes only: `namespace TauCeti` renamed to LeanFormal.IUT.XiFPaper.BelyiPolynomial; imports rewritten to
   Mathlib (all TauCeti dependency imports are inlined below); duplicate `universe` lines removed.
   No mathematical content change. Consumer: henry's B2 (polynomial Belyification / critical values). -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.FieldSimp

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module


/-!
# Minimal polynomials of classes in `AdjoinRoot`

For polynomials `f` and `g` over a field `K`, the class `AdjoinRoot.mk f g` is the value `g(α)` at
the root `α` of `f`. Its minimal polynomial over `K` is the polynomial whose roots are the images
under `g` of the roots of `f` when `f` is irreducible: it divides `p` exactly when
`f ∣ p.comp g`, which for squarefree `f` says that `g` maps the roots of `f` into the roots of
`p`. It is irreducible of degree at most `deg f`.

## Main results

* `AdjoinRoot.minpoly_mk_dvd_iff`: `minpoly K (mk f g) ∣ p ↔ f ∣ p.comp g`.
* `AdjoinRoot.natDegree_minpoly_mk_le`: for `f ≠ 0`, the minimal polynomial has degree at most
  `f.natDegree`.
* `AdjoinRoot.irreducible_minpoly_mk`: for `f` irreducible, the minimal polynomial is irreducible.
* `AdjoinRoot.minpoly_root_of_monic`: over any commutative ring, the minimal polynomial of the
  adjoined root of a monic `f` is `f`.
-/

public section

open Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K]

/-- The minimal polynomial of `g(α)`, for the root `α` of `f`, divides `p` exactly when
`f ∣ p.comp g`, that is, when `p(g(α)) = 0` in `AdjoinRoot f`. For squarefree `f` this says that
`g` maps the roots of `f` into the roots of `p`. -/
theorem minpoly_mk_dvd_iff {f g p : K[X]} : minpoly K (mk f g) ∣ p ↔ f ∣ p.comp g := by
  rw [minpoly.dvd_iff, ← aeval_eq, ← aeval_comp, aeval_eq, mk_eq_zero]

/-- `g` maps the roots of `f` into the roots of the minimal polynomial of `g(α)`. -/
theorem dvd_minpoly_mk_comp (f g : K[X]) : f ∣ (minpoly K (mk f g)).comp g :=
  minpoly_mk_dvd_iff.1 dvd_rfl

/-- The minimal polynomial of an element of `AdjoinRoot f` has degree at most that of `f`. -/
theorem natDegree_minpoly_mk_le {f : K[X]} (g : K[X]) (hf : f ≠ 0) :
    (minpoly K (mk f g)).natDegree ≤ f.natDegree :=
  have := (powerBasis hf).finite
  (minpoly.natDegree_le _).trans_eq ((powerBasis hf).finrank.trans (powerBasis_dim hf))

/-- For `f` irreducible, the minimal polynomial of an element of `AdjoinRoot f` is irreducible. -/
theorem irreducible_minpoly_mk {f : K[X]} (g : K[X]) (hf : Irreducible f) :
    Irreducible (minpoly K (mk f g)) := by
  have := Fact.mk hf
  have := (powerBasis hf.ne_zero).finite
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)

/-- Over any commutative ring, the minimal polynomial of the adjoined root of a monic polynomial
`f` is `f` itself: no nonzero polynomial of smaller degree vanishes at `root f`, because
`1, root f, …, root f ^ (deg f - 1)` is a basis. Over a field this is
`AdjoinRoot.minpoly_powerBasis_gen_of_monic`. -/
theorem minpoly_root_of_monic {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic) :
    minpoly R (root f) = f := by
  refine (minpoly.unique' R (root f) hf (aeval_eq f ▸ mk_self) fun q hq ↦
    or_iff_not_imp_left.2 fun hq0 hroot ↦ ?_).symm
  exact (hq.trans_le degree_le_natDegree).not_ge
    ((powerBasis' hf).dim_le_degree_of_root hq0 hroot)

end AdjoinRoot

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module


/-!
# Belyi's degree reduction

Let `F` be a perfect field, for instance `ℚ`. Every finite set `S` of elements algebraic over `F`
is carried into `F` by a polynomial `q ∈ F[X]` with nonzero derivative whose critical values,
the values of `q` at the roots of `q′` in any field extension, also lie in `F`. This is the first
half of Belyi's construction of a Belyi map on a curve over `AlgebraicClosure ℚ`. A polynomial
also fixes `∞`, so a finite subset of `ℙ¹(AlgebraicClosure ℚ)` is carried into `ℙ¹(ℚ)` together
with the critical values of `q`.

## Main results

* `TauCeti.exists_irreducible_finset_dvd_comp`: the degree-reduction step.
* `TauCeti.exists_forall_dvd_sub_C`: for a finite set `P` of irreducible polynomials, a
  polynomial `q` with `q′ ≠ 0` that is constant modulo every member of `P` and modulo every
  irreducible factor of `q′`.
* `TauCeti.exists_polynomial_aeval_mem_range`: the same statement for a finite set of algebraic
  elements of a field extension, with the critical values of `q` taken in an arbitrary field
  extension.

## Implementation notes

The set `S` is replaced by the finite set of minimal polynomials of its elements, which records
its closure under conjugation over `F`. A root of an irreducible `r ∈ F[X]` is mapped by a
polynomial `μ` into the root set of an irreducible `p'` exactly when `r ∣ p'.comp μ`, and `q`
takes a value `c ∈ F` at the roots of `r` exactly when `r ∣ q - C c`. All statements are made in
these terms over `F` and transferred to elements of field extensions at the end.

The degree-reduction step: if `μ` has the largest degree `d ≥ 2` among the polynomials in such a
set `P`, then `μ` maps the roots of `P`, together with the roots of `μ′`, into the roots of a
new finite set `P'` of irreducible polynomials of degree at most `d`, with strictly fewer of
degree exactly `d`. Indeed the roots of `μ` go to `0`, every root of any polynomial in `P` goes to
a point of no larger degree, and the roots of `μ′` have degree at most `d - 1` since `μ′ ≠ 0`
(here perfectness is used). The well-founded measure of the induction is therefore the pair
(largest degree `d`, number of members of degree `d`), ordered lexicographically. The
cardinality of the root set alone need not drop: `X ^ 2 - 2` sends `{√2, -√2}` to `{0}` and adds
its critical value `-2`.

## References

* G. V. Belyi, *On Galois extensions of a maximal cyclotomic field*, Math. USSR Izv. 14 (1980).
* B. Köck, *Belyi's theorem revisited*, Beiträge Algebra Geom. 45 (2004), Lemma 3.5.
-/

public section

open Polynomial UniqueFactorizationMonoid
open scoped Finset

namespace LeanFormal.IUT.XiFPaper.BelyiPolynomial

variable {F : Type*} [Field F]

/-- **The degree-reduction step.** Let `P` be a finite set of irreducible polynomials, and let
`μ ∈ P`, with `μ′ ≠ 0`, have the largest degree `d ≥ 2` in `P`. Then there is a finite set `P'`
of irreducible polynomials of degree at most `d`, with fewer members of degree `d` than `P`, such
that `μ` maps the roots of every member of `P`, and the roots of `μ′`, into the roots of members
of `P'`. Over a perfect field the hypothesis `μ′ ≠ 0` holds for every irreducible `μ`. -/
theorem exists_irreducible_finset_dvd_comp {P : Finset F[X]}
    (hP : ∀ p ∈ P, Irreducible p) {μ : F[X]} (hμ : μ ∈ P) (hμ' : derivative μ ≠ 0)
    (hdeg : ∀ p ∈ P, p.natDegree ≤ μ.natDegree) (hμ2 : 2 ≤ μ.natDegree) :
    ∃ P' : Finset F[X], (∀ p ∈ P', Irreducible p) ∧ (∀ p ∈ P', p.natDegree ≤ μ.natDegree) ∧
      #{p ∈ P' | p.natDegree = μ.natDegree} < #{p ∈ P | p.natDegree = μ.natDegree} ∧
      (∀ p ∈ P, ∃ p' ∈ P', p ∣ p'.comp μ) ∧
      ∀ r, Irreducible r → r ∣ derivative μ → ∃ p' ∈ P', r ∣ p'.comp μ := by
  classical
  -- The irreducible factors of `μ′` have degree less than `μ`.
  have hcrit : ∀ r ∈ normalizedFactors (derivative μ), r.natDegree < μ.natDegree := fun r hr ↦
    have := natDegree_derivative_le μ
    (natDegree_le_of_dvd (dvd_of_mem_normalizedFactors hr) hμ').trans_lt (by omega)
  set Q := P ∪ (normalizedFactors (derivative μ)).toFinset
  have hQ : ∀ r ∈ Q, Irreducible r := fun r hr ↦ (Finset.mem_union.1 hr).elim (hP r)
    fun h ↦ irreducible_of_normalized_factor r (Multiset.mem_toFinset.1 h)
  -- `P'` consists of the minimal polynomials of the images under `μ` of the roots of `Q`.
  refine ⟨Q.image fun r ↦ minpoly F (AdjoinRoot.mk r μ), ?_, ?_, ?_,
    fun p hp ↦ ⟨_, Finset.mem_image_of_mem _ (Finset.mem_union_left _ hp),
      AdjoinRoot.dvd_minpoly_mk_comp p μ⟩, fun r hr hdvd ↦ ?_⟩
  · simpa using fun r hr ↦ AdjoinRoot.irreducible_minpoly_mk μ (hQ r hr)
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine fun r hr ↦ (AdjoinRoot.natDegree_minpoly_mk_le μ (hQ r hr).ne_zero).trans ?_
    rcases Finset.mem_union.1 hr with hr | hr
    · exact hdeg r hr
    · exact (hcrit r (Multiset.mem_toFinset.1 hr)).le
  · -- A member of `P'` of degree `d` is the image of a member of `P` of degree `d` other than
    -- `μ`, whose image is `X`.
    refine (Finset.card_le_card (t := ({p ∈ P | p.natDegree = μ.natDegree}.erase μ).image
      fun r ↦ minpoly F (AdjoinRoot.mk r μ)) ?_).trans_lt (Finset.card_image_le.trans_lt
        (Finset.card_erase_lt_of_mem (by simp [hμ])))
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_image] at hp
    obtain ⟨⟨r, hrQ, rfl⟩, hdr⟩ := hp
    have hle := AdjoinRoot.natDegree_minpoly_mk_le μ (hQ r hrQ).ne_zero
    rcases Finset.mem_union.1 hrQ with hrP | hrC
    · refine Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2
        ⟨hrP, le_antisymm (hdeg r hrP) (hdr ▸ hle)⟩⟩)
      -- The roots of `μ` are mapped to `0`, whose minimal polynomial is `X`.
      rintro rfl
      have := Fact.mk (hP _ hrP)
      rw [AdjoinRoot.mk_self, minpoly.zero, natDegree_X] at hdr
      omega
    · have := hcrit r (Multiset.mem_toFinset.1 hrC)
      omega
  · obtain ⟨r₀, hr₀, hassoc⟩ := exists_mem_normalizedFactors_of_dvd hμ' hr hdvd
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Multiset.mem_toFinset.2 hr₀)),
      hassoc.dvd.trans (AdjoinRoot.dvd_minpoly_mk_comp r₀ μ)⟩

/-- If `μ` maps the roots of `P`, and the roots of `μ′`, into the roots of `P'`, and `q` is
constant modulo every member of `P'` and every irreducible factor of `q′`, then `q.comp μ` is
constant modulo every member of `P` and every irreducible factor of its derivative. -/
private theorem forall_dvd_sub_C_comp {P P' : Finset F[X]} {μ q : F[X]} (hμ' : derivative μ ≠ 0)
    (hPP' : ∀ p ∈ P, ∃ p' ∈ P', p ∣ p'.comp μ)
    (hcrit : ∀ r, Irreducible r → r ∣ derivative μ → ∃ p' ∈ P', r ∣ p'.comp μ)
    (hq' : derivative q ≠ 0) (hqP' : ∀ p ∈ P', ∃ c, p ∣ q - C c)
    (hqcrit : ∀ r, Irreducible r → r ∣ derivative q → ∃ c, r ∣ q - C c) :
    derivative (q.comp μ) ≠ 0 ∧ (∀ p ∈ P, ∃ c, p ∣ q.comp μ - C c) ∧
      ∀ r, Irreducible r → r ∣ derivative (q.comp μ) → ∃ c, r ∣ q.comp μ - C c := by
  -- If `μ` maps the roots of `p` into the roots of `p'`, and `q` takes the value `c` at the roots
  -- of `p'`, then `q.comp μ` takes the value `c` at the roots of `p`.
  have dvd_comp_sub_C {p p' : F[X]} {c : F} (hp : p ∣ p'.comp μ) (hp' : p' ∣ q - C c) :
      p ∣ q.comp μ - C c :=
    hp.trans (by simpa using map_dvd (compRingHom μ) hp')
  refine ⟨?_, fun p hp ↦ ?_, fun r hr hdvd ↦ ?_⟩
  · rw [derivative_comp]
    refine mul_ne_zero hμ' fun h ↦ ?_
    rcases comp_eq_zero_iff.1 h with h | ⟨-, h⟩
    · exact hq' h
    · exact hμ' (by rw [h, derivative_C])
  · obtain ⟨p', hp', hpp'⟩ := hPP' p hp
    obtain ⟨c, hc⟩ := hqP' p' hp'
    exact ⟨c, dvd_comp_sub_C hpp' hc⟩
  rw [derivative_comp] at hdvd
  rcases hr.prime.dvd_or_dvd hdvd with h | h
  · -- A root of `μ′` is mapped into the roots of a member of `P'`.
    obtain ⟨p', hp', hrp'⟩ := hcrit r hr h
    obtain ⟨c, hc⟩ := hqP' p' hp'
    exact ⟨c, dvd_comp_sub_C hrp' hc⟩
  · -- A root of `q′ ∘ μ` is mapped by `μ` to a root of `q′`.
    obtain ⟨c, hc⟩ := hqcrit _ (AdjoinRoot.irreducible_minpoly_mk μ hr)
      (AdjoinRoot.minpoly_mk_dvd_iff.2 h)
    exact ⟨c, dvd_comp_sub_C (AdjoinRoot.dvd_minpoly_mk_comp r μ) hc⟩

/-- The polynomial `X` has nonzero derivative and is constant modulo every irreducible
polynomial of degree one. -/
private theorem forall_dvd_sub_C_X {P : Finset F[X]} (hP : ∀ p ∈ P, Irreducible p)
    (hdeg : ∀ p ∈ P, p.natDegree ≤ 1) :
    derivative (X : F[X]) ≠ 0 ∧ (∀ p ∈ P, ∃ c, p ∣ X - C c) ∧
      ∀ r, Irreducible r → r ∣ derivative (X : F[X]) → ∃ c, r ∣ X - C c := by
  refine ⟨by simp, fun p hp ↦ ?_, fun r hr hdvd ↦
    absurd (isUnit_of_dvd_one (derivative_X (R := F) ▸ hdvd)) hr.not_isUnit⟩
  have hp1 : p.degree = 1 := (degree_eq_iff_natDegree_eq (hP p hp).ne_zero).2
    (le_antisymm (hdeg p hp) (hP p hp).natDegree_pos)
  obtain ⟨c, hc⟩ := exists_root_of_degree_eq_one hp1
  exact ⟨c, ((irreducible_X_sub_C c).associated_of_dvd (hP p hp) (dvd_iff_isRoot.2 hc)).symm.dvd⟩

/-- **Belyi's degree reduction over `F`.** For a finite set `P` of irreducible polynomials over a
perfect field `F`, there is a polynomial `q ∈ F[X]` with `q′ ≠ 0` that is constant modulo every
member of `P` and modulo every irreducible factor of `q′`: at the roots of each of these, in any
field extension, `q` takes a value in `F`. -/
theorem exists_forall_dvd_sub_C [PerfectField F] {P : Finset F[X]}
    (hP : ∀ p ∈ P, Irreducible p) :
    ∃ q : F[X], derivative q ≠ 0 ∧ (∀ p ∈ P, ∃ c, p ∣ q - C c) ∧
      ∀ r, Irreducible r → r ∣ derivative q → ∃ c, r ∣ q - C c := by
  classical
  -- Induction on the largest degree `d` in `P`, then on the number of members of degree `d`.
  suffices h : ∀ (d n : ℕ) (P : Finset F[X]), (∀ p ∈ P, Irreducible p) →
      (∀ p ∈ P, p.natDegree ≤ d) → #{p ∈ P | p.natDegree = d} ≤ n →
      ∃ q : F[X], derivative q ≠ 0 ∧ (∀ p ∈ P, ∃ c, p ∣ q - C c) ∧
        ∀ r, Irreducible r → r ∣ derivative q → ∃ c, r ∣ q - C c from
    h _ _ P hP (fun p hp ↦ Finset.le_sup (f := natDegree) hp) le_rfl
  intro d
  induction d with
  | zero =>
    exact fun _ P hP hd _ ↦ ⟨X, forall_dvd_sub_C_X hP fun p hp ↦ (hd p hp).trans zero_le_one⟩
  | succ d ihd =>
    intro n
    induction n with
    | zero =>
      -- No member has degree `d + 1`, so all have degree at most `d`.
      intro P hP hd hn
      refine ihd _ P hP (fun p hp ↦ Nat.le_of_lt_succ (lt_of_le_of_ne (hd p hp) fun h ↦ ?_))
        le_rfl
      rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hn
      exact hn hp h
    | succ n ihn =>
      intro P hP hd hn
      by_cases hd1 : d + 1 ≤ 1
      · exact ⟨X, forall_dvd_sub_C_X hP fun p hp ↦ (hd p hp).trans hd1⟩
      by_cases hex : ∃ μ ∈ P, μ.natDegree = d + 1
      · -- Apply the degree-reduction step to a member `μ` of degree `d + 1`, and compose.
        obtain ⟨μ, hμ, hμd⟩ := hex
        have hμ' : derivative μ ≠ 0 := (separable_iff_derivative_ne_zero (hP μ hμ)).1
          (PerfectField.separable_of_irreducible (hP μ hμ))
        obtain ⟨P', hP', hd', hlt, hPP', hcrit⟩ :=
          exists_irreducible_finset_dvd_comp hP hμ hμ' (hμd ▸ hd) (by omega)
        rw [hμd] at hd' hlt
        obtain ⟨q, hq', hqP', hqcrit⟩ := ihn P' hP' hd' (by omega)
        exact ⟨q.comp μ, forall_dvd_sub_C_comp hμ' hPP' hcrit hq' hqP' hqcrit⟩
      · push Not at hex
        exact ihd _ P hP (fun p hp ↦ Nat.le_of_lt_succ (lt_of_le_of_ne (hd p hp) (hex p hp)))
          le_rfl

universe w

/-- **Belyi's degree reduction.** Every finite set `S` of elements algebraic over a perfect field
`F`, such as a finite subset of `AlgebraicClosure ℚ`, is carried into `F` by a polynomial
`q ∈ F[X]` with `q′ ≠ 0`, in particular nonconstant, whose critical values in every field
extension of `F` also lie in `F`. -/
theorem exists_polynomial_aeval_mem_range [PerfectField F] {K : Type*} [Field K] [Algebra F K]
    {S : Finset K} (hS : ∀ s ∈ S, IsIntegral F s) :
    ∃ q : F[X], derivative q ≠ 0 ∧ (∀ s ∈ S, aeval s q ∈ Set.range (algebraMap F K)) ∧
      ∀ (L : Type w) [Field L] [Algebra F L] (x : L), aeval x (derivative q) = 0 →
        aeval x q ∈ Set.range (algebraMap F L) := by
  classical
  obtain ⟨q, hq', hqS, hqcrit⟩ := exists_forall_dvd_sub_C (P := S.image (minpoly F))
    (by simpa using fun s hs ↦ minpoly.irreducible (hS s hs))
  refine ⟨q, hq', fun s hs ↦ ?_, fun L _ _ x hx ↦ ?_⟩
  · obtain ⟨c, hc⟩ := hqS _ (Finset.mem_image_of_mem _ hs)
    exact ⟨c, by rw [eq_comm, ← sub_eq_zero]; simpa using minpoly.dvd_iff.1 hc⟩
  · have hint : IsIntegral F x := (IsAlgebraic.isIntegral ⟨_, hq', hx⟩)
    obtain ⟨c, hc⟩ := hqcrit _ (minpoly.irreducible hint) (minpoly.dvd F x hx)
    exact ⟨c, by rw [eq_comm, ← sub_eq_zero]; simpa using minpoly.dvd_iff.1 hc⟩

end LeanFormal.IUT.XiFPaper.BelyiPolynomial

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module


/-!
# The abc triple of a rational number

Writing a rational `q` in lowest terms as `a / c` with `a = q.num` and `c = q.den`, and setting
`b = c - a`, gives integers with `a + b = c`, pairwise coprime since `a` and `c` are
(`Rat.isCoprime_num_den`). This is how an abc triple is read off a rational number, as for the
`j`-invariant of an elliptic curve over `ℚ` divided by `1728`. The three integers are nonzero
exactly when `q ≠ 0` and `q ≠ 1`: `a = 0` means `q = 0` (`Rat.num_ne_zero`), `c` is a
denominator, and `b = 0` means `q = 1`. For `0 < q < 1` all three are positive, so `q` has the
form `m / (m + n)` for positive natural numbers `m` and `n`.

## Main results

* `Rat.den_sub_num_ne_zero`: `q.den - q.num ≠ 0` if and only if `q ≠ 1`.
* `Rat.exists_eq_div_add_of_pos_of_lt_one`: a rational strictly between `0` and `1` is
  `m / (m + n)` for positive natural numbers `m` and `n`.
-/

public section

namespace Rat

/-- The middle term `q.den - q.num` of the abc triple of `q` is nonzero if and only if `q ≠ 1`. -/
@[simp]
theorem den_sub_num_ne_zero (q : ℚ) : (q.den : ℤ) - q.num ≠ 0 ↔ q ≠ 1 := by
  refine sub_ne_zero.trans (not_congr ⟨fun h => ?_, fun h => by simp [h]⟩)
  rw [← q.num_div_den, ← h, Int.cast_natCast, div_self (Nat.cast_ne_zero.mpr q.den_ne_zero)]

/-- A rational number strictly between `0` and `1` has the form `m / (m + n)` for positive
natural numbers `m` and `n`, namely `m = q.num` and `n = q.den - q.num`. -/
theorem exists_eq_div_add_of_pos_of_lt_one {q : ℚ} (h0 : 0 < q) (h1 : q < 1) :
    ∃ m n : ℕ, m ≠ 0 ∧ n ≠ 0 ∧ q = (m : ℚ) / (m + n) := by
  have hnum : 0 < q.num := Rat.num_pos.mpr h0
  have hden : q.num < q.den := Rat.num_lt_denom_iff.mpr h1
  refine ⟨q.num.toNat, q.den - q.num.toNat, by omega, by omega, ?_⟩
  have hle : q.num.toNat ≤ q.den := by omega
  rw [← Nat.cast_add, Nat.add_sub_cancel' hle]
  have : ((q.num.toNat : ℕ) : ℚ) = q.num := by exact_mod_cast Int.toNat_of_nonneg hnum.le
  rw [this, Rat.num_div_den]

end Rat

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module


/-!
# Critical values of polynomials

The critical values of a polynomial `p` with coefficients in `R`, computed in an `R`-algebra
`S` that is a domain, are the values `p(x)` at the roots `x ∈ S` of the derivative `p′`. Over
an algebraically closed field of characteristic zero they are the finite branch values of the
map `x ↦ p(x)` of the projective line; the point at infinity, over which a polynomial of degree
at least two is always ramified, is not part of this set.

Following Mathlib's `Polynomial.rootSet`, the roots of the zero polynomial form the empty set,
so a polynomial with vanishing derivative has no critical values.

The chain rule `(p ∘ q)′ = (p′ ∘ q) · q′` gives the bookkeeping for composites used in Belyi's
construction: the critical values of `p ∘ q` lie in the image under `p` of the critical values
of `q` together with the critical values of `p`, with equality over an algebraically closed
field of characteristic zero when `p` and `q` are nonconstant.

## Main declarations

* `Polynomial.criticalValues`: the critical values of `p` in `S`.
* `Polynomial.mem_criticalValues_self_iff`: membership in the critical values of a polynomial
  over a domain, computed in the domain itself, via roots of `p′`.
* `Polynomial.criticalValues_comp_subset`: the critical values of a composite.
* `Polynomial.criticalValues_comp`: equality for nonconstant polynomials over a field of
  characteristic zero, computed in an algebraically closed field.
* `Polynomial.algebraMap_mem_criticalValues_of_isAlgClosed`: a critical value lying in the
  coefficient field, attained in some field extension, is attained in every algebraically closed
  one.

## References

* Joseph H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in
  Mathematics 106, Springer, 2009, Exercise 1.12 and its hint.
* Bernhard Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004),
  253–265, §3.
-/

public section

open scoped Polynomial

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]

variable (S) in
/-- The critical values of `p` in `S`: the values of `p` at the roots of its derivative in `S`.
When `S` is an algebraically closed field of characteristic zero, these are the finite branch
values of `p` regarded as a self-map of the projective line. -/
noncomputable def criticalValues (p : R[X]) : Set S :=
  (fun x ↦ aeval x p) '' (derivative p).rootSet S

variable (S) in
/-- The critical values of `p` are the image of the roots of `p′` under `x ↦ p(x)`. -/
theorem criticalValues_def (p : R[X]) :
    p.criticalValues S = (fun x ↦ aeval x p) '' (derivative p).rootSet S :=
  (rfl)

@[simp]
theorem mem_criticalValues {p : R[X]} {y : S} :
    y ∈ p.criticalValues S ↔ ∃ x ∈ (derivative p).rootSet S, aeval x p = y :=
  Iff.rfl

/-- For a polynomial over a domain with nonzero derivative, its critical values in the domain
itself are the values `p(x)` at the roots `x` of `p′`. -/
theorem mem_criticalValues_self_iff {p : S[X]} (hp : derivative p ≠ 0) {y : S} :
    y ∈ p.criticalValues S ↔ ∃ x, (derivative p).IsRoot x ∧ p.eval x = y := by
  simp [mem_rootSet_of_ne hp]

theorem aeval_mem_criticalValues {p : R[X]} {x : S} (hx : x ∈ (derivative p).rootSet S) :
    aeval x p ∈ p.criticalValues S :=
  Set.mem_image_of_mem _ hx

theorem criticalValues_finite (p : R[X]) : (p.criticalValues S).Finite :=
  ((derivative p).rootSet_finite S).image _

/-- A polynomial of degree at most one has no critical values. -/
theorem criticalValues_eq_empty_of_natDegree_le_one {p : R[X]} (hp : p.natDegree ≤ 1) :
    p.criticalValues S = ∅ := by
  rw [criticalValues, eq_C_of_natDegree_le_zero
    ((natDegree_derivative_le p).trans (Nat.sub_le_of_le_add hp)), rootSet_C, Set.image_empty]

@[simp]
theorem criticalValues_C (a : R) : (C a).criticalValues S = ∅ :=
  criticalValues_eq_empty_of_natDegree_le_one (by rw [natDegree_C]; exact zero_le_one)

@[simp]
theorem criticalValues_X : (X : R[X]).criticalValues S = ∅ :=
  criticalValues_eq_empty_of_natDegree_le_one natDegree_X_le

variable (S) in
/-- Critical values are unchanged by first extending the coefficients along a scalar tower. -/
@[simp]
theorem criticalValues_map {T : Type*} [CommRing T] [Algebra R T] [Algebra T S]
    [IsScalarTower R T S] (p : R[X]) :
    (p.map (algebraMap R T)).criticalValues S = p.criticalValues S := by
  simp [criticalValues, derivative_map, aeval_map_algebraMap]

/-- The critical values of `p ∘ q` lie in the image under `p` of the critical values of `q`,
together with the critical values of `p`. -/
theorem criticalValues_comp_subset (p q : R[X]) :
    (p.comp q).criticalValues S ⊆ (fun y ↦ aeval y p) '' q.criticalValues S ∪
      p.criticalValues S := by
  rintro _ ⟨x, hx, rfl⟩
  rw [derivative_comp, mem_rootSet', Polynomial.map_mul, map_mul, aeval_comp] at hx
  obtain ⟨hne, hx⟩ := hx
  rcases mul_eq_zero.mp hx with h | h
  · refine Or.inl ⟨aeval x q, aeval_mem_criticalValues ?_, (aeval_comp x).symm⟩
    exact mem_rootSet'.mpr ⟨left_ne_zero_of_mul hne, h⟩
  · simp only [aeval_comp]
    refine Or.inr (aeval_mem_criticalValues (mem_rootSet'.mpr ⟨fun h' ↦ ?_, h⟩))
    exact right_ne_zero_of_mul hne (by rw [map_comp, h', zero_comp])

/-- Over a field of characteristic zero, computed in an algebraically closed field, the critical
values of a composite of nonconstant polynomials are the image under `p` of the critical values
of `q`, together with the critical values of `p`. -/
theorem criticalValues_comp {K L : Type*} [Field K] [CharZero K] [Field L] [IsAlgClosed L]
    [Algebra K L] {p q : K[X]} (hp : 0 < p.natDegree) (hq : 0 < q.natDegree) :
    (p.comp q).criticalValues L = (fun y ↦ aeval y p) '' q.criticalValues L ∪
      p.criticalValues L := by
  refine (criticalValues_comp_subset p q).antisymm ?_
  have hp' : derivative p ≠ 0 := derivative_ne_zero.mpr hp.ne'
  have hq' : derivative q ≠ 0 := derivative_ne_zero.mpr hq.ne'
  have hpq : derivative (p.comp q) ≠ 0 := by
    rw [derivative_comp]
    refine mul_ne_zero hq' fun h ↦ ?_
    rcases comp_eq_zero_iff.mp h with h | ⟨-, h⟩
    · exact hp' h
    · rw [h, natDegree_C] at hq
      exact hq.false
  -- A root `x` of either factor of `(p′ ∘ q) · q′` is a root of `(p ∘ q)′`.
  have key : ∀ x : L, aeval x (derivative q) * aeval (aeval x q) (derivative p) = 0 →
      aeval (aeval x q) p ∈ (p.comp q).criticalValues L := fun x hx ↦ by
    rw [← aeval_comp]
    refine aeval_mem_criticalValues ((mem_rootSet_of_ne hpq).mpr ?_)
    rwa [derivative_comp, map_mul, aeval_comp]
  rintro _ (⟨_, ⟨x, hx, rfl⟩, rfl⟩ | ⟨y, hy, rfl⟩)
  · exact key x (by rw [aeval_eq_zero_of_mem_rootSet hx, zero_mul])
  · -- Every value of `q` is attained over the algebraically closed field `L`.
    obtain ⟨x, hx⟩ := IsAlgClosed.eval_surjective (p := q.map (algebraMap K L))
      (by rw [natDegree_map]; exact hq.ne') y
    have hxy : aeval x q = y := by rwa [← eval_map_algebraMap]
    rw [← hxy]
    exact key x (by rw [hxy, aeval_eq_zero_of_mem_rootSet hy, mul_zero])

/-- A critical value of `p ∈ K[X]` that lies in `K` and is attained at a critical point in some
field extension `L` of `K` is also a critical value of `p` in every algebraically closed field
extension `Ω` of `K`. -/
theorem algebraMap_mem_criticalValues_of_isAlgClosed {K L Ω : Type*} [Field K] [Field L]
    [Field Ω] [IsAlgClosed Ω] [Algebra K L] [Algebra K Ω] {p : K[X]} {c : K}
    (h : algebraMap K L c ∈ p.criticalValues L) : algebraMap K Ω c ∈ p.criticalValues Ω := by
  obtain ⟨x, hx, hxc⟩ := mem_criticalValues.mp h
  have hp' : derivative p ≠ 0 := ne_zero_of_mem_rootSet hx
  have hx' := aeval_eq_zero_of_mem_rootSet hx
  have hint : IsIntegral K x := IsAlgebraic.isIntegral ⟨_, hp', hx'⟩
  -- A root `ξ ∈ Ω` of the minimal polynomial of the critical point `x` is a common root of `p′`
  -- and of `p - c`, as `x` is.
  obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective Ω (algebraMap K Ω).injective
    (minpoly K x) (minpoly.degree_pos hint).ne'
  have aeval_eq_zero {q : K[X]} (hq : aeval x q = 0) : aeval ξ q = 0 := by
    obtain ⟨r, hr⟩ := minpoly.dvd K x hq
    rw [hr, map_mul, hξ, zero_mul]
  refine ⟨ξ, (mem_rootSet_of_ne hp').mpr (aeval_eq_zero hx'), ?_⟩
  simpa [sub_eq_zero] using aeval_eq_zero (q := p - C c) (by simp [hxc])

end Polynomial

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module


/-!
# Belyi polynomials and the three-point step of Belyi's theorem

For natural numbers `m` and `n`, the Belyi polynomial

  `B_{m,n} = ((m + n) ^ (m + n) / (m ^ m * n ^ n)) * X ^ m * (1 - X) ^ n`

sends `0` and `1` to `0` (for `m` and `n` positive) and `m / (m + n)` to `1`, and its
derivative is a multiple of `X ^ (m - 1) * (1 - X) ^ (n - 1) * (m - (m + n) * X)`. So its
critical points lie in `{0, 1, m / (m + n)}` and its critical values lie in `{0, 1}`. The
containment of critical points is strict when `m = 1` or `n = 1`: `B_{1,1} = 4 X (1 - X)` has
the single critical point `1 / 2`.

Composing an affine normalization over `ℚ` with a Belyi polynomial sends three chosen rational
points into `{0, 1}` without creating critical values outside `{0, 1}`. Inducting on the size of
the set gives polynomial Belyification over `ℚ`: every finite set of rational numbers is carried
into `{0, 1}` by a nonconstant polynomial with rational coefficients whose critical values, in
every field of characteristic zero, lie in `{0, 1}`. Being a polynomial, it also fixes `∞`.

Preceding it by Belyi's degree reduction (`TauCeti.exists_polynomial_aeval_mem_range`), which
carries a finite set of algebraic numbers into `ℚ` by a polynomial over `ℚ` with rational
critical values, gives polynomial Belyification of algebraic numbers: every finite set of
elements algebraic over `ℚ`, such as a finite subset of `AlgebraicClosure ℚ`, is carried into
`{0, 1}` by a nonconstant polynomial over `ℚ` with all its critical values in `{0, 1}`. In terms
of the projective line, every finite `S ⊆ ℙ¹(AlgebraicClosure ℚ)` containing `∞` is sent into
`{0, 1, ∞}` by a polynomial `q ∈ ℚ[X]`, with `q⁻¹(∞) = {∞}` and every branch value of `q` in
`{0, 1, ∞}`.

## Main declarations

* `TauCeti.belyiPolynomial`: the Belyi polynomial `B_{m,n}` over a field; `B_{1,1}` is
  `4 X (1 - X)` (`TauCeti.belyiPolynomial_one_one`).
* `TauCeti.X_mul_one_sub_X_mul_derivative_belyiPolynomial`: the derivative of `B_{m,n}`,
  multiplied by `X (1 - X)`.
* `TauCeti.rootSet_derivative_belyiPolynomial_subset`: the critical points of `B_{m,n}` lie in
  `{0, 1, m / (m + n)}`.
* `TauCeti.criticalValues_belyiPolynomial_subset`: the critical values of `B_{m,n}` lie in
  `{0, 1}`.
* `TauCeti.exists_polynomial_eval_mem_criticalValues_subset`: polynomial Belyification of a
  finite set of rational numbers.
* `TauCeti.exists_polynomial_aeval_mem_criticalValues_subset`: polynomial Belyification of a
  finite set of algebraic numbers.

## References

* G. V. Belyi, *On Galois extensions of a maximal cyclotomic field*, Izv. Akad. Nauk SSSR
  Ser. Mat. 43 (1979), 267–276.
* Bernhard Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004),
  253–265, Lemmas 3.5 and 3.6.
* Ernesto Girondo and Gabino González-Diez, *Introduction to Compact Riemann Surfaces and
  Dessins d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University
  Press, 2012, §3.1.
-/

public section

open Polynomial

namespace LeanFormal.IUT.XiFPaper.BelyiPolynomial

universe u

section Field

variable (K : Type*) [Field K]

/-- The Belyi polynomial `B_{m,n} = ((m + n) ^ (m + n) / (m ^ m * n ^ n)) * X ^ m * (1 - X) ^ n`.
In characteristic zero its normalizing constant makes its value at `m / (m + n)` equal to `1`
(`TauCeti.eval_div_belyiPolynomial`). -/
noncomputable def belyiPolynomial (m n : ℕ) : K[X] :=
  C (((m : K) + n) ^ (m + n) / ((m : K) ^ m * (n : K) ^ n)) * X ^ m * (1 - X) ^ n

variable {K}

/-- The Belyi polynomial is preserved by every ring homomorphism of fields. -/
@[simp]
theorem map_belyiPolynomial {L : Type*} [Field L] (f : K →+* L) (m n : ℕ) :
    (belyiPolynomial K m n).map f = belyiPolynomial L m n := by
  simp [belyiPolynomial, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub]

/-- The Belyi polynomial `B_{1,1}` is `4 X (1 - X)`. -/
theorem belyiPolynomial_one_one : belyiPolynomial K 1 1 = C 4 * X * (1 - X) := by
  norm_num [belyiPolynomial]

/-- The value of the Belyi polynomial at a point `x`. -/
theorem eval_belyiPolynomial (m n : ℕ) (x : K) :
    (belyiPolynomial K m n).eval x =
      ((m : K) + n) ^ (m + n) / ((m : K) ^ m * (n : K) ^ n) * x ^ m * (1 - x) ^ n := by
  simp [belyiPolynomial]

/-- For `m ≠ 0`, the Belyi polynomial vanishes at `0`. -/
@[simp]
theorem eval_zero_belyiPolynomial {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    (belyiPolynomial K m n).eval 0 = 0 := by
  simp [eval_belyiPolynomial, hm]

/-- For `n ≠ 0`, the Belyi polynomial vanishes at `1`. -/
@[simp]
theorem eval_one_belyiPolynomial (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (belyiPolynomial K m n).eval 1 = 0 := by
  simp [eval_belyiPolynomial, hn]

/-- The derivative of the Belyi polynomial: `X (1 - X) B′_{m,n} = B_{m,n} (m - (m + n) X)`.
Multiplying by `X (1 - X)` avoids the exponents `m - 1` and `n - 1`. -/
theorem X_mul_one_sub_X_mul_derivative_belyiPolynomial (m n : ℕ) :
    X * (1 - X) * derivative (belyiPolynomial K m n) =
      belyiPolynomial K m n * (C (m : K) - C ((m : K) + n) * X) := by
  rw [belyiPolynomial]
  generalize ((m : K) + n) ^ (m + n) / ((m : K) ^ m * (n : K) ^ n) = c
  -- Split off `m = 0` and `n = 0` so that the exponents `m - 1` and `n - 1` simplify.
  rcases m with _ | m <;> rcases n with _ | n <;>
    simp only [derivative_mul, derivative_pow, derivative_C, derivative_sub, derivative_one,
      derivative_X, Nat.add_sub_cancel, map_add, map_natCast] <;> ring

variable [CharZero K]

/-- In characteristic zero, the normalizing constant `(m + n) ^ (m + n) / (m ^ m * n ^ n)` of the
Belyi polynomial is nonzero. -/
theorem belyiConstant_ne_zero (m n : ℕ) :
    ((m : K) + n) ^ (m + n) / ((m : K) ^ m * (n : K) ^ n) ≠ 0 := by
  -- `a ^ a` is nonzero for every natural number `a`, including `0 ^ 0 = 1`.
  refine div_ne_zero ?_ (mul_ne_zero ?_ ?_) <;> exact_mod_cast Nat.pow_self_pos.ne'

/-- In characteristic zero, the Belyi polynomial takes the value `1` at `m / (m + n)`. -/
@[simp]
theorem eval_div_belyiPolynomial (m n : ℕ) :
    (belyiPolynomial K m n).eval ((m : K) / (m + n)) = 1 := by
  rcases eq_or_ne (m + n) 0 with h | h
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp h
    simp [eval_belyiPolynomial]
  have hmn : (m : K) + n ≠ 0 := by exact_mod_cast h
  have hsub : 1 - (m : K) / (m + n) = n / (m + n) := by
    field_simp
    ring
  have hc := belyiConstant_ne_zero (K := K) m n
  rw [div_ne_zero_iff, mul_ne_zero_iff] at hc
  obtain ⟨-, hm, hn⟩ := hc
  rw [eval_belyiPolynomial, hsub, div_pow, div_pow, pow_add]
  field_simp

/-- In characteristic zero, the Belyi polynomial `B_{m,n}` has degree `m + n`. -/
@[simp]
theorem natDegree_belyiPolynomial (m n : ℕ) : (belyiPolynomial K m n).natDegree = m + n := by
  have hc := belyiConstant_ne_zero (K := K) m n
  have h1 : (1 - X : K[X]).natDegree = 1 := by
    rw [← neg_sub, natDegree_neg, ← C_1, natDegree_X_sub_C]
  rw [belyiPolynomial, mul_assoc, natDegree_C_mul hc, natDegree_mul (pow_ne_zero _ X_ne_zero)
    (pow_ne_zero _ (fun h ↦ by simp [h] at h1)), natDegree_X_pow, natDegree_pow, h1, mul_one]

/-- The critical points of the Belyi polynomial lie in `{0, 1, m / (m + n)}`. The containment is
strict when `m = 1` or `n = 1`. -/
theorem rootSet_derivative_belyiPolynomial_subset (L : Type*) [Field L] [Algebra K L]
    (m n : ℕ) :
    (derivative (belyiPolynomial K m n)).rootSet L ⊆ {0, 1, (m : L) / (m + n)} := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  intro x hx
  rw [← rootSet_map L (T := L), ← derivative_map, map_belyiPolynomial, mem_rootSet] at hx
  obtain ⟨hne, hx⟩ := hx
  rw [coe_aeval_eq_eval] at hx
  -- Evaluate `X (1 - X) B′ = B (m - (m + n) X)` at the critical point `x`.
  have key := congr_arg (eval x) (X_mul_one_sub_X_mul_derivative_belyiPolynomial (K := L) m n)
  simp only [eval_mul, eval_sub, eval_X, eval_one, eval_C, hx, mul_zero] at key
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_contra! h
  obtain ⟨h0, h1, hr⟩ := h
  rcases mul_eq_zero.mp key.symm with h | h
  · rw [eval_belyiPolynomial] at h
    exact mul_ne_zero (mul_ne_zero (belyiConstant_ne_zero m n) (pow_ne_zero _ h0))
      (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm h1))) h
  rcases eq_or_ne ((m : L) + n) 0 with hmn | hmn
  · obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := Nat.add_eq_zero_iff.mp (by exact_mod_cast hmn)
    simp [belyiPolynomial] at hne
  exact hr (by field_simp; linear_combination -h)

/-- The critical values of the Belyi polynomial lie in `{0, 1}`. -/
theorem criticalValues_belyiPolynomial_subset (L : Type*) [Field L] [Algebra K L] (m n : ℕ) :
    (belyiPolynomial K m n).criticalValues L ⊆ {0, 1} := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_criticalValues.mp hy
  rw [← eval_map_algebraMap, map_belyiPolynomial, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases rootSet_derivative_belyiPolynomial_subset L m n hx with rfl | rfl | rfl
  · rcases eq_or_ne m 0 with rfl | hm
    · simpa using Or.inr (eval_div_belyiPolynomial (K := L) 0 n)
    · exact Or.inl (eval_zero_belyiPolynomial hm n)
  · rcases eq_or_ne n 0 with rfl | hn
    · simp [eval_belyiPolynomial]
    · exact Or.inl (eval_one_belyiPolynomial m hn)
  · exact Or.inr (eval_div_belyiPolynomial m n)

end Field

section Rat

/-- If `p` and `q` over `ℚ` have their critical values in `{0, 1}`, in every field of
characteristic zero, and `p` sends `0` and `1` into `{0, 1}`, then `p ∘ q` has its critical
values in `{0, 1}` as well. -/
private theorem criticalValues_comp_subset_zero_one {p q : ℚ[X]}
    (hp : ∀ (L : Type u) [Field L] [Algebra ℚ L], p.criticalValues L ⊆ {0, 1})
    (hq : ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ {0, 1})
    (hp0 : p.eval 0 ∈ ({0, 1} : Set ℚ)) (hp1 : p.eval 1 ∈ ({0, 1} : Set ℚ))
    (L : Type u) [Field L] [Algebra ℚ L] :
    (p.comp q).criticalValues L ⊆ {0, 1} := by
  -- A value of `p` at `0` or `1` of `L` is the image of a rational value in `{0, 1}`.
  have hmap : ∀ y : ℚ, p.eval y ∈ ({0, 1} : Set ℚ) →
      aeval (algebraMap ℚ L y) p ∈ ({0, 1} : Set L) := by
    intro y h
    rw [aeval_algebraMap_apply_eq_algebraMap_eval]
    rcases h with h | h <;> simp_all
  refine (criticalValues_comp_subset p q).trans (Set.union_subset ?_ (hp L))
  rintro _ ⟨y, hy, rfl⟩
  rcases hq L hy with rfl | rfl
  · simpa using hmap 0 hp0
  · simpa using hmap 1 hp1

/-- **The three-point step.** For a set `S` of at least three rational numbers, an affine
normalization followed by a Belyi polynomial sends the least and the greatest element of `S`
to `0` and a third one to `1`. The resulting nonconstant polynomial has critical values in
`{0, 1}`, and the image of `S` is smaller than `S` and contains `0` and `1`. -/
private theorem exists_card_image_lt (S : Finset ℚ) (hS : 2 < S.card) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧
      (∀ (L : Type u) [Field L] [Algebra ℚ L], f.criticalValues L ⊆ {0, 1}) ∧
      (S.image fun s ↦ f.eval s).card < S.card ∧ (0 : ℚ) ∈ S.image (fun s ↦ f.eval s) ∧
      (1 : ℚ) ∈ S.image (fun s ↦ f.eval s) := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  set a := S.min' hne
  set b := S.max' hne
  obtain ⟨c, hcS, hca, hcb⟩ : ∃ c ∈ S, c ≠ a ∧ c ≠ b := by
    have : 0 < ((S.erase a).erase b).card := by
      have h₁ := Finset.pred_card_le_card_erase (s := S) (a := a)
      have h₂ := Finset.pred_card_le_card_erase (s := S.erase a) (a := b)
      omega
    obtain ⟨c, hc⟩ := Finset.card_pos.mp this
    simp only [Finset.mem_erase] at hc
    exact ⟨c, hc.2.2, hc.2.1, hc.1⟩
  have hac : a < c := lt_of_le_of_ne (S.min'_le c hcS) hca.symm
  have hcb' : c < b := lt_of_le_of_ne (S.le_max' c hcS) hcb
  have hab : a ≠ b := (hac.trans hcb').ne
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  -- The affine normalization sending `a` to `0` and `b` to `1`.
  set A := C (b - a)⁻¹ * (X - C a)
  have hA : A.natDegree = 1 := by rw [natDegree_C_mul (inv_ne_zero hba), natDegree_X_sub_C]
  obtain ⟨m, n, hm, hn, hr⟩ := Rat.exists_eq_div_add_of_pos_of_lt_one
    (div_pos (sub_pos.mpr hac) (sub_pos.mpr (hac.trans hcb')))
    ((div_lt_one (sub_pos.mpr (hac.trans hcb'))).mpr (by linarith))
  set f := (belyiPolynomial ℚ m n).comp A
  have hfx : ∀ x, f.eval x = (belyiPolynomial ℚ m n).eval ((x - a) / (b - a)) := fun x ↦ by
    simp [f, A, div_eq_inv_mul]
  have hfa : f.eval a = 0 := by simp [hfx, eval_zero_belyiPolynomial hm]
  have hfb : f.eval b = 0 := by simp [hfx, div_self hba, eval_one_belyiPolynomial m hn]
  have hfc : f.eval c = 1 := by rw [hfx, hr, eval_div_belyiPolynomial]
  refine ⟨f, ?_, fun L _ _ ↦ ?_, ?_, hfa ▸ Finset.mem_image_of_mem _ (S.min'_mem hne),
    hfc ▸ Finset.mem_image_of_mem _ hcS⟩
  · rw [natDegree_comp, natDegree_belyiPolynomial, hA]
    omega
  · -- The affine normalization has no critical values.
    refine (criticalValues_comp_subset _ _).trans (Set.union_subset ?_
      (criticalValues_belyiPolynomial_subset L m n))
    simp [criticalValues_eq_empty_of_natDegree_le_one hA.le]
  · -- The image is smaller since the distinct points `a` and `b` have the same image.
    exact lt_of_le_of_ne Finset.card_image_le fun h ↦
      hab (Finset.card_image_iff.mp h (S.min'_mem hne) (S.max'_mem hne) (hfa.trans hfb.symm))

/-- **Polynomial Belyification over `ℚ`.** Every finite set `S` of rational numbers is carried
into `{0, 1}` by a nonconstant polynomial `q` with rational coefficients whose critical values,
in every field of characteristic zero, lie in `{0, 1}`. -/
theorem exists_polynomial_eval_mem_criticalValues_subset (S : Finset ℚ) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧ (∀ s ∈ S, q.eval s ∈ ({0, 1} : Set ℚ)) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ {0, 1} := by
  -- It suffices to treat sets containing `0` and `1`.
  suffices h : ∀ T : Finset ℚ, 0 ∈ T → 1 ∈ T → ∃ q : ℚ[X], 0 < q.natDegree ∧
      (∀ s ∈ T, q.eval s ∈ ({0, 1} : Set ℚ)) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ {0, 1} by
    obtain ⟨q, hq, hqS, hqcrit⟩ := h (insert 0 (insert 1 S)) (by simp) (by simp)
    exact ⟨q, hq, fun s hs ↦ hqS s (by simp [hs]), hqcrit⟩
  intro S hS0 hS1
  induction hS : S.card using Nat.strong_induction_on generalizing S with
  | _ k ih =>
  subst hS
  by_cases h3 : S.card ≤ 2
  · -- A set of at most two elements containing `0` and `1` is `{0, 1}`, fixed by `X`.
    have hS : S = {0, 1} := (Finset.eq_of_subset_of_card_le (by simp [Finset.insert_subset_iff,
      hS0, hS1]) (h3.trans (Finset.card_pair zero_ne_one).ge)).symm
    exact ⟨X, by simp, fun s hs ↦ by simpa [hS] using hs, fun L _ _ ↦ by simp⟩
  -- Apply the three-point step and recurse on the smaller image, which contains `0` and `1`.
  obtain ⟨f, hf, hfcrit, hT, h0, h1⟩ := exists_card_image_lt S (by omega)
  obtain ⟨q, hq, hqT, hqcrit⟩ := ih _ hT _ h0 h1 rfl
  refine ⟨q.comp f, ?_, fun s hs ↦ ?_,
    criticalValues_comp_subset_zero_one hqcrit hfcrit (hqT 0 h0) (hqT 1 h1)⟩
  · rw [natDegree_comp]
    exact Nat.mul_pos hq hf
  · rw [eval_comp]
    exact hqT _ (Finset.mem_image_of_mem _ hs)

/-- **Polynomial Belyification of algebraic numbers.** Every finite set `S` of elements algebraic
over `ℚ` in a field `K`, such as a finite subset of `AlgebraicClosure ℚ`, is carried into
`{0, 1}` by a nonconstant polynomial `q` with rational coefficients whose critical values, in
every field of characteristic zero, lie in `{0, 1}`. -/
theorem exists_polynomial_aeval_mem_criticalValues_subset {K : Type*} [Field K] [Algebra ℚ K]
    {S : Finset K} (hS : ∀ s ∈ S, IsIntegral ℚ s) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧ (∀ s ∈ S, aeval s q ∈ ({0, 1} : Set K)) ∧
      ∀ (L : Type u) [Field L] [Algebra ℚ L], q.criticalValues L ⊆ {0, 1} := by
  -- Belyi's degree reduction carries `S` and the critical values of `p` into `ℚ`.
  obtain ⟨p, hp', hpS, hpcrit⟩ := exists_polynomial_aeval_mem_range.{u} hS
  -- The rational values of `p` on `S` and the rational critical values of `p` form a finite
  -- set `T`, since the latter are among the critical values of `p` in `AlgebraicClosure ℚ`.
  have hT₁ : (algebraMap ℚ K ⁻¹' ((fun s ↦ aeval s p) '' S)).Finite :=
    (S.finite_toSet.image _).preimage (algebraMap ℚ K).injective.injOn
  have hT₂ :
      (algebraMap ℚ (AlgebraicClosure ℚ) ⁻¹' p.criticalValues (AlgebraicClosure ℚ)).Finite :=
    (criticalValues_finite p).preimage (algebraMap ℚ _).injective.injOn
  -- Polynomial Belyification over `ℚ` carries `T` into `{0, 1}`.
  obtain ⟨q, hq, hqT, hqcrit⟩ :=
    exists_polynomial_eval_mem_criticalValues_subset.{u} (hT₁.toFinset ∪ hT₂.toFinset)
  refine ⟨q.comp p, ?_, fun s hs ↦ ?_, fun L _ _ ↦ ?_⟩
  · rw [natDegree_comp]
    exact Nat.mul_pos hq (Nat.pos_of_ne_zero (derivative_ne_zero.mp hp'))
  · obtain ⟨c, hc⟩ := hpS s hs
    rw [aeval_comp, ← hc, aeval_algebraMap_apply_eq_algebraMap_eval]
    obtain h | h : q.eval c = 0 ∨ q.eval c = 1 :=
      hqT c (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).2 ⟨s, hs, hc.symm⟩))
    all_goals simp [h]
  refine (criticalValues_comp_subset q p).trans (Set.union_subset ?_ (hqcrit L))
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx, rfl⟩ := mem_criticalValues.mp hy
  obtain ⟨c, hc⟩ := hpcrit L x (aeval_eq_zero_of_mem_rootSet hx)
  -- A critical value `c ∈ ℚ` of `p` in `L` is one in `AlgebraicClosure ℚ`, so lies in `T`.
  have hcT : c ∈ hT₁.toFinset ∪ hT₂.toFinset := Finset.mem_union_right _
    ((Set.Finite.mem_toFinset _).2 (algebraMap_mem_criticalValues_of_isAlgClosed
      (hc ▸ aeval_mem_criticalValues hx)))
  simp only [← hc, aeval_algebraMap_apply_eq_algebraMap_eval]
  obtain h | h : q.eval c = 0 ∨ q.eval c = 1 := hqT c hcT
  all_goals simp [h]

end Rat

end LeanFormal.IUT.XiFPaper.BelyiPolynomial


#print axioms Rat.exists_eq_div_add_of_pos_of_lt_one
#print axioms Polynomial.criticalValues_finite
#print axioms LeanFormal.IUT.XiFPaper.BelyiPolynomial.criticalValues_belyiPolynomial_subset
#print axioms LeanFormal.IUT.XiFPaper.BelyiPolynomial.exists_polynomial_aeval_mem_criticalValues_subset
#print axioms LeanFormal.IUT.XiFPaper.BelyiPolynomial.natDegree_belyiPolynomial
