import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import tmp.sheaf.xif.paper.Mzk1PolyMapActual
import tmp.sheaf.xif.paper.Mzk1MoebiusP1CActual
import tmp.sheaf.xif.paper.Mzk1Lemma22CritValueActual
import tmp.sheaf.xif.paper.Mzk1BelyiCvBridgeActual
import Mathlib.Tactic

/-! # Mzk1PolyEvalP1BridgeActual — ℚ → ℂ cast bridge for polyEvalP1 / specialSet

STEP 0 prior-art (read before writing):
* RestatedLemma24InterfaceActual: P1Point K (= Option K), P1Point.ofFinite,
  P1Point.infty, specialSet K = {infty, ofFinite 0, ofFinite 1},
  polyEvalP1 f p = p.map (fun x => f.eval x).
* Mzk1PolyMapActual: polyMapPoints f (same map), Mzk1PolyMapActual.specialSet
  (same three points, set-builder form).
* Mzk1MoebiusP1CActual: P1Point.mapRatComplex : P1Point ℚ → P1Point ℂ
  (none maps to infty, some x maps to ofFinite (x : ℂ)).  There is NO global Coe
  P1Point ℚ → P1Point ℂ in the tree; mapRatComplex is the actual cast.
* Mzk1Lemma22CritValueActual: aeval_cast_eval (aeval (x:ℂ) f = (f.eval x : ℂ)).
* Mzk1BelyiCvBridgeActual: C-point critical values of the canonical Belyi
  polynomial lie in {0,1}; the C-side vocabulary used by stage4.

This file is a small, exact, reusable bridge (no sorry/axiom/new assumption):

(1) polyEvalP1 on finite points / infinity (rfl), and its identification with
    polyMapPoints plus the two specialSet encodings.
(2) The graph of the ℚ → ℂ cast of P1Point.ofFinite, injectivity of the cast, and
    the casted evaluation map polyEvalP1C.
(3) Pointwise and image correspondence of the special sets under the cast.
(4) Exact avoidance correspondence: for f : ℚ[X] and a finite b : ℚ,
    polyEvalP1 f (ofFinite b) ∉ specialSet ℚ ↔ aeval (b : ℂ) f ∉ {0,1}.
    For a general β : P1Point ℚ the exact form is
    polyEvalP1 f β ∉ specialSet ℚ ↔ β ≠ ∞ ∧ ∀ b, β = ofFinite b → aeval (b:ℂ) f ∉ {0,1},
    equivalently with the existential finite form.  Nonconstancy of f is recorded
    in the paper-facing wrapper; the equivalence itself needs no nonconstancy.

Registry frozen 14041; no existing file is modified. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PolyEvalP1BridgeActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1CActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22CritValueActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1BelyiCvBridgeActual

/-! ## (1) polyEvalP1 on finite points and at infinity -/

/-- (1) On a finite point, polyEvalP1 is plain polynomial evaluation. -/
theorem polyEvalP1_ofFinite (f : ℚ[X]) (x : ℚ) :
    polyEvalP1 f (P1Point.ofFinite x) = P1Point.ofFinite (f.eval x) := rfl

/-- (1) At infinity, polyEvalP1 fixes infinity. -/
theorem polyEvalP1_infty (f : ℚ[X]) :
    polyEvalP1 f (P1Point.infty : P1Point ℚ) = P1Point.infty := rfl

/-- (1) polyEvalP1 is literally the polyMapPoints of Mzk1PolyMapActual
(the two prior-art evaluation layers coincide). -/
theorem polyEvalP1_eq_polyMapPoints (f : ℚ[X]) :
    polyEvalP1 f = polyMapPoints f := by
  funext p
  cases p with
  | none => rfl
  | some x => rfl

/-- (1) The specialSet of RestatedLemma24InterfaceActual and the set-builder
specialSet of Mzk1PolyMapActual are the same subset of P1(ℚ). -/
theorem specialSet_eq_polyMapSpecialSet :
    RestatedLemma24InterfaceActual.specialSet ℚ = Mzk1PolyMapActual.specialSet := by
  ext p
  cases p with
  | none =>
      simp [RestatedLemma24InterfaceActual.specialSet, Mzk1PolyMapActual.specialSet,
        P1Point.infty, P1Point.ofFinite]
  | some x =>
      simp [RestatedLemma24InterfaceActual.specialSet, Mzk1PolyMapActual.specialSet,
        P1Point.infty, P1Point.ofFinite]

/-- (1) Membership bridge between the two prior-art specialSet encodings. -/
theorem polyEvalP1_mem_specialSet_iff_polyMapPoints (f : ℚ[X]) (p : P1Point ℚ) :
    polyEvalP1 f p ∈ RestatedLemma24InterfaceActual.specialSet ℚ ↔
      polyMapPoints f p ∈ Mzk1PolyMapActual.specialSet := by
  rw [polyEvalP1_eq_polyMapPoints, specialSet_eq_polyMapSpecialSet]

/-! ## (2) The graph of the ℚ → ℂ cast of P1Point -/

/-- (2) The cast of a finite point: mapRatComplex (ofFinite x) = ofFinite (x : ℂ). -/
theorem P1Point.mapRatComplex_ofFinite (x : ℚ) :
    P1Point.mapRatComplex (P1Point.ofFinite x) =
      P1Point.ofFinite ((x : ℚ) : ℂ) := rfl

/-- (2) The cast fixes infinity. -/
theorem P1Point.mapRatComplex_infty :
    P1Point.mapRatComplex (P1Point.infty : P1Point ℚ) =
      (P1Point.infty : P1Point ℂ) := rfl

/-- (2) The cast P1Point ℚ → P1Point ℂ is injective. -/
theorem P1Point.mapRatComplex_injective : Function.Injective P1Point.mapRatComplex := by
  intro p q h
  cases p with
  | none =>
      cases q with
      | none => rfl
      | some y =>
          exact absurd h (by simp [P1Point.mapRatComplex, P1Point.infty, P1Point.ofFinite])
  | some x =>
      cases q with
      | none =>
          exact absurd h (by simp [P1Point.mapRatComplex, P1Point.infty, P1Point.ofFinite])
      | some y =>
          simp only [P1Point.mapRatComplex, P1Point.ofFinite, Option.some.injEq] at h
          exact congrArg P1Point.ofFinite (Rat.cast_injective h)

/-- (2) Casted evaluation map: evaluate a ℚ-polynomial at a P1(ℚ)-point and cast
the result to P1(ℂ).  This is the image of polyEvalP1 under P1Point.mapRatComplex. -/
def polyEvalP1C (f : ℚ[X]) : P1Point ℚ → P1Point ℂ :=
  fun p => P1Point.mapRatComplex (polyEvalP1 f p)

/-- (2) polyEvalP1C is definitionally the cast of polyEvalP1. -/
theorem polyEvalP1C_eq_mapRatComplex (f : ℚ[X]) (p : P1Point ℚ) :
    polyEvalP1C f p = P1Point.mapRatComplex (polyEvalP1 f p) := rfl

/-- (2) On finite points the casted evaluation is aeval at the cast coordinate. -/
theorem polyEvalP1C_ofFinite (f : ℚ[X]) (x : ℚ) :
    polyEvalP1C f (P1Point.ofFinite x) =
      P1Point.ofFinite (Polynomial.aeval ((x : ℚ) : ℂ) f) := by
  show P1Point.mapRatComplex (polyEvalP1 f (P1Point.ofFinite x)) =
    P1Point.ofFinite (Polynomial.aeval ((x : ℚ) : ℂ) f)
  rw [polyEvalP1_ofFinite, P1Point.mapRatComplex_ofFinite, aeval_cast_eval]

/-- (2) At infinity the casted evaluation is infinity. -/
theorem polyEvalP1C_infty (f : ℚ[X]) :
    polyEvalP1C f (P1Point.infty : P1Point ℚ) = (P1Point.infty : P1Point ℂ) := rfl

/-! ## (3) specialSet correspondence under the cast -/

/-- (3) Membership of a finite point in specialSet K is exactly being 0 or 1. -/
theorem ofFinite_mem_specialSet_iff (K : Type) [Zero K] [One K] (x : K) :
    (P1Point.ofFinite x : P1Point K) ∈ RestatedLemma24InterfaceActual.specialSet K ↔
      x = 0 ∨ x = 1 := by
  simp [RestatedLemma24InterfaceActual.specialSet, P1Point.ofFinite, P1Point.infty,
    Set.mem_insert_iff, Set.mem_singleton_iff]

/-- (3) Membership of a finite point in specialSet K fails exactly at 0 and 1. -/
theorem ofFinite_notMem_specialSet_iff (K : Type) [Zero K] [One K] (x : K) :
    (P1Point.ofFinite x : P1Point K) ∉ RestatedLemma24InterfaceActual.specialSet K ↔
      x ≠ 0 ∧ x ≠ 1 := by
  rw [ofFinite_mem_specialSet_iff, not_or]

/-- (3) The three points {∞, 0, 1} over ℚ map exactly onto {∞, 0, 1} over ℂ
under the cast (pointwise membership form). -/
theorem P1Point.mapRatComplex_mem_specialSet_iff (p : P1Point ℚ) :
    P1Point.mapRatComplex p ∈ RestatedLemma24InterfaceActual.specialSet ℂ ↔
      p ∈ RestatedLemma24InterfaceActual.specialSet ℚ := by
  rcases P1Point.eq_infty_or_finite p with rfl | ⟨x, rfl⟩
  · simp [P1Point.mapRatComplex, P1Point.infty,
      RestatedLemma24InterfaceActual.specialSet]
  · rw [P1Point.mapRatComplex_ofFinite,
      ofFinite_mem_specialSet_iff ℂ ((x : ℚ) : ℂ),
      ofFinite_mem_specialSet_iff ℚ x]
    constructor
    · rintro (h | h)
      · left
        exact_mod_cast h
      · right
        exact_mod_cast h
    · rintro (h | h)
      · left
        rw [h]
        exact Rat.cast_zero
      · right
        rw [h]
        exact Rat.cast_one

/-- (3) Individual point membership: infinity corresponds to infinity. -/
theorem P1Point.mapRatComplex_infty_mem_specialSet_iff :
    (P1Point.infty : P1Point ℂ) ∈ RestatedLemma24InterfaceActual.specialSet ℂ ↔
      (P1Point.infty : P1Point ℚ) ∈
        RestatedLemma24InterfaceActual.specialSet ℚ := by
  simp [RestatedLemma24InterfaceActual.specialSet, P1Point.infty]

/-- (3) Individual point membership: 0 corresponds to 0. -/
theorem P1Point.mapRatComplex_zero_mem_specialSet_iff :
    P1Point.ofFinite (0 : ℂ) ∈ RestatedLemma24InterfaceActual.specialSet ℂ ↔
      P1Point.ofFinite (0 : ℚ) ∈
        RestatedLemma24InterfaceActual.specialSet ℚ := by
  simp [RestatedLemma24InterfaceActual.specialSet, P1Point.ofFinite]

/-- (3) Individual point membership: 1 corresponds to 1. -/
theorem P1Point.mapRatComplex_one_mem_specialSet_iff :
    P1Point.ofFinite (1 : ℂ) ∈ RestatedLemma24InterfaceActual.specialSet ℂ ↔
      P1Point.ofFinite (1 : ℚ) ∈
        RestatedLemma24InterfaceActual.specialSet ℚ := by
  simp [RestatedLemma24InterfaceActual.specialSet, P1Point.ofFinite]

/-- (3) The design C-typed target set specialSetC is the same as specialSet ℂ. -/
theorem specialSetC_eq_specialSet_complex :
    specialSetC = RestatedLemma24InterfaceActual.specialSet ℂ := by
  ext p
  simp [specialSetC, RestatedLemma24InterfaceActual.specialSet, P1Point.infty,
    P1Point.ofFinite, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- (3) Pointwise membership correspondence with the design target set specialSetC
(the exact C-side vocabulary of stage4). -/
theorem P1Point.mapRatComplex_mem_specialSetC_iff (p : P1Point ℚ) :
    P1Point.mapRatComplex p ∈ specialSetC ↔
      p ∈ RestatedLemma24InterfaceActual.specialSet ℚ := by
  rw [specialSetC_eq_specialSet_complex]
  exact P1Point.mapRatComplex_mem_specialSet_iff p

/-- (3) Image of the rational special set under the cast: exactly the complex one. -/
theorem P1Point.mapRatComplex_image_specialSet :
    P1Point.mapRatComplex '' RestatedLemma24InterfaceActual.specialSet ℚ =
      RestatedLemma24InterfaceActual.specialSet ℂ := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (P1Point.mapRatComplex_mem_specialSet_iff q).mpr hq
  · intro hp
    have hp' : p = P1Point.infty ∨ p = P1Point.ofFinite (0 : ℂ) ∨
        p = P1Point.ofFinite (1 : ℂ) := by
      simpa [RestatedLemma24InterfaceActual.specialSet, P1Point.infty, P1Point.ofFinite,
        Set.mem_insert_iff, Set.mem_singleton_iff] using hp
    rcases hp' with rfl | rfl | rfl
    · exact ⟨P1Point.infty,
        by simp [RestatedLemma24InterfaceActual.specialSet, P1Point.infty], rfl⟩
    · exact ⟨P1Point.ofFinite (0 : ℚ),
        by simp [RestatedLemma24InterfaceActual.specialSet, P1Point.ofFinite],
        by simpa using P1Point.mapRatComplex_ofFinite (0 : ℚ)⟩
    · exact ⟨P1Point.ofFinite (1 : ℚ),
        by simp [RestatedLemma24InterfaceActual.specialSet, P1Point.ofFinite],
        by simpa using P1Point.mapRatComplex_ofFinite (1 : ℚ)⟩

/-! ## (4) Exact avoidance correspondence (the stage4 cast) -/

/-- Cast preserves membership in {0,1}. -/
theorem ratCast_mem_zeroOne_iff (q : ℚ) :
    ((q : ℚ) : ℂ) ∈ ({0, 1} : Set ℂ) ↔ q ∈ ({0, 1} : Set ℚ) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · left
      exact_mod_cast h
    · right
      exact_mod_cast h
  · rintro (h | h)
    · left
      rw [h]
      exact Rat.cast_zero
    · right
      rw [h]
      exact Rat.cast_one

/-- (4) Finite-point form of the exact avoidance correspondence:
polyEvalP1 f (ofFinite b) ∉ specialSet ℚ iff aeval (b:ℂ) f ∉ {0,1}.
This is the main usable form for the stage4 cast; ofFinite b ≠ ∞ is automatic. -/
theorem polyEvalP1_ofFinite_notMem_specialSet_iff_aeval_notMem
    (f : ℚ[X]) (b : ℚ) :
    polyEvalP1 f (P1Point.ofFinite b) ∉
        RestatedLemma24InterfaceActual.specialSet ℚ ↔
      Polynomial.aeval ((b : ℚ) : ℂ) f ∉ ({0, 1} : Set ℂ) := by
  rw [polyEvalP1_ofFinite, aeval_cast_eval]
  have hQ : (P1Point.ofFinite (f.eval b) : P1Point ℚ) ∈
      RestatedLemma24InterfaceActual.specialSet ℚ ↔
        f.eval b = 0 ∨ f.eval b = 1 :=
    ofFinite_mem_specialSet_iff ℚ (f.eval b)
  have hC : ((f.eval b : ℚ) : ℂ) ∈ ({0, 1} : Set ℂ) ↔
      f.eval b = 0 ∨ f.eval b = 1 := by
    rw [ratCast_mem_zeroOne_iff]
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [not_congr hQ, not_congr hC]

/-- (4) The same finite-point correspondence in the literal shape with the explicit
β ≠ ∞ conjunct (here β = ofFinite b, so the conjunct is True but displayed). -/
theorem polyEvalP1_ofFinite_notMem_specialSet_iff_aeval_notMem_and_ne_infty
    (f : ℚ[X]) (b : ℚ) :
    polyEvalP1 f (P1Point.ofFinite b) ∉
        RestatedLemma24InterfaceActual.specialSet ℚ ↔
      Polynomial.aeval ((b : ℚ) : ℂ) f ∉ ({0, 1} : Set ℂ) ∧
        (P1Point.ofFinite b : P1Point ℚ) ≠ P1Point.infty := by
  rw [polyEvalP1_ofFinite_notMem_specialSet_iff_aeval_notMem]
  exact ⟨fun h => ⟨h, P1Point.ofFinite_ne_infty b⟩, fun h => h.1⟩

/-- (4) General P1-point form with the explicit β ≠ ∞ conjunct. -/
theorem polyEvalP1_notMem_specialSet_iff_ne_infty_and_aeval
    (f : ℚ[X]) (β : P1Point ℚ) :
    polyEvalP1 f β ∉ RestatedLemma24InterfaceActual.specialSet ℚ ↔
      β ≠ P1Point.infty ∧
        ∀ b : ℚ, β = P1Point.ofFinite b →
          Polynomial.aeval ((b : ℚ) : ℂ) f ∉ ({0, 1} : Set ℂ) := by
  rcases P1Point.eq_infty_or_finite β with rfl | ⟨b, rfl⟩
  · simp [polyEvalP1, P1Point.infty,
      RestatedLemma24InterfaceActual.specialSet]
  · rw [polyEvalP1_ofFinite_notMem_specialSet_iff_aeval_notMem]
    constructor
    · intro h
      refine ⟨P1Point.ofFinite_ne_infty b, ?_⟩
      intro b' hb'
      have hb'' : b' = b := by simpa [P1Point.ofFinite] using hb'.symm
      subst b'
      exact h
    · rintro ⟨_, h⟩
      exact h b rfl

/-- (4) General P1-point form with an existential finite coordinate (equivalent to
the β ≠ ∞ form, often easier to consume). -/
theorem polyEvalP1_notMem_specialSet_iff_exists_finite_aeval
    (f : ℚ[X]) (β : P1Point ℚ) :
    polyEvalP1 f β ∉ RestatedLemma24InterfaceActual.specialSet ℚ ↔
      ∃ b : ℚ, β = P1Point.ofFinite b ∧
        Polynomial.aeval ((b : ℚ) : ℂ) f ∉ ({0, 1} : Set ℂ) := by
  rw [polyEvalP1_notMem_specialSet_iff_ne_infty_and_aeval]
  constructor
  · rintro ⟨hne, h⟩
    rcases P1Point.eq_infty_or_finite β with rfl | ⟨b, rfl⟩
    · exact absurd rfl hne
    · exact ⟨b, rfl, h b rfl⟩
  · rintro ⟨b, rfl, h⟩
    refine ⟨P1Point.ofFinite_ne_infty b, ?_⟩
    intro b' hb'
    have hb'' : b' = b := by simpa [P1Point.ofFinite] using hb'.symm
    subst b'
    exact h

/-- (4) Membership companion (used to cast the preservation clause of Lemma 2.4). -/
theorem polyEvalP1_ofFinite_mem_specialSet_iff_aeval_mem
    (f : ℚ[X]) (b : ℚ) :
    polyEvalP1 f (P1Point.ofFinite b) ∈
        RestatedLemma24InterfaceActual.specialSet ℚ ↔
      Polynomial.aeval ((b : ℚ) : ℂ) f ∈ ({0, 1} : Set ℂ) := by
  rw [polyEvalP1_ofFinite, aeval_cast_eval]
  have hQ := ofFinite_mem_specialSet_iff ℚ (f.eval b)
  have hC : ((f.eval b : ℚ) : ℂ) ∈ ({0, 1} : Set ℂ) ↔
      f.eval b = 0 ∨ f.eval b = 1 := by
    rw [ratCast_mem_zeroOne_iff]
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [hQ, hC]

/-- (4) General membership form: the image of β lies in specialSet ℚ iff either
β = ∞ or β is finite with C-value in {0,1}. -/
theorem polyEvalP1_mem_specialSet_iff (f : ℚ[X]) (β : P1Point ℚ) :
    polyEvalP1 f β ∈ RestatedLemma24InterfaceActual.specialSet ℚ ↔
      β = P1Point.infty ∨
        ∃ b : ℚ, β = P1Point.ofFinite b ∧
          Polynomial.aeval ((b : ℚ) : ℂ) f ∈ ({0, 1} : Set ℂ) := by
  rcases P1Point.eq_infty_or_finite β with rfl | ⟨b, rfl⟩
  · simp [polyEvalP1, P1Point.infty,
      RestatedLemma24InterfaceActual.specialSet]
  · rw [polyEvalP1_ofFinite_mem_specialSet_iff_aeval_mem]
    constructor
    · intro h
      exact Or.inr ⟨b, rfl, h⟩
    · rintro (h | ⟨b', hb', h⟩)
      · exact absurd h (by simp [P1Point.ofFinite, P1Point.infty])
      · have hb'' : b' = b := by simpa [P1Point.ofFinite] using hb'.symm
        subst b'
        exact h

/-- (4) C-side (casted point) form: the casted evaluation avoids the C special set
iff the rational evaluation avoids the rational special set. -/
theorem polyEvalP1C_mem_specialSetC_iff (f : ℚ[X]) (β : P1Point ℚ) :
    polyEvalP1C f β ∈ specialSetC ↔
      polyEvalP1 f β ∈ RestatedLemma24InterfaceActual.specialSet ℚ :=
  P1Point.mapRatComplex_mem_specialSetC_iff (polyEvalP1 f β)

/-- (4) C-side (casted point) avoidance form. -/
theorem polyEvalP1C_notMem_specialSetC_iff (f : ℚ[X]) (β : P1Point ℚ) :
    polyEvalP1C f β ∉ specialSetC ↔
      polyEvalP1 f β ∉ RestatedLemma24InterfaceActual.specialSet ℚ :=
  not_congr (polyEvalP1C_mem_specialSetC_iff f β)

/-- (4) C-side finite-point form: the casted point polyEvalP1C f (ofFinite b) avoids
specialSetC iff aeval (b:ℂ) f ∉ {0,1}.  This is the most direct stage4 cast form. -/
theorem polyEvalP1C_ofFinite_notMem_specialSetC_iff_aeval_notMem
    (f : ℚ[X]) (b : ℚ) :
    polyEvalP1C f (P1Point.ofFinite b) ∉ specialSetC ↔
      Polynomial.aeval ((b : ℚ) : ℂ) f ∉ ({0, 1} : Set ℂ) := by
  rw [polyEvalP1C_notMem_specialSetC_iff,
    polyEvalP1_ofFinite_notMem_specialSet_iff_aeval_notMem]

/-- (4) C-side general form with the explicit β ≠ ∞ conjunct (exact stage4 shape). -/
theorem polyEvalP1C_notMem_specialSetC_iff_ne_infty_and_aeval
    (f : ℚ[X]) (β : P1Point ℚ) :
    polyEvalP1C f β ∉ specialSetC ↔
      β ≠ P1Point.infty ∧
        ∀ b : ℚ, β = P1Point.ofFinite b →
          Polynomial.aeval ((b : ℚ) : ℂ) f ∉ ({0, 1} : Set ℂ) := by
  rw [polyEvalP1C_notMem_specialSetC_iff,
    polyEvalP1_notMem_specialSet_iff_ne_infty_and_aeval]

/-- (4) Paper-facing nonconstant wrapper of the finite-point form.  The equivalence
itself does not need 0 < f.natDegree; the hypothesis is carried because the Lemma 2.4
witness is nonconstant. -/
theorem nonconstant_polyEvalP1_ofFinite_notMem_specialSet_iff_aeval_notMem
    (f : ℚ[X]) (hf : 0 < f.natDegree) (b : ℚ) :
    polyEvalP1 f (P1Point.ofFinite b) ∉
        RestatedLemma24InterfaceActual.specialSet ℚ ↔
      Polynomial.aeval ((b : ℚ) : ℂ) f ∉ ({0, 1} : Set ℂ) :=
  polyEvalP1_ofFinite_notMem_specialSet_iff_aeval_notMem f b

/-- (4) Paper-facing nonconstant wrapper of the general β ≠ ∞ form. -/
theorem nonconstant_polyEvalP1_notMem_specialSet_iff_ne_infty_and_aeval
    (f : ℚ[X]) (hf : 0 < f.natDegree) (β : P1Point ℚ) :
    polyEvalP1 f β ∉ RestatedLemma24InterfaceActual.specialSet ℚ ↔
      β ≠ P1Point.infty ∧
        ∀ b : ℚ, β = P1Point.ofFinite b →
          Polynomial.aeval ((b : ℚ) : ℂ) f ∉ ({0, 1} : Set ℂ) :=
  polyEvalP1_notMem_specialSet_iff_ne_infty_and_aeval f β

/-! ## Application to the canonical Belyi polynomial (asset check) -/

/-- Application: for the canonical Belyi polynomial, the rational avoidance condition
at a finite rational point is exactly the C-side condition used by the Belyi/CV layer. -/
theorem belyiPolynomial_avoid_iff_C (m n : ℕ) (b : ℚ) :
    polyEvalP1 (TauCeti.belyiPolynomial ℚ m n) (P1Point.ofFinite b) ∉
        RestatedLemma24InterfaceActual.specialSet ℚ ↔
      Polynomial.aeval ((b : ℚ) : ℂ) (TauCeti.belyiPolynomial ℚ m n) ∉
        ({0, 1} : Set ℂ) :=
  polyEvalP1_ofFinite_notMem_specialSet_iff_aeval_notMem _ _

/-- Application: the C-point critical values of the canonical Belyi polynomial lie in
{0,1} (restated-target criticalValuesOverC form), reusing the proved
belyiPolynomial_critIn01 of Mzk1BelyiCvBridgeActual. -/
theorem belyiPolynomial_criticalValuesOverC_subset {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    RestatedLemma24InterfaceActual.criticalValuesOverC
        (TauCeti.belyiPolynomial ℚ m n) ⊆ ({0, 1} : Set ℂ) := by
  rintro c ⟨z, _hnd, hder, rfl⟩
  have hval := belyiPolynomial_critIn01 hm hn z hder
  simpa using hval

/-! ## Rows -/

/-- Summary rows: (item, status, main declaration). -/
def polyEvalP1BridgeRows : List (String × String × String) :=
  [ ("(1) polyEvalP1 finite/infinity", "PROVED (rfl)",
      "polyEvalP1_ofFinite, polyEvalP1_infty, polyEvalP1_eq_polyMapPoints")
  , ("(2) P1Point ℚ → ℂ cast graph", "PROVED (rfl + injection)",
      "P1Point.mapRatComplex_ofFinite/_infty/_injective, polyEvalP1C_ofFinite")
  , ("(3) specialSet ℚ ↔ ℂ correspondence", "PROVED",
      "P1Point.mapRatComplex_mem_specialSet_iff/_specialSetC_iff/_image_specialSet")
  , ("(4) exact avoidance cast", "PROVED",
      "polyEvalP1_ofFinite_notMem_specialSet_iff_aeval_notMem + general Option forms")
  , ("Belyi application", "PROVED",
      "belyiPolynomial_avoid_iff_C, belyiPolynomial_criticalValuesOverC_subset") ]

theorem polyEvalP1BridgeRows_length : polyEvalP1BridgeRows.length = 5 := rfl

#check polyEvalP1_ofFinite
#check polyEvalP1_infty
#check polyEvalP1_eq_polyMapPoints
#check P1Point.mapRatComplex_ofFinite
#check P1Point.mapRatComplex_injective
#check polyEvalP1C_ofFinite
#check P1Point.mapRatComplex_mem_specialSet_iff
#check P1Point.mapRatComplex_infty_mem_specialSet_iff
#check P1Point.mapRatComplex_zero_mem_specialSet_iff
#check P1Point.mapRatComplex_one_mem_specialSet_iff
#check polyEvalP1C_eq_mapRatComplex
#check P1Point.mapRatComplex_mem_specialSetC_iff
#check P1Point.mapRatComplex_image_specialSet
#check polyEvalP1_ofFinite_notMem_specialSet_iff_aeval_notMem
#check polyEvalP1_notMem_specialSet_iff_ne_infty_and_aeval
#check polyEvalP1_notMem_specialSet_iff_exists_finite_aeval
#check polyEvalP1C_ofFinite_notMem_specialSetC_iff_aeval_notMem
#check polyEvalP1C_notMem_specialSetC_iff_ne_infty_and_aeval
#check nonconstant_polyEvalP1_notMem_specialSet_iff_ne_infty_and_aeval
#check belyiPolynomial_avoid_iff_C
#check belyiPolynomial_criticalValuesOverC_subset
#check polyEvalP1BridgeRows_length

end LeanFormal.IUT.XiFPaper.Mzk1PolyEvalP1BridgeActual
end
