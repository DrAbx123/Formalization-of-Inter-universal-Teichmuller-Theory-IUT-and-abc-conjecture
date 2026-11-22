/- R5: the projective line `P1(L)` as pairs modulo scaling, with the well-defined boundary
distance `rhoP1` obtained from `rhoDist` by scale invariance (`rhoDist_smul`). REUSE:
- `Mzk1G1GKRhoDistanceActual.rhoDist`, `Mzk1G1GKRhoZeroActual.rhoDist_eq_zero_iff`,
  `Mzk1G1GKRhoSmulActual.rhoDist_smul` (this lane).
DEDUP: no analytic P1(L) pair model existed. -/
import tmp.sheaf.xif.paper.Mzk1G1GKRhoSmulActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoP1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoDistanceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoZeroActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoSmulActual

variable {L : Type*} [NormedField L]

/-- The scaling relation on nonzero pairs: `q = c • p` for some `c ≠ 0`. -/
def p1PairRel (p q : {p : L × L // p ≠ (0, 0)}) : Prop :=
  ∃ c : L, c ≠ 0 ∧ q.1 = (c * p.1.1, c * p.1.2)

theorem p1PairRel_refl (p : {p : L × L // p ≠ (0, 0)}) : p1PairRel p p := by
  refine ⟨1, one_ne_zero, ?_⟩
  simp

theorem p1PairRel_symm {p q : {p : L × L // p ≠ (0, 0)}} (h : p1PairRel p q) :
    p1PairRel q p := by
  obtain ⟨c, hc, hq⟩ := h
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [hq]
  ext <;> simp [← mul_assoc, inv_mul_cancel₀ hc]

theorem p1PairRel_trans {p q r : {p : L × L // p ≠ (0, 0)}}
    (h1 : p1PairRel p q) (h2 : p1PairRel q r) : p1PairRel p r := by
  obtain ⟨c, hc, hq⟩ := h1
  obtain ⟨d, hd, hr⟩ := h2
  refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
  rw [hr, hq]
  ext <;> simp [mul_assoc]

/-- The setoid of the analytic projective line `P1(L)`. -/
def p1PairSetoid : Setoid {p : L × L // p ≠ (0, 0)} where
  r := p1PairRel
  iseqv := ⟨p1PairRel_refl, p1PairRel_symm, p1PairRel_trans⟩

/-- The analytic projective line: nonzero pairs modulo scaling. -/
abbrev P1Pair : Type _ := Quotient (p1PairSetoid (L := L))

/-- **The boundary distance on `P1(L)`**, well-defined by scale invariance. -/
noncomputable def rhoP1 (x : P1Pair (L := L)) : ℝ :=
  Quotient.lift (fun p => rhoDist p.1.1 p.1.2) (by
    intro p q h
    obtain ⟨c, hc, hq⟩ := h
    show rhoDist p.1.1 p.1.2 = rhoDist q.1.1 q.1.2
    rw [hq]
    exact (rhoDist_smul c hc p.1.1 p.1.2).symm) x

/-- The boundary distance is nonnegative on the projective line. -/
theorem rhoP1_nonneg (x : P1Pair (L := L)) : 0 ≤ rhoP1 x := by
  induction x using Quotient.ind with
  | _ p => exact rhoDist_nonneg p.1.1 p.1.2

end LeanFormal.IUT.XiFPaper.Mzk1G1GKRhoP1Actual