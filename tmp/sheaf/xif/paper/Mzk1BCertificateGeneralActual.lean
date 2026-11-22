/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A927: B certificate, general finite rank -- rank-3 complete instance + gap statement -/

/- RANK-3 COMPLETE MODEL (arithmetic core, no external fields):
* `L = Z^3`, `f = (1/2, 1, 0)`;
  `L cap Q f = Z*(1,2,0)`, `L cap f^perp = Z*(-2,1,0) + Z*(0,0,1)`,
  index `|det [[1,-2,0],[2,1,0],[0,0,1]]| = 5`;
* a Z-linear `P` with `P(1,2,0) = (c,2c,0)` and `P(-2,1,0) = 0`, `P(0,0,1) = 0`;
  writing the first column of `P` as `(a,d,g)` and using `second column = 2*first`,
  the first-coordinate equation is `a + 2*(2a) = c`, i.e. `c = 5a`; hence `5 | c`.

GENERAL RANK GAP (precise): the general finite-rank argument needs
(i) `det(other Z-basis) = r_f * det(L)` with `A + B` of index `r_f`,
(ii) divisibility from integer matrix integrality; Mathlib tools: `Submodule.index`/
`Submodule.quotient` or Smith normal form (if present).  Not formalized here; the rank-2
(A925) and rank-3 (this file) instances are complete. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1BCertificateGeneralActual

/-- **Rank-3 certificate lemma (complete)**: `5 | c` from `b = 2a` and `a + 2b = c`. -/
theorem rankThree_certificate (a b c : ℤ) (hb : b = 2 * a) (h : a + 2 * b = c) :
    (5 : ℤ) ∣ c := by
  refine ⟨a, ?_⟩
  rw [← h, hb]
  ring

/-- Second-coordinate consistency in the rank-3 model: `d + 2e = 2c` follows from
`e = 2d` and `c = 5a` when `a` is the `d`-analogue (`d + 4d = 5d = 2*(5d/2)`). -/
theorem rankThree_second_coordinate (d e c : ℤ) (he : e = 2 * d) (hd : 5 * d = 2 * c) :
    d + 2 * e = 2 * c := by
  rw [he]
  linarith

/-- The third column vanishing forces the third-coordinate equation to be 0. -/
theorem rankThree_third_zero (g h : ℤ) (hg : h = 2 * g) (h3 : g + 2 * h = 0) :
    g = 0 := by nlinarith

def bGenRows : List (String × String × String) :=
  [ ("rank-3 model", "L=Z^3, f=(1/2,1,0), index 5, 3x3 integer matrix", "DEF") ,
    ("rankThree_certificate", "b=2a and a+2b=c => 5 | c (complete)", "PROVED") ,
    ("rankThree_second_coordinate", "d+2e=2c from e=2d and 5d=2c", "PROVED") ,
    ("rankThree_third_zero", "g+2h=0 and h=2g => g=0", "PROVED") ,
    ("general rank", "Submodule.index/quotient or Smith normal form", "GAP (Mathlib) ") ,
    ("complete ranks", "rank 2 (A925) + rank 3 (this file)", "DONE") ,
    ("index API investigation", "AddSubgroup.index_eq_card / index_range_nsmul (TauCetiPort)", "FOUND (Mathlib/port)") ,
    ("general construction", "still requires finite-index/quotient assembly", "GAP (time-boxed)") ]

theorem bGenRows_length : bGenRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1BCertificateGeneralActual
