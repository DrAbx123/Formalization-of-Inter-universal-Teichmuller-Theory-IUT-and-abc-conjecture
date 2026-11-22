/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1BCertificateLemmaActual
import Mathlib.Tactic

/-! # A925: B certificate lemma -- complete rank-2 construction -/

/- RANK-2 COMPLETE MODEL (all hypotheses arithmetic, no external input):
* `L = Z x Z`; `f = (1/2, 1) in Q x Q`;
* `L cap Q f = Z*(1,2)` (since `2 f = (1,2)`), `L cap f^perp = Z*(-2,1)`
  for the standard dot product; their sum has index `r_f = |det [[1,-2],[2,1]]| = 5`;
* a Z-linear `P : L -> L` with matrix columns `m1, m2` satisfies
  `P(f) = c f`  <=>  `P(1,2) = (c, 2c)`,
  and `P` vanishes on the orthogonal lattice  <=>  `P(-2,1) = 0`.
Writing `M = [[a,b],[d,e]]` these become the four integer equations below;
then `c = a + 2b = a + 4a = 5a`, hence `r_f = 5 | c`.

This is the certificate lemma (B.2) COMPLETELY constructed in rank 2 (no E-B-1 field).
The general-rank version still needs the quotient/finite-index construction with
`Submodule.quotient`/`Module.finrank` (recorded as the remaining Mathlib work). -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1BCertificateFullActual

def rfRankTwo : ℤ := 5

theorem rfRankTwo_eq : rfRankTwo = 5 := rfl

/-- Matrix data of a Z-linear endomorphism of `Z x Z` with the certificate hypotheses in
the rank-2 model. -/
structure RankTwoHeckeData where
  a : ℤ
  b : ℤ
  d : ℤ
  e : ℤ
  c : ℤ
  /-- `P(1,2) = (c, 2c)`, first coordinate. -/
  fst : a + 2 * b = c
  /-- `P(1,2) = (c, 2c)`, second coordinate. -/
  snd : d + 2 * e = 2 * c
  /-- `P(-2,1) = 0`, first coordinate (vanishing on the orthogonal lattice). -/
  orth_fst : -2 * a + b = 0
  /-- `P(-2,1) = 0`, second coordinate. -/
  orth_snd : -2 * d + e = 0

/-- **Rank-2 certificate lemma (complete)**: `r_f = 5` divides the eigenvalue `c`. -/
theorem rankTwo_certificate (D : RankTwoHeckeData) : rfRankTwo ∣ D.c := by
  have hb : D.b = 2 * D.a := by linarith [D.orth_fst]
  have hc : D.c = 5 * D.a := by linarith [D.fst, hb]
  refine ⟨D.a, ?_⟩
  rw [rfRankTwo_eq]
  exact hc

/-- The same conclusion stated as `5 ∣ c`. -/
theorem rankTwo_five_dvd (D : RankTwoHeckeData) : (5 : ℤ) ∣ D.c :=
  rankTwo_certificate D

def bFullRows : List (String × String × String) :=
  [ ("rank-2 model", "L=Z^2, f=(1/2,1), L cap Qf = Z(1,2), L cap f^perp = Z(-2,1)", "DEF") ,
    ("index r_f", "|det [[1,-2],[2,1]]| = 5", "DEF (rfRankTwo)") ,
    ("RankTwoHeckeData", "matrix a,b,d,e,c + 4 integer equations", "DEF") ,
    ("rankTwo_certificate", "r_f = 5 divides c (complete, no external field)", "PROVED") ,
    ("general rank", "quotient/Submodule.quotient/finrank construction", "GAP (Mathlib work)") ,
    ("E-B-1 removal", "replaced by explicit rank-2 arithmetic", "DONE (rank 2)") ]

theorem bFullRows_length : bFullRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1BCertificateFullActual
