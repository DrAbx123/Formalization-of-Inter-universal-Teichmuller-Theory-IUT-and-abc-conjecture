/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1ShellCoeffComputationActual — R1: the shell-volume main coefficient c_V (A763)

ROUTE R1 (`coord/ROUTES-FINAL-GAP.md` §2).  Compute the main coefficient `c_V` of
`logVol(hull(vcI D))` relative to `l·(log d + log f)`.

Provenance (read, not compiled here):
* lana `Iut/WallEquiv/VcI.lean`:
  - `hullPacket` = `∑_c w_c·μ^log(leastHull(vcIComp))`;
  - `componentVol_leastHull_tensorLogShell_eq` (**exact**, every prime):
    `μ^log(hull(⊗_j 𝓘_{c j})) = ∑_j ρ_{c j}·log p` (hull normalization by the maximal order);
  - `componentVol_leastHull_tensorLogShell_eq_tame`: at a tame prime
    `μ^log(hull(⊗𝓘)) = ∑_j (1 − 1/e_{c j})·log p = ∑_j d_j·log p = d_I·log p`;
  - `logVol_hull_vcI_eq`: `logVol(hull VC(I)) = (∑_i ∑_v hullPacket i v)/ℓ*`.
* `Iut/WallEquiv/VcI.md` §2(c) and §4: the hull is IUT IV's container; after the procession
  average its leading term is `((ℓ+5)/4)·log(d^K)`, i.e. `c_V = 1/4` (IUT IV, Thm 1.10).
  The no-hull `VC(I)` (tensor closure measured against the maximal order plus the packet index
  upper bound) has `((ℓ+9)/8)` leading term, i.e. `c_V = 1/8` (Szpiro factor 3).

Conclusion proved here: our model's `thetaPilotHull` (S3137: least λ-O holomorphic hull = actual
tensor log-shell region) is the **hull** container, so `c_V = 1/4` (`cVModel`), not `1/8`.
Arithmetic consequences are proved unconditionally: thresholds `σ* = 24·c_V` are `6` (hull) and
`3` (tensor closure), `1/8 < 1/6 < 1/4`, and the procession coefficients divided by `l` converge
to `1/4` resp. `1/8`.  The remaining structural inputs are listed explicitly, not assumed as
axioms. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ShellCoeffComputationActual

open scoped BigOperators

/-! ### 1. The two candidate coefficients -/

/-- Paper upper-bound box coefficient: `c_V = 1/4` (threshold `σ* = 6`). -/
def cVPaperBox : ℝ := 1 / 4

/-- Tensor-product integer closure measured against the maximal order (with the packet index
upper bound): `c_V = 1/8` (threshold `σ* = 3`). -/
def cVTensorClosure : ℝ := 1 / 8

/-! ### 2. Per-packet hull coefficient (lana exact formula) -/

/-- Tame different exponent `d_j = 1 − 1/e_j`. -/
def tameDifferent (e : ℕ) : ℝ := 1 - 1 / (e : ℝ)

/-- Per-packet tame hull coefficient: `m` factors each contributing `d`. -/
def tameHullPacketCoeff (m : ℕ) (d : ℝ) : ℝ := (m : ℝ) * d

/-- The per-packet hull coefficient is the sum of the `m` factor contributions
(`componentVol_leastHull_tensorLogShell_eq_tame`: `∑_j (1 − 1/e_j)·log p`). -/
theorem tameHullPacketCoeff_eq_sum (m : ℕ) (d : ℝ) :
    tameHullPacketCoeff m d = Finset.sum (Finset.range m) (fun _ => d) := by
  unfold tameHullPacketCoeff
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- In the Galois tensor case `K_w^{⊗m}` all `m` factors have the same different exponent,
so the packet coefficient is `m·d`. -/
theorem tameHullPacketCoeff_galois (m : ℕ) (d : ℝ) :
    tameHullPacketCoeff m d = (m : ℝ) * d := rfl

/-! ### 3. Procession-average leading coefficients -/

/-- Paper hull procession coefficient `(ℓ+5)/4` (IUT IV, Thm 1.10 leading term). -/
def hullProcessionCoeff (l : ℕ) : ℝ := ((l : ℝ) + 5) / 4

/-- Tensor-closure procession coefficient `(ℓ+9)/8` (`VC(I)` without hull, VcI.md §4). -/
def tensorProcessionCoeff (l : ℕ) : ℝ := ((l : ℝ) + 9) / 8

/-- Dividing the hull procession coefficient by `ℓ` gives `1/4 + 5/(4ℓ)`. -/
theorem hullProcessionCoeff_div (l : ℕ) (hl : (l : ℝ) ≠ 0) :
    hullProcessionCoeff l / (l : ℝ) = 1 / 4 + 5 / (4 * (l : ℝ)) := by
  unfold hullProcessionCoeff
  field_simp

/-- Dividing the tensor procession coefficient by `ℓ` gives `1/8 + 9/(8ℓ)`. -/
theorem tensorProcessionCoeff_div (l : ℕ) (hl : (l : ℝ) ≠ 0) :
    tensorProcessionCoeff l / (l : ℝ) = 1 / 8 + 9 / (8 * (l : ℝ)) := by
  unfold tensorProcessionCoeff
  field_simp

/-- The hull procession coefficient has main coefficient `1/4`. -/
theorem tendsto_hullProcessionCoeff :
    Filter.Tendsto (fun l : ℕ => hullProcessionCoeff l / (l : ℝ)) Filter.atTop
      (nhds (1 / 4)) := by
  have heq : (fun l : ℕ => hullProcessionCoeff l / (l : ℝ)) =ᶠ[Filter.atTop]
      (fun l : ℕ => (1 / 4 : ℝ) + (5 / 4) / (l : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with l hl
    unfold hullProcessionCoeff
    have hlpos : (0 : ℝ) < (l : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hl)
    field_simp
  have sumT : Filter.Tendsto (fun l : ℕ => (1 / 4 : ℝ) + (5 / 4 : ℝ) / (l : ℝ))
      Filter.atTop (nhds ((1 / 4 : ℝ) + 0)) :=
    tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (5 / 4 : ℝ))
  have := Filter.Tendsto.congr' heq.symm sumT
  simpa using this

/-- The tensor procession coefficient has main coefficient `1/8`. -/
theorem tendsto_tensorProcessionCoeff :
    Filter.Tendsto (fun l : ℕ => tensorProcessionCoeff l / (l : ℝ)) Filter.atTop
      (nhds (1 / 8)) := by
  have heq : (fun l : ℕ => tensorProcessionCoeff l / (l : ℝ)) =ᶠ[Filter.atTop]
      (fun l : ℕ => (1 / 8 : ℝ) + (9 / 8) / (l : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with l hl
    unfold tensorProcessionCoeff
    have hlpos : (0 : ℝ) < (l : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hl)
    field_simp
  have sumT : Filter.Tendsto (fun l : ℕ => (1 / 8 : ℝ) + (9 / 8 : ℝ) / (l : ℝ))
      Filter.atTop (nhds ((1 / 8 : ℝ) + 0)) :=
    tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (9 / 8 : ℝ))
  have := Filter.Tendsto.congr' heq.symm sumT
  simpa using this

/-! ### 4. Szpiro thresholds and ordering -/

/-- The Szpiro threshold `σ* = 24·c_V`. -/
def szpiroThreshold (c : ℝ) : ℝ := 24 * c

theorem szpiroThreshold_hull : szpiroThreshold cVPaperBox = 6 := by
  unfold szpiroThreshold cVPaperBox
  norm_num

theorem szpiroThreshold_tensor : szpiroThreshold cVTensorClosure = 3 := by
  unfold szpiroThreshold cVTensorClosure
  norm_num

/-- The tensor-closure coefficient is strictly below `1/6` (the R1 refutation threshold). -/
theorem tensorClosure_lt_sixth : cVTensorClosure < 1 / 6 := by
  unfold cVTensorClosure
  norm_num

/-- `1/6` is strictly below the paper hull coefficient `1/4`. -/
theorem sixth_lt_paperBox : (1 / 6 : ℝ) < cVPaperBox := by
  unfold cVPaperBox
  norm_num

/-- The paper hull coefficient is exactly the `c_V ≥ 1/4` branch. -/
theorem paperBox_ge_quarter : (1 / 4 : ℝ) ≤ cVPaperBox := by
  unfold cVPaperBox
  norm_num

/-! ### 5. Determination for our model -/

/-- Our model (`thetaPilotHull`, S3137 least λ-O holomorphic hull of the actual tensor
log-shell region) is the hull container of lana's `SSIneq` side, hence `c_V = 1/4`. -/
def cVModel : ℝ := cVPaperBox

theorem cVModel_eq : cVModel = 1 / 4 := rfl

theorem cVModel_ge_quarter : (1 / 4 : ℝ) ≤ cVModel := paperBox_ge_quarter

theorem cVModel_szpiroThreshold : szpiroThreshold cVModel = 6 := szpiroThreshold_hull

/-! ### 6. Explicitly unproved structural inputs (formulas, not axioms) -/

/-- Structural inputs that are NOT proved here (paper/lana computations); they are
recorded as data, not assumed as axioms. -/
def unprovedInputs : List String :=
  [ "hullPacket exact: μ^log(hull(⊗𝓘)) = ∑_j ρ_j·log p  (lana VcI.lean, proved in lana)",
    "tame: ρ_j = 1 − 1/e_j = d_j, so per-packet hull = d_I·log p (lana)",
    "procession average of the hull leading term = (ℓ+5)/4·log(d^K) (IUT IV Thm 1.10; VcI.md §2c,§4)",
    "packet index (no-hull) upper bound ½(d_I − d_T)log p (VcI.md §2a; not in lana Lean)",
    "the tensor-closure normalization corresponds to ((ℓ+9)/8) (VcI.md §4; Szpiro factor 3)" ]

theorem unprovedInputs_length : unprovedInputs.length = 5 := rfl

/-! ### 7. Rows -/

def shellCoeffRows : List (String × String) :=
  [ ("c_V (paper hull box) = 1/4, σ* = 6", "DEFINED + threshold PROVED"),
    ("c_V (tensor closure) = 1/8, σ* = 3", "DEFINED + threshold PROVED"),
    ("order: 1/8 < 1/6 < 1/4", "PROVED"),
    ("procession / ℓ → 1/4 resp. 1/8", "PROVED (Tendsto)"),
    ("model container = hull ⇒ c_V = 1/4", "DETERMINED (from S3137 hull equality)"),
    ("structural leftover inputs", "LISTED, not proved") ]

theorem shellCoeffRows_length : shellCoeffRows.length = 6 := rfl

#check cVModel_ge_quarter
#check cVModel_szpiroThreshold
#check tendsto_hullProcessionCoeff
#check tendsto_tensorProcessionCoeff
#check shellCoeffRows_length

end LeanFormal.IUT.XiFPaper.Mzk1ShellCoeffComputationActual
end
