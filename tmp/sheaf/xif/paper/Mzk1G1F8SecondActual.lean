/-
F8 second equality in the two-chart Cech model (route §8.6, L838-848).

`Mzk1G1F8PiActual` proves the first equality
`h(pi(y)) = n * h_{O_Y(1)}(y) + O(log 2)` on chart-0 data.  The second
equality `h(pi(y)) = n/(n-3) * h_{omega_Y}(y) + O(1)` is, at the level of the
two-chart Cech data of `Mzk1G1A5LineBundleIsoActual`, the statement that the
transition unit of `omega_Y` is `u0^(n-3)` while the transition unit of
`pi^* O(1)` is `u0^n`.

This file isolates that layer and proves it unconditionally:

* the transition units `transitionUnit`, `lineBundleEUnit`, `pullbackO1Unit` are the
  units `u0^(n-3)`, `u0^3`, `u0^n` of the overlap ring `O0 n` (unit-level
  exponent formulas);
* a structure `CechUnit` certifies a line-bundle transition unit together with its
  Cech degree (the exponent of `u0`); degrees are additive, and the A5 unit
  identity is an identity of certified Cech units with degrees `(n-3) + 3 = n`;
* honest `H0` frames for the two line bundles are produced as
  `F1HeightTransportData` (frame `(x0^(n-3), 1)` for `omega_Y`, frame
  `(x0^n, 1)` for `pi^* O(1)`), so the frame heights below are heights of
  actual H0 sections;
* `Height.logHeight₁` of the H0-frame values gives
  `h_{omega_Y} = (n-3) * h_{O_Y(1)}` and `h_{pi^*O(1)} = n * h_{O_Y(1)}`, hence
  `h(pi(y)) = n/(n-3) * h_{omega_Y}(y)` as an exact identity of Cech-frame heights.

What is *not* proved here (and is not available in the Cech model): the comparison of
these frame heights with an Arakelov/divisor height of the actual line bundles on the
scheme `Y_n`.  That comparison is precisely where the `O(1)` of the paper
comes from; the frame-level identity below is the exact part of F8's second equality.
-/
import tmp.sheaf.xif.paper.Mzk1G1OmegaLineBundleActual
import tmp.sheaf.xif.paper.Mzk1G1A5LineBundleIsoActual
import tmp.sheaf.xif.paper.Mzk1G1F1HeightTransportActual
import tmp.sheaf.xif.paper.Mzk1G1F8PiActual
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1G1F8SecondActual

open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaTransitionGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A5LineBundleIsoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F1HeightTransportActual
open LeanFormal.IUT.XiFPaper.F8PiActual

/-! ## 1. The unit `u0` and its integer powers -/

/-- `u0` as a unit of the Fermat overlap ring `O0 n`. -/
noncomputable def u0Unit (n : ℕ) : (O0 n)ˣ := (u0_isUnit n).unit

theorem u0Unit_val (n : ℕ) : ((u0Unit n : (O0 n)ˣ) : O0 n) = u0 n := rfl

/-- The unit `u0 ^ k` of the overlap ring, for an integer exponent `k`. -/
noncomputable def u0ZPow (n : ℕ) (k : ℤ) : (O0 n)ˣ := u0Unit n ^ k

theorem u0ZPow_add (n : ℕ) (k l : ℤ) :
    u0ZPow n (k + l) = u0ZPow n k * u0ZPow n l :=
  zpow_add (u0Unit n) k l

/-! ## 2. The explicit `u0`-power formulas for the line-bundle units -/

/-- The canonical-bundle transition unit is `u0^(n-3)` (route A3). -/
theorem transitionUnit_eq_u0Unit_pow (n : ℕ) :
    transitionUnit n = u0Unit n ^ (n - 3) :=
  IsUnit.unit_pow (u0_isUnit n) (n - 3)

/-- The `O(E) = O(3)` transition unit is `u0^3`. -/
theorem lineBundleEUnit_eq_u0Unit_pow (n : ℕ) :
    lineBundleEUnit n = u0Unit n ^ 3 :=
  IsUnit.unit_pow (u0_isUnit n) 3

/-- The `pi^* O(1)` transition unit is `u0^n`. -/
theorem pullbackO1Unit_eq_u0Unit_pow (n : ℕ) :
    pullbackO1Unit n = u0Unit n ^ n :=
  IsUnit.unit_pow (u0_isUnit n) n

/-- The transition unit of `omega_Y(E)` is `u0^n` for `n >= 3`,
by A5 (`omega_Y(E) = pi^* omega_{P^1}`). -/
theorem omegaYEUnit_eq_u0Unit_pow (n : ℕ) (hn : 3 ≤ n) :
    omegaYEUnit n = u0Unit n ^ n := by
  rw [omegaYEUnit_eq_pullbackUnit n hn, pullbackOmegaP1Unit,
    pullbackO1Unit_eq_u0Unit_pow]

/-! ## 3. Cech degrees of line-bundle transition units -/

/-- A two-chart Cech line-bundle transition unit together with a certificate that it is
the `degree`-th power of `u0`.  On the Fermat overlap every line bundle
occurring in the A3/A5 data is of this form, and `degree` is its Cech degree. -/
structure CechUnit (n : ℕ) where
  /-- The underlying transition unit on the overlap. -/
  unit : (O0 n)ˣ
  /-- The Cech degree, i.e. the exponent of `u0`. -/
  degree : ℤ
  /-- The certification `unit = u0 ^ degree`. -/
  eq_u0_zpow : unit = u0ZPow n degree

/-- The product of two certified Cech units has the sum of the degrees. -/
instance instCechUnitMul {n : ℕ} : Mul (CechUnit n) where
  mul u v :=
    { unit := u.unit * v.unit
      degree := u.degree + v.degree
      eq_u0_zpow := by
        rw [u.eq_u0_zpow, v.eq_u0_zpow, ← u0ZPow_add] }

@[simp] theorem CechUnit.mul_unit {n : ℕ} (u v : CechUnit n) :
    (u * v).unit = u.unit * v.unit := rfl

@[simp] theorem CechUnit.mul_degree {n : ℕ} (u v : CechUnit n) :
    (u * v).degree = u.degree + v.degree := rfl

/-- Two certified Cech units with the same underlying unit and the same degree are equal. -/
theorem CechUnit.eq_of_unit_degree {n : ℕ} {u v : CechUnit n}
    (h1 : u.unit = v.unit) (h2 : u.degree = v.degree) : u = v := by
  obtain ⟨u1, d1, p1⟩ := u
  obtain ⟨u2, d2, p2⟩ := v
  simp only at h1 h2
  cases h1
  cases h2
  rfl

/-- The canonical line bundle `omega_Y = O(n-3)`: Cech degree `n-3`. -/
noncomputable def transitionCechUnit (n : ℕ) : CechUnit n where
  unit := transitionUnit n
  degree := ((n - 3 : ℕ) : ℤ)
  eq_u0_zpow := by
    rw [transitionUnit_eq_u0Unit_pow]
    exact (zpow_natCast (u0Unit n) (n - 3)).symm

/-- The `O(E) = O(3)` line bundle: Cech degree `3`. -/
noncomputable def lineBundleECechUnit (n : ℕ) : CechUnit n where
  unit := lineBundleEUnit n
  degree := 3
  eq_u0_zpow := by
    rw [lineBundleEUnit_eq_u0Unit_pow]
    exact (zpow_natCast (u0Unit n) 3).symm

/-- The pullback `pi^* omega_{P^1}(0+1+infty)`: Cech degree `n`. -/
noncomputable def pullbackOmegaP1CechUnit (n : ℕ) : CechUnit n where
  unit := pullbackOmegaP1Unit n
  degree := (n : ℤ)
  eq_u0_zpow := by
    rw [pullbackOmegaP1Unit, pullbackO1Unit_eq_u0Unit_pow]
    exact (zpow_natCast (u0Unit n) n).symm

/-- The line bundle `omega_Y(E)`: the same certified unit as the A5 pullback. -/
noncomputable def omegaYECechUnit (n : ℕ) (hn : 3 ≤ n) : CechUnit n where
  unit := omegaYEUnit n
  degree := (n : ℤ)
  eq_u0_zpow := by
    rw [omegaYEUnit_eq_u0Unit_pow n hn]
    exact (zpow_natCast (u0Unit n) n).symm

@[simp] theorem transitionCechUnit_degree (n : ℕ) :
    (transitionCechUnit n).degree = ((n - 3 : ℕ) : ℤ) := rfl

@[simp] theorem lineBundleECechUnit_degree (n : ℕ) :
    (lineBundleECechUnit n).degree = 3 := rfl

@[simp] theorem pullbackOmegaP1CechUnit_degree (n : ℕ) :
    (pullbackOmegaP1CechUnit n).degree = (n : ℤ) := rfl

@[simp] theorem omegaYECechUnit_degree (n : ℕ) (hn : 3 ≤ n) :
    (omegaYECechUnit n hn).degree = (n : ℤ) := rfl

/-- A5 at the level of certified Cech units: the underlying units of
`omega_Y tensor O(E)` and `pi^* omega_{P^1}(0+1+infty)` agree. -/
theorem cechUnit_mul_transition_E_unit (n : ℕ) (hn : 3 ≤ n) :
    (transitionCechUnit n * lineBundleECechUnit n).unit
      = (pullbackOmegaP1CechUnit n).unit :=
  Units.ext (a5_transition_unit n hn)

/-- A5 at the level of Cech degrees: `(n-3) + 3 = n`. -/
theorem cechUnit_mul_transition_E_degree (n : ℕ) (hn : 3 ≤ n) :
    (transitionCechUnit n * lineBundleECechUnit n).degree
      = (pullbackOmegaP1CechUnit n).degree := by
  simp only [CechUnit.mul_degree, transitionCechUnit_degree,
    lineBundleECechUnit_degree, pullbackOmegaP1CechUnit_degree]
  omega

/-- A5 as an identity of certified Cech units. -/
theorem cechUnit_mul_transition_E (n : ℕ) (hn : 3 ≤ n) :
    transitionCechUnit n * lineBundleECechUnit n = pullbackOmegaP1CechUnit n :=
  CechUnit.eq_of_unit_degree (cechUnit_mul_transition_E_unit n hn)
    (cechUnit_mul_transition_E_degree n hn)

/-- The underlying unit of `omega_Y(E)` is the A5 pullback unit. -/
theorem omegaYECechUnit_unit (n : ℕ) (hn : 3 ≤ n) :
    (omegaYECechUnit n hn).unit = (pullbackOmegaP1CechUnit n).unit :=
  omegaYEUnit_eq_pullbackUnit n hn

/-- The Cech degree of `omega_Y(E)` is `n`, the degree of the pullback. -/
theorem omegaYECechUnit_degree_eq_pullback (n : ℕ) (hn : 3 ≤ n) :
    (omegaYECechUnit n hn).degree = (pullbackOmegaP1CechUnit n).degree := by
  simp only [omegaYECechUnit_degree, pullbackOmegaP1CechUnit_degree]

/-- `omega_Y(E)` and the A5 pullback are equal certified Cech units. -/
theorem omegaYECechUnit_eq_pullback (n : ℕ) (hn : 3 ≤ n) :
    omegaYECechUnit n hn = pullbackOmegaP1CechUnit n :=
  CechUnit.eq_of_unit_degree (omegaYECechUnit_unit n hn)
    (omegaYECechUnit_degree_eq_pullback n hn)

/-- `omega_Y(E)` decomposes as `omega_Y` times `O(E)` at the level of
certified Cech units (degrees add: `(n-3) + 3 = n`). -/
theorem omegaYECechUnit_eq_mul (n : ℕ) (hn : 3 ≤ n) :
    omegaYECechUnit n hn = transitionCechUnit n * lineBundleECechUnit n :=
  CechUnit.eq_of_unit_degree
    (by
      show omegaYEUnit n = transitionUnit n * lineBundleEUnit n
      rfl)
    (by
      simp only [omegaYECechUnit_degree, CechUnit.mul_degree,
        transitionCechUnit_degree, lineBundleECechUnit_degree]
      omega)

/-! ## 4. H0 frames for `omega_Y` and `pi^* O(1)` -/

/-- The H0 frame of `omega_Y = O(n-3)` on the canonical cover: `x0^(n-3)` on
chart 0 and `1` on chart 1 (the transition unit is `u0^(n-3)`). -/
noncomputable def omegaYF1Data (n : ℕ) : F1HeightTransportData n where
  cover := canonicalCover n
  transitionUnit := transitionUnit n
  frame0 := x0 n ^ (n - 3)
  frame1 := 1
  frame_compat := by
    show (algebraMap (B n) (O0 n)) (x0 n ^ (n - 3))
      = (transitionUnit n : O0 n) * (algebraMap (B n) (O0 n)) (1 : B n)
    rw [map_pow, map_one, mul_one, transitionUnit_spec, u0_def]

/-- The H0 frame of `pi^* O(1)` on the canonical cover: `x0^n` on chart 0
and `1` on chart 1 (the transition unit is `u0^n`). -/
noncomputable def pullbackO1F1Data (n : ℕ) : F1HeightTransportData n where
  cover := canonicalCover n
  transitionUnit := pullbackO1Unit n
  frame0 := x0 n ^ n
  frame1 := 1
  frame_compat := by
    show (algebraMap (B n) (O0 n)) (x0 n ^ n)
      = (pullbackO1Unit n : O0 n) * (algebraMap (B n) (O0 n)) (1 : B n)
    rw [map_pow, map_one, mul_one, pullbackO1Unit_spec, u0_def]

/-- The frame `(x0^(n-3), 1)` is an actual H0 section of `omega_Y`. -/
theorem omegaYF1Data_mem_H0 (n : ℕ) :
    ((omegaYF1Data n).frame0, (omegaYF1Data n).frame1) ∈
      ((omegaYF1Data n).cover.lineBundle (omegaYF1Data n).transitionUnit).H0 :=
  (f1_frame_mem_H0 n (omegaYF1Data n)).mpr (omegaYF1Data n).frame_compat

/-- The frame `(x0^n, 1)` is an actual H0 section of `pi^* O(1)`. -/
theorem pullbackO1F1Data_mem_H0 (n : ℕ) :
    ((pullbackO1F1Data n).frame0, (pullbackO1F1Data n).frame1) ∈
      ((pullbackO1F1Data n).cover.lineBundle (pullbackO1F1Data n).transitionUnit).H0 :=
  (f1_frame_mem_H0 n (pullbackO1F1Data n)).mpr (pullbackO1F1Data n).frame_compat

/-- The `omega_Y` H0 frame value at a chart-0 point is `(phi x0)^(n-3)`. -/
theorem omegaYF1Data_frame0_value {k : Type*} [CommRing k] (n : ℕ)
    (φ : Chart0Ring n →+* k) :
    φ ((omegaYF1Data n).frame0) = (φ (x0 n)) ^ (n - 3) := by
  show φ (x0 n ^ (n - 3)) = (φ (x0 n)) ^ (n - 3)
  rw [map_pow]

/-- The `pi^* O(1)` H0 frame value at a chart-0 point is `(phi x0)^n`. -/
theorem pullbackO1F1Data_frame0_value {k : Type*} [CommRing k] (n : ℕ)
    (φ : Chart0Ring n →+* k) :
    φ ((pullbackO1F1Data n).frame0) = (φ (x0 n)) ^ n := by
  show φ (x0 n ^ n) = (φ (x0 n)) ^ n
  rw [map_pow]

/-- Height of the `omega_Y` H0 frame at a chart-0 point: `(n-3) * h(phi x0)`. -/
theorem omegaYF1Data_frame0_height {k : Type*} [Field k] [NumberField k] (n : ℕ)
    (φ : Chart0Ring n →+* k) :
    Height.logHeight₁ (φ ((omegaYF1Data n).frame0))
      = ((n - 3 : ℕ) : ℝ) * Height.logHeight₁ (φ (x0 n)) := by
  rw [omegaYF1Data_frame0_value, Height.logHeight₁_pow]

/-! ## 5. Cech-frame heights and the F8 second equality -/

section Heights

variable {k : Type*} [Field k] [NumberField k]

/-- The height of the Cech frame value of a line-bundle unit at a `K`-point `Phi`
of the overlap ring: `logHeight₁ (Phi u)`. -/
noncomputable def frameHeight (n : ℕ) (Φ : O0 n →+* k) (u : (O0 n)ˣ) : ℝ :=
  Height.logHeight₁ (Φ (u : O0 n))

/-- The `omega_Y` frame height is `(n-3)` times the `O_Y(1)` height. -/
theorem frameHeight_transitionUnit (n : ℕ) (Φ : O0 n →+* k) :
    frameHeight n Φ (transitionUnit n)
      = ((n - 3 : ℕ) : ℝ) * Height.logHeight₁ (Φ (u0 n)) := by
  rw [frameHeight, transitionUnit_spec, map_pow, Height.logHeight₁_pow]

/-- The `O(E)` frame height is `3` times the `O_Y(1)` height. -/
theorem frameHeight_lineBundleEUnit (n : ℕ) (Φ : O0 n →+* k) :
    frameHeight n Φ (lineBundleEUnit n) = 3 * Height.logHeight₁ (Φ (u0 n)) := by
  rw [frameHeight, lineBundleEUnit_spec, map_pow, Height.logHeight₁_pow]
  norm_num

/-- The `pi^* O(1)` frame height is `n` times the `O_Y(1)` height. -/
theorem frameHeight_pullbackO1Unit (n : ℕ) (Φ : O0 n →+* k) :
    frameHeight n Φ (pullbackO1Unit n) = (n : ℝ) * Height.logHeight₁ (Φ (u0 n)) := by
  rw [frameHeight, pullbackO1Unit_spec, map_pow, Height.logHeight₁_pow]

/-- The `omega_Y(E)` frame height is `n` times the `O_Y(1)` height. -/
theorem frameHeight_omegaYEUnit (n : ℕ) (hn : 3 ≤ n) (Φ : O0 n →+* k) :
    frameHeight n Φ (omegaYEUnit n) = (n : ℝ) * Height.logHeight₁ (Φ (u0 n)) := by
  rw [frameHeight, omegaYEUnit_eq_pullbackUnit n hn, pullbackOmegaP1Unit]
  exact frameHeight_pullbackO1Unit n Φ

/-- The arithmetic core of F8's second equality: `n/(n-3) * (n-3) = n`. -/
theorem n_div_n_sub_three_mul (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℝ) / ((n : ℝ) - 3)) * ((n : ℝ) - 3) = (n : ℝ) := by
  have h3 : (n : ℝ) - 3 ≠ 0 := by
    have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact div_mul_cancel₀ (n : ℝ) h3

/-- **F8 second equality at the level of the two-chart Cech units.**  The height of the
`pi^* O(1)` frame is `n/(n-3)` times the height of the `omega_Y` frame,
for every `K`-point of the overlap ring and every `n >= 4`. -/
theorem f8_second_equality_frame (n : ℕ) (hn : 4 ≤ n) (Φ : O0 n →+* k) :
    frameHeight n Φ (pullbackO1Unit n)
      = ((n : ℝ) / ((n : ℝ) - 3)) * frameHeight n Φ (transitionUnit n) := by
  have hcast : ((n - 3 : ℕ) : ℝ) = (n : ℝ) - 3 := by
    rw [Nat.cast_sub (show 3 ≤ n by omega)]
    push_cast
    ring
  have h3 : (n : ℝ) - 3 ≠ 0 := by
    have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [frameHeight_pullbackO1Unit, frameHeight_transitionUnit, ← mul_assoc, hcast,
    div_mul_cancel₀ _ h3]

/-- **F8 second equality, chart-0 coordinate form.**  For a chart-0 `K`-point, the
height of `(phi x0)^n` (the value of the `pi^*O(1)` frame, equal to `h(pi(y))`
by `f8_pi_height_chart0`) is `n/(n-3)` times the height of the `omega_Y` frame
value `(phi x0)^(n-3)`. -/
theorem f8_second_equality_chart0 (n : ℕ) (hn : 4 ≤ n) (φ : Chart0Ring n →+* k) :
    Height.logHeight₁ ((φ (x0 n)) ^ n)
      = ((n : ℝ) / ((n : ℝ) - 3)) * Height.logHeight₁ ((φ (x0 n)) ^ (n - 3)) := by
  have hcast : ((n - 3 : ℕ) : ℝ) = (n : ℝ) - 3 := by
    rw [Nat.cast_sub (show 3 ≤ n by omega)]
    push_cast
    ring
  have h3 : (n : ℝ) - 3 ≠ 0 := by
    have h4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [Height.logHeight₁_pow, Height.logHeight₁_pow, ← mul_assoc, hcast,
    div_mul_cancel₀ _ h3]

/-- **F8 second equality with the actual H0 frames.**  The height of the `pi^*O(1)` H0
frame equals `n/(n-3)` times the height of the `omega_Y` H0 frame. -/
theorem f8_second_equality_H0frame (n : ℕ) (hn : 4 ≤ n) (φ : Chart0Ring n →+* k) :
    Height.logHeight₁ (φ ((pullbackO1F1Data n).frame0))
      = ((n : ℝ) / ((n : ℝ) - 3))
          * Height.logHeight₁ (φ ((omegaYF1Data n).frame0)) := by
  rw [pullbackO1F1Data_frame0_value, omegaYF1Data_frame0_value]
  exact f8_second_equality_chart0 n hn φ

/-- **F8 second equality in the interface of the first equality**: the chart-0 height of
`pi(y)` (namely `p1ChartHeight ((phi x0)^n)`) equals `n/(n-3)` times the
`omega_Y` frame height. -/
theorem f8_second_equality_p1ChartHeight (n : ℕ) (hn : 4 ≤ n) (φ : Chart0Ring n →+* k) :
    p1ChartHeight ((φ (x0 n)) ^ n)
      = ((n : ℝ) / ((n : ℝ) - 3)) *
          Height.logHeight₁ ((φ (x0 n)) ^ (n - 3)) :=
  f8_second_equality_chart0 n hn φ

end Heights

/-! ## 6. Bridge from chart-0 points to the Cech frame values -/

section ChartPoints

variable {k : Type*} [Field k]

/-- The `K`-point of the overlap ring induced by a chart-0 point whose `x0`-coordinate
is invertible (the non-boundary chart-0 points). -/
noncomputable def chart0ToOverlap (n : ℕ) (φ : Chart0Ring n →+* k)
    (hφ : IsUnit (φ (x0 n))) : O0 n →+* k :=
  IsLocalization.Away.lift (S := O0 n) (x0 n) (g := φ) hφ

theorem chart0ToOverlap_u0 (n : ℕ) (φ : Chart0Ring n →+* k)
    (hφ : IsUnit (φ (x0 n))) :
    chart0ToOverlap n φ hφ (u0 n) = φ (x0 n) := by
  simp [chart0ToOverlap, u0_def]

/-- The `omega_Y` Cech frame value at a chart-0 point is `(phi x0)^(n-3)`. -/
theorem chart0ToOverlap_transitionUnit (n : ℕ) (φ : Chart0Ring n →+* k)
    (hφ : IsUnit (φ (x0 n))) :
    chart0ToOverlap n φ hφ (transitionUnit n : O0 n) = (φ (x0 n)) ^ (n - 3) := by
  rw [transitionUnit_spec, map_pow, chart0ToOverlap_u0]

/-- The `pi^* O(1)` Cech frame value at a chart-0 point is `(phi x0)^n`. -/
theorem chart0ToOverlap_pullbackO1Unit (n : ℕ) (φ : Chart0Ring n →+* k)
    (hφ : IsUnit (φ (x0 n))) :
    chart0ToOverlap n φ hφ (pullbackO1Unit n : O0 n) = (φ (x0 n)) ^ n := by
  rw [pullbackO1Unit_spec, map_pow, chart0ToOverlap_u0]

end ChartPoints

#print axioms u0ZPow_add
#print axioms transitionUnit_eq_u0Unit_pow
#print axioms lineBundleEUnit_eq_u0Unit_pow
#print axioms pullbackO1Unit_eq_u0Unit_pow
#print axioms omegaYEUnit_eq_u0Unit_pow
#print axioms CechUnit.eq_of_unit_degree
#print axioms cechUnit_mul_transition_E
#print axioms omegaYECechUnit_eq_pullback
#print axioms omegaYECechUnit_eq_mul
#print axioms omegaYF1Data_mem_H0
#print axioms pullbackO1F1Data_mem_H0
#print axioms omegaYF1Data_frame0_height
#print axioms frameHeight_transitionUnit
#print axioms frameHeight_lineBundleEUnit
#print axioms frameHeight_pullbackO1Unit
#print axioms frameHeight_omegaYEUnit
#print axioms n_div_n_sub_three_mul
#print axioms f8_second_equality_frame
#print axioms f8_second_equality_chart0
#print axioms f8_second_equality_H0frame
#print axioms f8_second_equality_p1ChartHeight
#print axioms chart0ToOverlap_transitionUnit
#print axioms chart0ToOverlap_pullbackO1Unit

end LeanFormal.IUT.XiFPaper.Mzk1G1F8SecondActual
