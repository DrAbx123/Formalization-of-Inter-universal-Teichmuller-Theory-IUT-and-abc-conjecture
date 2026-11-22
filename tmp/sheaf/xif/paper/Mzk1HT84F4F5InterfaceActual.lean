/- H-T §8.4: F4/F5 named statements (NO INHABITANT) + structural lemmas.

Provenance (route §8.4; batch1/batch2 of alan's conductor/different cancellation):
* F2/F3 and f2_f3_cancellation: Mzk1G1ConductorDifferentCancellationActual
  (normalizedLogDisc, ConductorDifferentData, F2, F3);
* per-place core: Mzk1G1ConductorDifferentCancellationCoreActual
  (LocalConductorDifferentData, conductorDifference, differentTerm,
   conductorDifference_le_differentTerm, log_natAbs_discr_tower);
* assembly witness (not imported here: its olean is queued):
  Mzk1G1ConductorDifferentCancellationAssemblyActual (F2PlaceWitness, f2_of_witness);
* 8.1 interface: Mzk1HT81InterfaceActual (HT81Interface, HT81LineBundleHeights);
* paper T letter: Mzk1URLabelDataActual.labelTl / Mzk1ULHpktActual.paperLstarLogs.

F4 = conductor/different cancellation with the O(E_i)-height (the 8.4 form of F2+F3).
F5 = log-height comparison of h_{E_i}(y) against h_{O(1)}(y) and the paper T letter
     l*_mod log(s≤) (20/3 coefficient from IUT IV Step (viii) display).
Neither statement has an inhabitant here; they are named route targets. -/
import tmp.sheaf.xif.paper.Mzk1G1ConductorDifferentCancellationActual
import tmp.sheaf.xif.paper.Mzk1G1ConductorDifferentCancellationCoreActual
import tmp.sheaf.xif.paper.Mzk1HT81InterfaceActual
import tmp.sheaf.xif.paper.Mzk1URLabelDataActual
import tmp.sheaf.xif.paper.Mzk1G1RelativeDifferentNormActual
import tmp.sheaf.xif.paper.Mzk1G1PlaceDataActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HT84F4F5InterfaceActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual

/-- H-T §8.4 height data over the 8.1 interface (NO INHABITANT):
h_{E_i}(y) for each i, the paper T letter l*_mod log(s≤), and the two fixed
comparison constants (C for F2/F3, C' for the 8.4 height comparison). -/
structure HT84HeightData (H : LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81Interface) where
  /-- h_{E_i}(y): the O(E_i)-height of y -/
  hEi : H.I → ℝ
  /-- paper T letter: l*_mod log(s≤) -/
  lstar : ℝ
  /-- C: the fixed constant of F2/F3 -/
  C_conductor : ℝ
  /-- C': the fixed constant of the 8.4 height comparison -/
  C_height : ℝ
  lstar_nonneg : 0 ≤ lstar
  C_height_nonneg : 0 ≤ C_height

/-- **F4 (H-T §8.4)**: conductor/different cancellation with the O(E_i)-height.
For every i and every 8.2 conductor data A (with the height/constant identified
with the 8.4 data), D(K_i) + N_D(phi_i(y)) <= D(L) + h_{E_i}(y) + 2 C.
NO INHABITANT: the actual A comes from the 8.1/8.2 construction. -/
def F4Statement (H : LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81Interface)
    (Hh : HT84HeightData H) : Prop :=
  ∀ (i : H.I)
    (A : LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.ConductorDifferentData H i),
    A.heightE = Hh.hEi i → A.constant = Hh.C_conductor →
      normalizedLogDisc (H.K i) + A.conductorAtD ≤
        normalizedLogDisc H.L + Hh.hEi i + 2 * Hh.C_conductor

/-- **F5 (H-T §8.4)**: log-height comparison of the O(E_i)-height against the
O(1)-height and the paper T letter: h_{E_i}(y) <= h_{O(1)}(y) + (20/3)·lstar + C'.
NO INHABITANT. -/
def F5Statement (H : LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81Interface)
    (Hh : HT84HeightData H) : Prop :=
  ∀ i : H.I, Hh.hEi i ≤ H.hO1 H.y + (20 / 3) * Hh.lstar + Hh.C_height

/-- Structural lemma: F2 + F3 (pointwise) imply F4 with the 8.4 height data
(identifying A.heightE with Hh.hEi and A.constant with Hh.C_conductor). -/
theorem f4Statement_of_f2_f3
    (H : LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81Interface)
    (Hh : HT84HeightData H)
    (h2 : ∀ (i : H.I)
      (A : LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.ConductorDifferentData H i),
      LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.F2 H i A)
    (h3 : ∀ (i : H.I)
      (A : LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.ConductorDifferentData H i),
      LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.F3 H i A) :
    F4Statement H Hh := by
  intro i A hheight hconst
  have hF2 := h2 i A
  have hF3 := h3 i A
  simp only [LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.F2,
    LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.F3] at hF2 hF3
  rw [hconst] at hF2
  rw [hconst, hheight] at hF3
  linarith

/-- Structural lemma: F4 + F5 bound the O(1)-height form of the conductor bound:
D(K_i) + N_D(phi_i(y)) <= D(L) + h_{O(1)}(y) + (20/3)·lstar + 2 C + C'. -/
theorem f4_f5_combined
    (H : LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81Interface) (Hh : HT84HeightData H)
    (h4 : F4Statement H Hh) (h5 : F5Statement H Hh) :
    ∀ (i : H.I)
      (A : LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.ConductorDifferentData H i),
      A.heightE = Hh.hEi i → A.constant = Hh.C_conductor →
        normalizedLogDisc (H.K i) + A.conductorAtD ≤
          normalizedLogDisc H.L + H.hO1 H.y + (20 / 3) * Hh.lstar +
            (2 * Hh.C_conductor + Hh.C_height) := by
  intro i A hheight hconst
  have h4i := h4 i A hheight hconst
  have h5i := h5 i
  linarith

/-- F5 with the paper T letter instantiated at labelTl (l*_mod log(s≤));
this is the form consumed by the U-C Step (viii) display. -/
theorem f5Statement_of_labelTl
    (H : LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81Interface)
    (Hh : HT84HeightData H) (eMod : ℕ) (l : ℝ)
    (hstar : Hh.lstar = LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelTl eMod l)
    (h : ∀ i : H.I, Hh.hEi i ≤ H.hO1 H.y + (20 / 3) *
      LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual.labelTl eMod l + Hh.C_height) :
    F5Statement H Hh := by
  intro i
  rw [hstar]
  exact h i


/-! ## F4 的 different / discriminant-tower 形式（消费 alan batch4a） -/

/-- alan 的 1 行 adapter: HT84HeightData 的 hEi 即 HT81LineBundleHeights.hEi。 -/
def HT84HeightData.toLineBundleHeights
    (H : LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81Interface) (Hh : HT84HeightData H) :
    LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81LineBundleHeights H :=
  ⟨Hh.hEi⟩

/-- **F4 的 different 形式（per-index）**: 某 i 的 conductor 差 ≤ differentTerm
+ conductorAtE + C（配 F3 的 cE ≤ hE + C 得 F4 的 2C；differentTerm 来自 alan batch4a）。 -/
def F4DifferentFormAt
    (H : LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81Interface) (Hh : HT84HeightData H)
    (i : H.I) [Algebra (H.K i) H.L] [Module.Finite (𝓞 (H.K i)) (𝓞 H.L)]
    (Rd : LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentNormActual.RelativeDifferentNormData
      (H.K i) H.L)
    (A : LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.ConductorDifferentData H i) :
    Prop :=
  A.heightE = Hh.hEi i → A.constant = Hh.C_conductor →
    A.conductorAtD ≤
      LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual.differentTerm Rd.D +
        A.conductorAtE + Hh.C_conductor

/-- 相对 different 项 ≤ D(L) - D(K)：relative-different norm 恒等（batch4a）
+ 判别式塔公式（batch2 Core）。 -/
theorem differentTerm_le_normalizedLogDisc_sub
    {K : Type u} [Field K] [NumberField K] {L : Type u} [Field L] [NumberField L]
    [Algebra K L] [Module.Finite (𝓞 K) (𝓞 L)]
    (Rd : LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentNormActual.RelativeDifferentNormData K L) :
    LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual.differentTerm Rd.D ≤
      normalizedLogDisc L - normalizedLogDisc K := by
  have h1 := LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentNormActual.differentTerm_le_log_absNorm K L Rd
  have hlog := LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual.log_absNorm_differentIdeal_eq
    (K := K) (L := L)
  have hfL : (Module.finrank ℚ L : ℝ) ≠ 0 := by
    have hpos : 0 < Module.finrank ℚ L := Module.finrank_pos
    exact_mod_cast hpos.ne'
  have hfK : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast hpos.ne'
  have hfinN : Module.finrank K L * Module.finrank ℚ K = Module.finrank ℚ L := by
    simpa [mul_comm] using (Module.finrank_mul_finrank ℚ K L)
  have hfin : (Module.finrank K L : ℝ) * (Module.finrank ℚ K : ℝ) = (Module.finrank ℚ L : ℝ) := by
    rw [← Nat.cast_mul, hfinN]
  have hratio : (Module.finrank K L : ℝ) / (Module.finrank ℚ L : ℝ) =
      1 / (Module.finrank ℚ K : ℝ) := by
    rw [div_eq_div_iff hfL hfK]
    linarith [hfin]
  unfold normalizedLogDisc
  calc LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual.differentTerm Rd.D
      ≤ Real.log ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) /
          (Module.finrank ℚ L : ℝ) := h1
    _ = (Real.log ((discr L).natAbs : ℝ) -
          (Module.finrank K L : ℝ) * Real.log ((discr K).natAbs : ℝ)) /
          (Module.finrank ℚ L : ℝ) := by rw [hlog]
    _ = Real.log ((discr L).natAbs : ℝ) / (Module.finrank ℚ L : ℝ) -
          Real.log ((discr K).natAbs : ℝ) / (Module.finrank ℚ K : ℝ) := by
          rw [sub_div]
          have h2 : (Module.finrank K L : ℝ) * Real.log ((discr K).natAbs : ℝ) /
              (Module.finrank ℚ L : ℝ) =
              Real.log ((discr K).natAbs : ℝ) / (Module.finrank ℚ K : ℝ) := by
            rw [show (Module.finrank K L : ℝ) * Real.log ((discr K).natAbs : ℝ) /
                (Module.finrank ℚ L : ℝ) =
                ((Module.finrank K L : ℝ) / (Module.finrank ℚ L : ℝ)) *
                  Real.log ((discr K).natAbs : ℝ) from by ring, hratio]
            ring
          rw [h2]

/-- F4 的 different 形式（per-index）+ tower 引理 ⇒ F4 的单 index 不等式。 -/
theorem f4Bound_of_f4DifferentFormAt
    (H : LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81Interface) (Hh : HT84HeightData H)
    (i : H.I) [Algebra (H.K i) H.L] [Module.Finite (𝓞 (H.K i)) (𝓞 H.L)]
    (Rd : LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentNormActual.RelativeDifferentNormData
      (H.K i) H.L)
    (A : LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.ConductorDifferentData H i)
    (hheight : A.heightE = Hh.hEi i) (hconst : A.constant = Hh.C_conductor)
    (hF3 : A.conductorAtE ≤ A.heightE + A.constant)
    (hdiff : F4DifferentFormAt H Hh i Rd A) :
    normalizedLogDisc (H.K i) + A.conductorAtD ≤
      normalizedLogDisc H.L + Hh.hEi i + 2 * Hh.C_conductor := by
  have h4 := hdiff hheight hconst
  have hd := differentTerm_le_normalizedLogDisc_sub (K := H.K i) (L := H.L) Rd
  rw [hheight, hconst] at hF3
  linarith


/-! ## route 对齐别名（Lead 命名纠偏, route §8.2/§8.3/§8.4 行号） -/

/-- route-aligned alias: 本文件的 F4Statement 即 route F2+F3
(§8.2 conductor/different 相消 + N_E <= h_E + C, coord route lines 709-800)。 -/
def RouteF2F3Statement (H : LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81Interface)
    (Hh : HT84HeightData H) : Prop := F4Statement H Hh

/-- route-aligned alias: 本文件的 F5Statement 即 route F4
(§8.3 h_{E_i} <= r_i h_{O_Y(1)} + C_i = kappa_i h_omega + C_i 的 8.4 高度形式)。 -/
def RouteF4Statement (H : LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81Interface)
    (Hh : HT84HeightData H) : Prop := F5Statement H Hh

/-- route F2+F3 推出 RouteF2F3Statement（由 f4Statement_of_f2_f3）。 -/
theorem routeF2F3_of_F2_F3
    (H : LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81Interface) (Hh : HT84HeightData H)
    (h2 : ∀ (i : H.I)
      (A : LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.ConductorDifferentData H i),
      LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.F2 H i A)
    (h3 : ∀ (i : H.I)
      (A : LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.ConductorDifferentData H i),
      LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual.F3 H i A) :
    RouteF2F3Statement H Hh :=
  f4Statement_of_f2_f3 H Hh h2 h3

/-- route F4 别名由本文件 F5Statement 直接得到（定义相同）。 -/
theorem routeF4_of_F5Statement
    (H : LeanFormal.IUT.XiFPaper.Mzk1HT81InterfaceActual.HT81Interface) (Hh : HT84HeightData H)
    (h : F5Statement H Hh) : RouteF4Statement H Hh := h

/-! ## (i) route F2 的 placeData 形式（alan batch4b placeData, DONE 17:53:31） -/

/-- route F2 place-数据形式: 用 alan batch4b 的 placeData (W=p.primesOver,
e=ramificationIdx, f=inertiaDeg, logNv=log|N(p)|) 作局部 conductor/different 数据;
配 hdelta (delta >= e-1, provenance LocalDifferentUpperBound/batch4c) 与 tower 输入
hdifferent (differentTerm <= D(L)-D(K), provenance batch2 塔公式 + batch4a norm 恒等),
得 conductor 差 <= D(L)-D(K) (route F2 的 conductor/different 相消核心)。 -/
theorem routeF2_of_placeData
    {K : Type u} [Field K] [NumberField K] {L : Type u} [Field L] [NumberField L]
    [Algebra K L] [Module.Finite (𝓞 K) (𝓞 L)]
    (Kp : LeanFormal.IUT.XiFPaper.Mzk1G1PlaceDataActual.KPlace K)
    (delta : Ideal (𝓞 L) → ℕ)
    (hdelta : ∀ w, (LeanFormal.IUT.XiFPaper.Mzk1G1PlaceDataActual.placeData
        (p := Kp.p) (hp := Kp.p_max) Kp.p_ne_bot delta).e w - 1 ≤
      (LeanFormal.IUT.XiFPaper.Mzk1G1PlaceDataActual.placeData
        (p := Kp.p) (hp := Kp.p_max) Kp.p_ne_bot delta).differentExponent w)
    (hdifferent : LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual.differentTerm
        (LeanFormal.IUT.XiFPaper.Mzk1G1PlaceDataActual.placeData
          (p := Kp.p) (hp := Kp.p_max) Kp.p_ne_bot delta) ≤
      normalizedLogDisc L - normalizedLogDisc K) :
    LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual.conductorDifference
        (LeanFormal.IUT.XiFPaper.Mzk1G1PlaceDataActual.placeData
          (p := Kp.p) (hp := Kp.p_max) Kp.p_ne_bot delta) ≤
      normalizedLogDisc L - normalizedLogDisc K :=
  le_trans
    (LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual.conductorDifference_le_differentTerm
      _ hdelta)
    hdifferent

#print axioms routeF2_of_placeData

#print axioms differentTerm_le_normalizedLogDisc_sub
#print axioms f4Bound_of_f4DifferentFormAt

#print axioms f4Statement_of_f2_f3
#print axioms f4_f5_combined
#print axioms f5Statement_of_labelTl

end LeanFormal.IUT.XiFPaper.Mzk1HT84F4F5InterfaceActual