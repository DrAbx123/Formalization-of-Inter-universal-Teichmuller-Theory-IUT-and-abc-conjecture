/- (A) LocalConductorDifferentData 实际 inhabitant（F→K 相对 different/conductor 数据）。

paper: IUT IV Prop 1.3 (i),(ii) 的局部不同/导子比较; 本文件只给 inhabitant + 非负/求和事实，
不宣称全局 hlogK（那需要 Prop1.3(ii) 的全局组装，见后续 batch）。

W := primesOverFinset (p) (O_K)（p 为 O_F 的极大理想）; e := ramificationIdx' p P;
f := inertiaDeg (O_F); logNv := log|N p|; differentExponent := batch4d 的
differentExponent (K:=F)(L:=K)（= normalizedFactors count）。
hdelta: e-1 <= differentExponent 来自 Mzk1G1F7DifferentExponentBoundsActual
+ Mathlib le_pow_ramificationIdx'. -/
import Mathlib.Tactic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import tmp.sheaf.xif.paper.Mzk1G1ConductorDifferentCancellationCoreActual
import tmp.sheaf.xif.paper.Mzk1G1RelativeDifferentLogActual
import tmp.sheaf.xif.paper.Mzk1G1F7DifferentExponentBoundsActual

noncomputable section
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.Mzk1G1LocalConductorInhabitantActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentLogActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F7DifferentExponentBoundsActual

universe u

variable {F : Type u} [Field F] [NumberField F]
variable {K : Type u} [Field K] [NumberField K] [Algebra F K]

private theorem mem_data {p : Ideal (𝓞 F)} [p.IsMaximal] (hp : p ≠ ⊥)
    {P : Ideal (𝓞 K)} (hP : P ∈ IsDedekindDomain.primesOverFinset p (𝓞 K)) :
    P.IsPrime ∧ P.LiesOver p := by
  exact (IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) hp).mp hP

/-- P 在极大 p 上 ⇒ 1 ≤ ramificationIdx' p P（经 new ramificationIdx 桥）。 -/
private theorem ram_idx_pos {p : Ideal (𝓞 F)} [hpm : p.IsMaximal] (hp : p ≠ ⊥)
    {P : Ideal (𝓞 K)} [hP : P.IsPrime] [hPp : P.LiesOver p]
    [Module.Finite (𝓞 F) (𝓞 K)] [Module.IsTorsionFree (𝓞 F) (𝓞 K)] :
    1 ≤ p.ramificationIdx' P := by
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (R := 𝓞 F) (S := 𝓞 K)
    (p := p) (q := P) hp]
  exact Nat.succ_le_of_lt (Ideal.ramificationIdx_pos (R := 𝓞 F) (q := P))

noncomputable def localConductorData (p : Ideal (𝓞 F)) [p.IsMaximal] (hp : p ≠ ⊥)
    [Module.Finite (𝓞 F) (𝓞 K)] : LocalConductorDifferentData where
  W := {P : Ideal (𝓞 K) // P ∈ IsDedekindDomain.primesOverFinset p (𝓞 K)}
  fintypeW := Fintype.subtype _ (fun _ => Iff.rfl)
  Ldim := Module.finrank ℚ K
  Ldim_pos := Module.finrank_pos
  e := fun P => (P.1.under (𝓞 F)).ramificationIdx' P.1
  e_pos := fun P => by
    have hP := mem_data (F := F) (K := K) hp P.2
    haveI : P.1.IsPrime := hP.1
    haveI : P.1.LiesOver p := hP.2
    have hpu : P.1.under (𝓞 F) = p :=
      (Ideal.LiesOver.over (p := p) (P := P.1)).symm
    simpa [hpu] using ram_idx_pos (F := F) (K := K) (p := p) hp (P := P.1)
  f := fun P => by
    have hP := mem_data (F := F) (K := K) hp P.2
    haveI : P.1.IsPrime := hP.1
    exact P.1.inertiaDeg (𝓞 F)
  logNv := fun _ => Real.log ((Ideal.absNorm p : ℕ) : ℝ)
  logNv_nonneg := fun _ => Real.log_natCast_nonneg _
  differentExponent := fun P => differentExponent (K := F) (L := K) P.1

theorem localConductorData_hdelta (p : Ideal (𝓞 F)) [p.IsMaximal] (hp : p ≠ ⊥)
    [Module.Finite (𝓞 F) (𝓞 K)] :
    ∀ P : (localConductorData (F := F) (K := K) p hp).W,
      (localConductorData (F := F) (K := K) p hp).e P - 1 ≤
        (localConductorData (F := F) (K := K) p hp).differentExponent P := by
  intro P
  have hP := mem_data (F := F) (K := K) hp P.2
  haveI : P.1.IsPrime := hP.1
  haveI : P.1.LiesOver p := hP.2
  have hpu0 : P.1.under (𝓞 F) = p :=
    (Ideal.LiesOver.over (p := p) (P := P.1)).symm
  have hepos : 1 ≤ (P.1.under (𝓞 F)).ramificationIdx' P.1 := by
    simpa [hpu0] using ram_idx_pos (F := F) (K := K) (p := p) hp (P := P.1)
  have he : (P.1.under (𝓞 F)).ramificationIdx' P.1 ≠ 0 := by omega
  have hpu : P.1.under (𝓞 F) = p :=
    (Ideal.LiesOver.over (p := p) (P := P.1)).symm
  have hpu_ne : P.1.under (𝓞 F) ≠ ⊥ := by
    rw [hpu]; exact hp
  have hmap : P.1 ^ (P.1.under (𝓞 F)).ramificationIdx' P.1 ∣
      (P.1.under (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 K)) := by
    rw [Ideal.dvd_iff_le]
    exact Ideal.le_pow_ramificationIdx' (p := P.1.under (𝓞 F)) (P := P.1)
  have hPne : P.1 ≠ ⊥ := by
    intro hbot
    have hunder : P.1.under (𝓞 F) = ⊥ := by simp [hbot]
    exact hp (by rw [← hpu]; exact hunder)
  show (localConductorData (F := F) (K := K) p hp).e P - 1 ≤
    (localConductorData (F := F) (K := K) p hp).differentExponent P
  exact differentExponent_ge_ramification_sub_one (K := F) (L := K) P.1 hPne he hpu_ne hmap


/-- 该 data 的 conductor 差 ≤ different 项（用 hdelta）。 -/
theorem localConductorData_conductorDifference_le (p : Ideal (𝓞 F)) [p.IsMaximal] (hp : p ≠ ⊥)
    [Module.Finite (𝓞 F) (𝓞 K)] :
    conductorDifference (localConductorData (F := F) (K := K) p hp) ≤
      differentTerm (localConductorData (F := F) (K := K) p hp) :=
  conductorDifference_le_differentTerm _
    (localConductorData_hdelta (F := F) (K := K) p hp)

#print axioms localConductorData_conductorDifference_le

end LeanFormal.IUT.XiFPaper.Mzk1G1LocalConductorInhabitantActual