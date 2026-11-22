/- absolute conductor/different data（ℤ → O_F; F/ℚ），供 sophie 的 log f_Ftpd 侧。

W := primesOverFinset p (O_F)（p : Ideal ℤ 极大）; e := p.ramificationIdx' P;
f := P.inertiaDeg ℤ; logNv := log|N p|; δ := (normalizedFactors (differentIdeal ℤ (O_F))).count P;
hdelta: e-1 <= δ（Mathlib pow_sub_one_dvd_differentIdeal (A:=ℤ) + count_le_of_ideal_ge）。 -/
import Mathlib.Tactic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Basic
import tmp.sheaf.xif.paper.Mzk1G1ConductorDifferentCancellationCoreActual
import tmp.sheaf.xif.paper.Mzk1HT82AbsDifferentSumActual

noncomputable section
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.Mzk1G1AbsoluteConductorInhabitantActual

open NumberField
open UniqueFactorizationMonoid
open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual

universe u

variable {F : Type u} [Field F] [NumberField F]

/-- e ≥ 1（new ramificationIdx 桥）。 -/
private theorem abs_ram_idx_pos (p : Ideal ℤ) [hpm : p.IsMaximal] (hp : p ≠ ⊥)
    {P : Ideal (𝓞 F)} [hP : P.IsPrime] [hPp : P.LiesOver p] :
    1 ≤ p.ramificationIdx' P := by
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (R := ℤ) (S := 𝓞 F) (p := p) (q := P) hp]
  exact Nat.succ_le_of_lt (Ideal.ramificationIdx_pos (R := ℤ) (q := P))

/-- e-1 <= δ（δ = differentIdeal ℤ (𝓞F) 的 normalizedFactors count）。 -/
theorem absolute_hdelta (p : Ideal ℤ) [hpm : p.IsMaximal] (hp : p ≠ ⊥)
    {P : Ideal (𝓞 F)} [hP : P.IsPrime] [hPp : P.LiesOver p] :
    p.ramificationIdx' P - 1 ≤
      (normalizedFactors (differentIdeal ℤ (𝓞 F))).count P := by
  have hI : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  have hepos : 1 ≤ p.ramificationIdx' P := abs_ram_idx_pos (F := F) p hp (P := P)
  have he : p.ramificationIdx' P ≠ 0 := by omega
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hunder : P.under ℤ = ⊥ := by simp [hbot]
    have hp_eq : p = P.under ℤ := Ideal.LiesOver.over (p := p) (P := P)
    rw [hunder] at hp_eq
    exact hp hp_eq
  have hPmap : P ^ (p.ramificationIdx' P) ∣ (p.map (algebraMap ℤ (𝓞 F))) := by
    rw [Ideal.dvd_iff_le]
    exact Ideal.le_pow_ramificationIdx' (p := p) (P := P)
  have hdiv : P ^ (p.ramificationIdx' P - 1) ∣ differentIdeal ℤ (𝓞 F) :=
    pow_sub_one_dvd_differentIdeal (A := ℤ) (B := 𝓞 F) (p := p) P
      (p.ramificationIdx' P) hp hPmap
  have hle : differentIdeal ℤ (𝓞 F) ≤ P ^ (p.ramificationIdx' P - 1) :=
    Ideal.dvd_iff_le.mp hdiv
  have hcount := Ideal.count_le_of_ideal_ge hle hI P
  have hprime : Prime P := Ideal.prime_of_isPrime hPne hP
  have hnf : normalizedFactors (P ^ (p.ramificationIdx' P - 1)) =
      Multiset.replicate (p.ramificationIdx' P - 1) (normalize P) :=
    hprime.irreducible.normalizedFactors_pow _
  have hnorm : normalize P = P := normalize_eq P
  rw [hnf, hnorm, Multiset.count_replicate_self] at hcount
  exact hcount

/-- absolute conductor 数据（ℤ→𝓞F）。 -/
noncomputable def absoluteConductorData (p : Ideal ℤ) [p.IsMaximal] (hp : p ≠ ⊥)
    [Module.Finite ℤ (𝓞 F)] : LocalConductorDifferentData where
  W := {P : Ideal (𝓞 F) // P ∈ IsDedekindDomain.primesOverFinset p (𝓞 F)}
  fintypeW := Fintype.subtype _ (fun _ => Iff.rfl)
  Ldim := Module.finrank ℚ F
  Ldim_pos := Module.finrank_pos
  e := fun P => p.ramificationIdx' P.1
  e_pos := fun P => abs_ram_idx_pos (F := F) p hp (P := P.1)
  f := fun P => P.1.inertiaDeg ℤ
  logNv := fun _ => Real.log ((Ideal.absNorm p : ℕ) : ℝ)
  logNv_nonneg := fun _ => Real.log_natCast_nonneg _
  differentExponent := fun P => (normalizedFactors (differentIdeal ℤ (𝓞 F))).count P.1

/-- hdelta 到 data。 -/
theorem absoluteConductorData_hdelta (p : Ideal ℤ) [p.IsMaximal] (hp : p ≠ ⊥)
    [Module.Finite ℤ (𝓞 F)] :
    ∀ P : (absoluteConductorData (F := F) p hp).W,
      (absoluteConductorData (F := F) p hp).e P - 1 ≤
        (absoluteConductorData (F := F) p hp).differentExponent P := by
  intro P
  have hmem := P.2
  have hdata := (IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 F) hp).mp hmem
  haveI : P.1.IsPrime := hdata.1
  haveI : P.1.LiesOver p := hdata.2
  exact absolute_hdelta (F := F) p hp (P := P.1)

/-- conductor 差 ≤ different 项。 -/
theorem absoluteConductorData_conductorDifference_le (p : Ideal ℤ) [p.IsMaximal] (hp : p ≠ ⊥)
    [Module.Finite ℤ (𝓞 F)] :
    conductorDifference (absoluteConductorData (F := F) p hp) ≤
      differentTerm (absoluteConductorData (F := F) p hp) :=
  conductorDifference_le_differentTerm _
    (absoluteConductorData_hdelta (F := F) p hp)

end LeanFormal.IUT.XiFPaper.Mzk1G1AbsoluteConductorInhabitantActual