import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# p-adic decomposition in a finite free Z_p-module

For a finite free module M over the p-adic integers and a nonzero element y : M,
we produce n : Nat and z : M such that y = p ^ n • z and z is not in the
submodule p • top.  This is the additive lattice decomposition used by the
log-shell saturation argument.  No card or placeholder is used.
-/

open scoped BigOperators Pointwise

namespace PadicInt

/-- A nonzero p-adic integer is a power of p times a unit. -/
theorem exists_unit_mul_pow_valuation {p : ℕ} [Fact p.Prime] {c : ℤ_[p]} (hc : c ≠ 0) :
    ∃ (n : ℕ) (u : ℤ_[p]ˣ), c = (p : ℤ_[p]) ^ n * (u : ℤ_[p]) :=
  ⟨c.valuation, unitCoeff hc, (unitCoeff_spec hc).trans (mul_comm _ _)⟩

end PadicInt

/-- In a finite free Z_p-module, every nonzero element is p ^ n times an element
which is not divisible by p. -/
theorem exists_pow_smul_notMem_p_smul_top
    {p : ℕ} [Fact p.Prime] {M : Type*}
    [AddCommGroup M] [Module ℤ_[p] M] [Module.Finite ℤ_[p] M] [Module.Free ℤ_[p] M]
    {y : M} (hy : y ≠ 0) :
    ∃ (n : ℕ) (z : M), y = (p : ℤ_[p]) ^ n • z ∧
      z ∉ (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] M) := by
  classical
  let b : Module.Basis (Module.Free.ChooseBasisIndex ℤ_[p] M) ℤ_[p] M :=
    Module.Free.chooseBasis ℤ_[p] M
  let c : Module.Free.ChooseBasisIndex ℤ_[p] M →₀ ℤ_[p] := b.repr y
  have hc_support : c.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hy
    have hc0 : c = 0 := Finsupp.support_eq_empty.mp h
    have hcy : b.repr.symm c = y := by
      simpa only [c] using b.repr.symm_apply_apply y
    rw [hc0, map_zero] at hcy
    exact hcy.symm
  let v : Module.Free.ChooseBasisIndex ℤ_[p] M → ℕ := fun i => (c i).valuation
  let n : ℕ := (c.support.image v).min' (hc_support.image v)
  have hn_le : ∀ i ∈ c.support, n ≤ v i := by
    intro i hi
    exact Finset.min'_le (c.support.image v) (v i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  obtain ⟨i0, hi0, hv0⟩ : ∃ i0 ∈ c.support, v i0 = n := by
    have hmem : n ∈ c.support.image v := Finset.min'_mem (c.support.image v) (hc_support.image v)
    exact Finset.mem_image.mp hmem
  have hci0 : c i0 ≠ 0 := Finsupp.mem_support_iff.mp hi0
  let u : ℤ_[p]ˣ := PadicInt.unitCoeff hci0
  let d : Module.Free.ChooseBasisIndex ℤ_[p] M → ℤ_[p] := fun i =>
    if h : c i = 0 then 0
    else (PadicInt.unitCoeff h : ℤ_[p]) * (p : ℤ_[p]) ^ (v i - n)
  let z : M := ∑ i, d i • b i
  have hd_coord : ∀ i, c i = (p : ℤ_[p]) ^ n * d i := by
    intro i
    by_cases hi : c i = 0
    · simp [d, hi]
    · have hi_mem : i ∈ c.support := Finsupp.mem_support_iff.mpr hi
      have hle : n ≤ v i := hn_le i hi_mem
      have hspec := PadicInt.unitCoeff_spec hi
      calc c i = (PadicInt.unitCoeff hi : ℤ_[p]) * (p : ℤ_[p]) ^ v i := hspec
        _ = (PadicInt.unitCoeff hi : ℤ_[p]) *
              ((p : ℤ_[p]) ^ n * (p : ℤ_[p]) ^ (v i - n)) := by
              rw [← pow_add, Nat.add_sub_of_le hle]
        _ = (p : ℤ_[p]) ^ n *
              ((PadicInt.unitCoeff hi : ℤ_[p]) * (p : ℤ_[p]) ^ (v i - n)) := by ring
        _ = (p : ℤ_[p]) ^ n * d i := by simp [d, hi]
  have hyz : y = (p : ℤ_[p]) ^ n • z := by
    calc y = ∑ i, c i • b i := (b.sum_repr y).symm
      _ = ∑ i, ((p : ℤ_[p]) ^ n * d i) • b i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hd_coord i]
      _ = ∑ i, (p : ℤ_[p]) ^ n • (d i • b i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [mul_smul]
      _ = (p : ℤ_[p]) ^ n • ∑ i, d i • b i := by
            rw [← Finset.smul_sum]
      _ = (p : ℤ_[p]) ^ n • z := rfl
  refine ⟨n, z, hyz, ?_⟩
  intro hz
  have hz' : ∃ w ∈ (⊤ : Submodule ℤ_[p] M), (p : ℤ_[p]) • w = z :=
    (Submodule.mem_smul_pointwise_iff_exists z (p : ℤ_[p]) (⊤ : Submodule ℤ_[p] M)).mp hz
  obtain ⟨w, -, hw⟩ := hz'
  have hrepr : (⇑(b.repr z) : Module.Free.ChooseBasisIndex ℤ_[p] M → ℤ_[p]) = d := by
    simpa [z] using Module.Basis.repr_sum_self b d
  have hzcoord : b.repr z i0 = (u : ℤ_[p]) := by
    rw [show b.repr z i0 = d i0 from congrFun hrepr i0]
    simp [d, hci0, u, hv0]
  have hwcoord : b.repr z i0 = (p : ℤ_[p]) * b.repr w i0 := by
    have := congrArg (fun t => b.repr t i0) hw.symm
    simpa using this
  have hdvd : (p : ℤ_[p]) ∣ (u : ℤ_[p]) :=
    ⟨b.repr w i0, hzcoord.symm.trans hwcoord⟩
  exact PadicInt.prime_p.not_unit (isUnit_of_dvd_unit hdvd u.isUnit)
