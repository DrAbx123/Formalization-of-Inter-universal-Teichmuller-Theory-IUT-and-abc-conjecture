import tmp.sheaf.xif.paper.Mzk1Ind1PadicUnitActual
import tmp.sheaf.xif.paper.Mzk1Ind1InfiniteDivisibleActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1ZpLatticeDivisibleActual
open LeanFormal.IUT.XiFPaper.Mzk1Ind1InfiniteDivisibleActual

abbrev ZpLattice (p d : Nat) [Fact p.Prime] : Type :=
  Multiplicative (Fin d → ℤ_[p])

theorem zpLattice_infinitelyDivisible {p r d : Nat} [Fact p.Prime]
    (hr : p.Coprime r) (x : ZpLattice p d) :
    InfinitelyDivisibleFor r x := by
  change ∀ n : Nat, ∃ y : ZpLattice p d, y ^ (r ^ n) = x
  intro n
  let k : Nat := r ^ n
  have hu : IsUnit ((k : ℕ) : ℤ_[p]) := by
    simpa [k] using
      (LeanFormal.IUT.XiFPaper.Mzk1Ind1PadicUnitActual.padicInt_isUnit_natCast_pow_of_coprime
        (p := p) (r := r) hr n)
  let uc : ℤ_[p]ˣ := hu.unit
  have huc : (uc : ℤ_[p]) = ((k : ℕ) : ℤ_[p]) := hu.unit_spec
  refine ⟨Multiplicative.ofAdd (fun i => ((uc⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * x.toAdd i), ?_⟩
  apply Multiplicative.toAdd.injective
  ext i
  change k • ((((uc⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * x.toAdd i)) = x.toAdd i
  rw [nsmul_eq_mul]
  rw [← huc, ← mul_assoc, Units.mul_inv, one_mul]

#print axioms zpLattice_infinitelyDivisible
end LeanFormal.IUT.XiFPaper.Mzk1Ind1ZpLatticeDivisibleActual