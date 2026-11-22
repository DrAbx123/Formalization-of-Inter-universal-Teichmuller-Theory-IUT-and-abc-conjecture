/- B3 Y-side wiring (grace): the Cech units of L^{⊗d} = (psi^*O(1))^{⊗d} and the claimed
   phi^*O(1) unit on the refined cover of S7. Consumers: b3_pullbackO1_iso (composes with
   S8's P1 statement O(d) ≅ h^*O(1)) and b3_omegaE_iso (omegaLineBundle + E_phi twist).
   Docstring/consumer notes only; no sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1B3RefinedCoverActual
import tmp.sheaf.xif.paper.Mzk1TwoChartCechLineBundleIsoActual
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
open AlgebraicGeometry CategoryTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B3PhiPullbackUnitActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B3RefinedCoverActual

/-- **L^{⊗d} 的 Čech 线丛**：refined cover 上取 `(refinedLunit)^d`；
    这是 `(psi^*O(1))^{⊗d}` 的单元表示（见 `psiPullbackO1`）。 -/
noncomputable def psiPullbackO1Pow (n : Nat) (T : Finset ℚ) (d : Nat) :
    TwoChartCech.Sections (fermatRefinedCover n T) :=
  (fermatRefinedCover n T).lineBundle (refinedLunit n T ^ d)

/-- **route B3 声称的 φ^*O(1) 过渡单元**：h 侧 coboundary 在 S8 的 P¹ 模型里被吸收，
    于是 φ^*O(1) 的单元 = `(refinedLunit)^d`。`b3_pullbackO1_iso` 将证明对应的
    `SectionsIso`。 -/
noncomputable def phiPullbackO1Unit (n : Nat) (T : Finset ℚ) (d : Nat) :
    (fermatRefinedCover n T).A01ˣ :=
  refinedLunit n T ^ d

theorem phiPullbackO1Unit_def (n : Nat) (T : Finset ℚ) (d : Nat) :
    phiPullbackO1Unit n T d = refinedLunit n T ^ d := rfl

/-- `L^{⊗d}` 线丛的 r0 就是 chart0 的局部化。 -/
theorem psiPullbackO1Pow_r0_apply (n : Nat) (T : Finset ℚ) (d : Nat)
    (p : refinedChart0 n T) :
    (psiPullbackO1Pow n T d).r0 p = (fermatRefinedCover n T).ρ0 p := rfl

/-- `L^{⊗d}` 线丛的 r1 是 `(refinedLunit)^d` 乘 chart-∞ 的局部化。 -/
theorem psiPullbackO1Pow_r1_apply (n : Nat) (T : Finset ℚ) (d : Nat)
    (p : refinedChart1 n T) :
    (psiPullbackO1Pow n T d).r1 p =
      ((refinedLunit n T ^ d : (fermatRefinedCover n T).A01ˣ) :
        (fermatRefinedCover n T).A01) * (fermatRefinedCover n T).ρ1 p := rfl

theorem psiPullbackO1Pow_eq_phiUnit (n : Nat) (T : Finset ℚ) (d : Nat) :
    phiPullbackO1Unit n T d = refinedLunit n T ^ d := rfl

#print axioms psiPullbackO1Pow
#print axioms phiPullbackO1Unit
#print axioms phiPullbackO1Unit_def
#print axioms psiPullbackO1Pow_r1_apply
#print axioms psiPullbackO1Pow_eq_phiUnit

end LeanFormal.IUT.XiFPaper.Mzk1G1B3PhiPullbackUnitActual
