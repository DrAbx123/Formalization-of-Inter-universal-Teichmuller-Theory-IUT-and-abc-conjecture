import tmp.sheaf.xif.paper.EtTh11ThetaRealizationRowsActual

/-!
# Mzk1EtTh11DerivedActual — derived monotonicity inequalities for the EtTh theta/elliptic
power kernels (new theorems from the existing EtTh11 asset; no copies/bookkeeping).
No axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1EtTh11DerivedActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.EtTh11ThetaRealizationRowsActual

universe u

/-- Derived: the level (l1*l2) theta power kernel sits inside the level-l1 kernel. -/
theorem thetaPowerKernel_mul_le_left (G : Type u) [Group G] (l1 l2 : ℕ) :
    thetaPowerKernel G (l1 * l2) ≤ thetaPowerKernel G l1 :=
  etTh11_thetaPowerKernel_mono G (dvd_mul_right l1 l2)

/-- Derived: the level (l1*l2) theta power kernel sits inside the level-l2 kernel. -/
theorem thetaPowerKernel_mul_le_right (G : Type u) [Group G] (l1 l2 : ℕ) :
    thetaPowerKernel G (l1 * l2) ≤ thetaPowerKernel G l2 :=
  etTh11_thetaPowerKernel_mono G (dvd_mul_left l2 l1)

/-- Derived: transitivity of anti-monotonicity for theta power kernels. -/
theorem thetaPowerKernel_le_trans (G : Type u) [Group G] {l1 l2 l3 : ℕ}
    (h12 : l1 ∣ l2) (h23 : l2 ∣ l3) :
    thetaPowerKernel G l3 ≤ thetaPowerKernel G l1 :=
  le_trans (etTh11_thetaPowerKernel_mono G h23) (etTh11_thetaPowerKernel_mono G h12)

/-- Derived: the level (l1*l2) elliptic power kernel sits inside the level-l1 kernel. -/
theorem ellipticPowerKernel_mul_le_left (G : Type u) [Group G] (l1 l2 : ℕ) :
    ellipticPowerKernel G (l1 * l2) ≤ ellipticPowerKernel G l1 :=
  etTh11_ellipticPowerKernel_mono G (dvd_mul_right l1 l2)

/-- Derived: the level (l1*l2) elliptic power kernel sits inside the level-l2 kernel. -/
theorem ellipticPowerKernel_mul_le_right (G : Type u) [Group G] (l1 l2 : ℕ) :
    ellipticPowerKernel G (l1 * l2) ≤ ellipticPowerKernel G l2 :=
  etTh11_ellipticPowerKernel_mono G (dvd_mul_left l2 l1)

/-- Derived: transitivity of anti-monotonicity for elliptic power kernels. -/
theorem ellipticPowerKernel_le_trans (G : Type u) [Group G] {l1 l2 l3 : ℕ}
    (h12 : l1 ∣ l2) (h23 : l2 ∣ l3) :
    ellipticPowerKernel G l3 ≤ ellipticPowerKernel G l1 :=
  le_trans (etTh11_ellipticPowerKernel_mono G h23) (etTh11_ellipticPowerKernel_mono G h12)

#check thetaPowerKernel_mul_le_left
#check thetaPowerKernel_mul_le_right
#check thetaPowerKernel_le_trans
#check ellipticPowerKernel_mul_le_left
#check ellipticPowerKernel_mul_le_right
#check ellipticPowerKernel_le_trans

end LeanFormal.IUT.XiFPaper.Mzk1EtTh11DerivedActual
end
