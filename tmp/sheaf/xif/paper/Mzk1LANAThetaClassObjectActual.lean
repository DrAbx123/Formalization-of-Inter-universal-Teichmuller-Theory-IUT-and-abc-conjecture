/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.lana.iut.Iut.EtaleTheta.ThetaClass

/-!
# Mzk1LANAThetaClassObjectActual — LANA etale-theta class object (Kummer-class side)

A515: reference object from LANA's actual model etale theta class
(`Iut.EtaleTheta.ThetaClass`, [EtTh] Prop. 1.3/1.5(iii)):
`thetaClass red rho ∈ H¹((Π^tp_Y)^Θ, μ)` for the model `(c,a') ↦ red c + ρ a'`,
its restriction to `Δ_Θ` being `red`, and its nontriviality criterion.

This is the etale-theta Kummer-class object that pairs with O2's
`thetaValueMon qroot j` (the `s^{-a²}` factor is the Gauss exponent).
No new axiom, no comparison. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LANAThetaClassObjectActual

open Iut.EtaleTheta
open ContH1
universe u

variable {M : Type u} [AddCommGroup M] {μ : Type u} [AddCommGroup μ]
variable [TopologicalSpace M] [DiscreteTopology M]
variable [TopologicalSpace μ] [IsTopologicalAddGroup μ]

/-- The LANA model etale-theta class object: the two characters `red`, `rho` and
the class `thetaClass red rho`. -/
structure EtaleThetaClassObject where
  red : M →+ μ
  rho : M →+ μ
  cl : ContH1 (PiYddot M) (Multiplicative μ)
  cl_eq : cl = thetaClass red rho

/-- The constructed class object from the LANA model. -/
def etaleThetaClassObject (red rho : M →+ μ) : EtaleThetaClassObject (M := M) (μ := μ) where
  red := red
  rho := rho
  cl := thetaClass red rho
  cl_eq := rfl

/-- `_constructed`: the class is LANA's `thetaClass red rho`. -/
theorem etaleThetaClassObject_constructed (red rho : M →+ μ) :
    (etaleThetaClassObject red rho).cl = thetaClass red rho := rfl

/-- Nontriviality: if `red ≠ 0`, the class is not the identity. -/
theorem etaleThetaClassObject_ne_one (red rho : M →+ μ) (h : red ≠ 0) :
    (etaleThetaClassObject red rho).cl ≠ 1 := by
  show thetaClass red rho ≠ 1
  exact thetaClass_ne_one rho h

/-- Restriction to `Δ_Θ` (`a' = 0`) is `red`. -/
theorem etaleThetaClassObject_restrict (red rho : M →+ μ) (c : M) :
    Multiplicative.toAdd ((thetaCocycle red rho : PiYddot M → Multiplicative μ)
      (Multiplicative.ofAdd (c, 0))) = red c :=
  thetaClass_restrict red rho c

/-- The class is trivial iff both characters vanish. -/
theorem etaleThetaClassObject_eq_one_iff (red rho : M →+ μ) :
    (etaleThetaClassObject red rho).cl = 1 ↔ red = 0 ∧ rho = 0 := by
  show thetaClass red rho = 1 ↔ red = 0 ∧ rho = 0
  exact thetaClass_eq_one_iff red rho

#check etaleThetaClassObject_constructed
#check etaleThetaClassObject_ne_one
#check etaleThetaClassObject_restrict

end LeanFormal.IUT.XiFPaper.Mzk1LANAThetaClassObjectActual
end
