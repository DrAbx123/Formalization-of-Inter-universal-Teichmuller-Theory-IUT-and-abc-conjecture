import tmp.sheaf.xif.paper.EtTh11ThetaRealizationRowsActual

/-!
  Mainline: EtTh power-kernel lattice laws (transitivity of level anti-monotonicity
  and theta->elliptic comap containment).  Real proofs from the EtTh11 re-exports.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1EtThKernelLatticeLawsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.EtTh10ThetaQuotientLawsActual
open LeanFormal.IUT.XiFPaper.EtTh11ThetaRealizationRowsActual

universe u

theorem etTh11_thetaPowerKernel_mono_trans (G : Type u) [Group G] {l1 l2 l3 : Nat}
    (h12 : l1 ∣ l2) (h23 : l2 ∣ l3) :
    thetaPowerKernel G l3 ≤ thetaPowerKernel G l1 :=
  le_trans (etTh11_thetaPowerKernel_mono G h23) (etTh11_thetaPowerKernel_mono G h12)

theorem etTh11_ellipticPowerKernel_mono_trans (G : Type u) [Group G] {l1 l2 l3 : Nat}
    (h12 : l1 ∣ l2) (h23 : l2 ∣ l3) :
    ellipticPowerKernel G l3 ≤ ellipticPowerKernel G l1 :=
  le_trans (etTh11_ellipticPowerKernel_mono G h23) (etTh11_ellipticPowerKernel_mono G h12)

theorem etTh11_thetaKernel_le_ellipticComap (G : Type u) [Group G] (l : Nat) :
    thetaPowerKernel G l ≤ (ellipticPowerKernel G l).comap (thetaToElliptic G) :=
  etTh10_thetaPowerKernel_le_comap G l

theorem etTh11_thetaPowerKernel_le_one (G : Type u) [Group G] (l : Nat) :
    thetaPowerKernel G l ≤ thetaPowerKernel G 1 :=
  etTh11_thetaPowerKernel_mono G (one_dvd l)

theorem etTh11_ellipticPowerKernel_le_one (G : Type u) [Group G] (l : Nat) :
    ellipticPowerKernel G l ≤ ellipticPowerKernel G 1 :=
  etTh11_ellipticPowerKernel_mono G (one_dvd l)
end LeanFormal.IUT.XiFPaper.Mzk1EtThKernelLatticeLawsActual