/- Route 3.1: the explicit quotient presentation of Omega_{A0/k}:
Omega = (A0 dx + A0 dy) / (n x^(n-1) dx + n y^(n-1) dy). -/
import tmp.sheaf.xif.paper.Mzk1G1OmegaFreeActual
import tmp.sheaf.xif.paper.Mzk1G1OmegaBasisActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1OmegaQuotientPresentationActual

open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaBasisActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaFreeActual

/-- The relation vector n x^(n-1) dx + n y^(n-1) dy in the free two-generator module. -/
def relVec (n : Nat) : (Fin 2 →₀ B n) :=
  Finsupp.single 0 ((n : B n) * coordX n ^ (n - 1)) +
    Finsupp.single 1 ((n : B n) * coordY n ^ (n - 1))

/-- The explicit quotient presentation (A0 dx + A0 dy) / (relation). -/
abbrev OmegaQuot (n : Nat) : Type :=
  (Fin 2 →₀ B n) ⧸ Submodule.span (B n) ({relVec n} : Set (Fin 2 →₀ B n))

theorem presMap_single_zero (n : Nat) (a : B n) :
    presMap n (Finsupp.single 0 a) = a • dX n := by
  rw [presMap, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply]

theorem presMap_single_one (n : Nat) (a : B n) :
    presMap n (Finsupp.single 1 a) = a • dY n := by
  rw [presMap, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply]

theorem presMap_relVec (n : Nat) : presMap n (relVec n) = 0 := by
  rw [relVec, map_add, presMap_single_zero, presMap_single_one]
  exact derivation_relation n

theorem span_relVec_le_ker (n : Nat) :
    Submodule.span (B n) ({relVec n} : Set (Fin 2 →₀ B n)) ≤ LinearMap.ker (presMap n) := by
  rw [Submodule.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact presMap_relVec n

theorem phiEquiv_y_pow (n : Nat) (hn : 1 ≤ n) :
    phiEquiv n hn (coordY n ^ (n - 1)) = dX n := by
  rw [phiEquiv, LinearEquiv.ofBijective_apply, Phi_apply]
  exact y_pow_smul_omegaForm n hn

theorem phiEquiv_neg_x_pow (n : Nat) (hn : 1 ≤ n) :
    phiEquiv n hn (-(coordX n ^ (n - 1))) = dY n := by
  rw [phiEquiv, LinearEquiv.ofBijective_apply, Phi_apply]
  rw [neg_smul, x_pow_smul_omegaForm n hn, neg_neg]

theorem omegaEquivO_dX (n : Nat) (hn : 1 ≤ n) :
    omegaEquivO n hn (dX n) = coordY n ^ (n - 1) := by
  rw [omegaEquivO, ← phiEquiv_y_pow n hn, LinearEquiv.symm_apply_apply]

theorem omegaEquivO_dY (n : Nat) (hn : 1 ≤ n) :
    omegaEquivO n hn (dY n) = -(coordX n ^ (n - 1)) := by
  rw [omegaEquivO, ← phiEquiv_neg_x_pow n hn, LinearEquiv.symm_apply_apply]

/-- Kernel of the presentation map is exactly the relation span. -/
theorem ker_presMap (n : Nat) (hn : 1 ≤ n) :
    LinearMap.ker (presMap n) = Submodule.span (B n) ({relVec n} : Set (Fin 2 →₀ B n)) := by
  apply le_antisymm _ (span_relVec_le_ker n)
  intro p hp
  have hpzero : presMap n p = 0 := hp
  have hpdecomp : p = Finsupp.single 0 (p 0) + Finsupp.single 1 (p 1) := by
    ext i
    fin_cases i <;> simp
  have hzero : p 0 • dX n + p 1 • dY n = 0 := by
    have := hpzero
    rw [hpdecomp, map_add, presMap_single_zero, presMap_single_one] at this
    exact this
  have hker : p 0 * coordY n ^ (n - 1) - p 1 * coordX n ^ (n - 1) = 0 := by
    have h := congrArg (omegaEquivO n hn) hzero
    simp only [map_add, map_smul, omegaEquivO_dX n hn, omegaEquivO_dY n hn,
      smul_eq_mul, map_zero] at h
    have h' := h
    rw [show p 1 * -coordX n ^ (n - 1) = -(p 1 * coordX n ^ (n - 1)) from
      mul_neg (p 1) (coordX n ^ (n - 1))] at h'
    simpa [sub_eq_add_neg] using h'
  have hab : p 0 * coordY n ^ (n - 1) = p 1 * coordX n ^ (n - 1) := sub_eq_zero.mp hker
  set a := p 0
  set b := p 1
  set c := a * coordX n + b * coordY n with hc
  have hcx : c * coordX n ^ (n - 1) = a := by
    have hsum : coordX n ^ n + coordY n ^ n = 1 := by
      have h : coordX n ^ n + coordY n ^ n = 1 := sub_eq_zero.mp (relation n)
      exact h
    have hxa : coordX n * coordX n ^ (n - 1) = coordX n ^ n := by
      calc coordX n * coordX n ^ (n - 1) = coordX n ^ ((n - 1) + 1) :=
            (pow_succ' (coordX n) (n - 1)).symm
        _ = coordX n ^ n := by rw [Nat.sub_add_cancel hn]
    have hya : coordY n * coordY n ^ (n - 1) = coordY n ^ n := by
      calc coordY n * coordY n ^ (n - 1) = coordY n ^ ((n - 1) + 1) :=
            (pow_succ' (coordY n) (n - 1)).symm
        _ = coordY n ^ n := by rw [Nat.sub_add_cancel hn]
    calc c * coordX n ^ (n - 1)
        = a * (coordX n * coordX n ^ (n - 1)) + b * (coordY n * coordX n ^ (n - 1)) := by
          rw [hc]; ring
      _ = a * coordX n ^ n + b * coordY n * coordX n ^ (n - 1) := by
          rw [hxa]
          ring
      _ = a * coordX n ^ n + a * coordY n ^ n := by
          rw [show b * coordY n * coordX n ^ (n - 1) = a * coordY n ^ n from by
            calc b * coordY n * coordX n ^ (n - 1)
                = (b * coordX n ^ (n - 1)) * coordY n := by ring
              _ = (a * coordY n ^ (n - 1)) * coordY n := by rw [← hab]
              _ = a * coordY n ^ n := by rw [← hya]; ring]
      _ = a * (coordX n ^ n + coordY n ^ n) := by ring
      _ = a := by rw [hsum, mul_one]
  have hcy : c * coordY n ^ (n - 1) = b := by
    have hsum : coordX n ^ n + coordY n ^ n = 1 := sub_eq_zero.mp (relation n)
    have hyb : coordY n * coordY n ^ (n - 1) = coordY n ^ n := by
      calc coordY n * coordY n ^ (n - 1) = coordY n ^ ((n - 1) + 1) :=
            (pow_succ' (coordY n) (n - 1)).symm
        _ = coordY n ^ n := by rw [Nat.sub_add_cancel hn]
    have hxb : coordX n * coordX n ^ (n - 1) = coordX n ^ n := by
      calc coordX n * coordX n ^ (n - 1) = coordX n ^ ((n - 1) + 1) :=
            (pow_succ' (coordX n) (n - 1)).symm
        _ = coordX n ^ n := by rw [Nat.sub_add_cancel hn]
    calc c * coordY n ^ (n - 1)
        = a * (coordX n * coordY n ^ (n - 1)) + b * (coordY n * coordY n ^ (n - 1)) := by
          rw [hc]; ring
      _ = a * coordX n * coordY n ^ (n - 1) + b * coordY n ^ n := by
          rw [hyb]
          ring_nf
      _ = b * coordX n ^ n + b * coordY n ^ n := by
          rw [show a * coordX n * coordY n ^ (n - 1) = b * coordX n ^ n from by
            calc a * coordX n * coordY n ^ (n - 1)
                = (a * coordY n ^ (n - 1)) * coordX n := by ring
              _ = (b * coordX n ^ (n - 1)) * coordX n := by rw [hab]
              _ = b * coordX n ^ n := by rw [← hxb]; ring]
      _ = b * (coordX n ^ n + coordY n ^ n) := by ring
      _ = b := by rw [hsum, mul_one]
  have hunit : IsUnit (n : B n) := natCast_isUnit n hn
  set u := hunit.unit with hu
  have huval : ((u : B n)) = (n : B n) := hunit.unit_spec
  have hinv : ((↑u⁻¹) : B n) * (u : B n) = 1 := hunit.val_inv_mul
  set cc := c * (↑u⁻¹ : B n) with hcc
  have hpp : p = cc • relVec n := by
    rw [hpdecomp, relVec, smul_add, Finsupp.smul_single, Finsupp.smul_single]
    have h0 : cc * ((n : B n) * coordX n ^ (n - 1)) = a := by
      rw [hcc, ← huval]
      calc c * (↑u⁻¹) * ((u : B n) * coordX n ^ (n - 1))
          = c * (((↑u⁻¹) : B n) * (u : B n)) * coordX n ^ (n - 1) := by ring
        _ = c * coordX n ^ (n - 1) := by rw [hinv, mul_one]
        _ = a := hcx
    have h1 : cc * ((n : B n) * coordY n ^ (n - 1)) = b := by
      rw [hcc, ← huval]
      calc c * (↑u⁻¹) * ((u : B n) * coordY n ^ (n - 1))
          = c * (((↑u⁻¹) : B n) * (u : B n)) * coordY n ^ (n - 1) := by ring
        _ = c * coordY n ^ (n - 1) := by rw [hinv, mul_one]
        _ = b := hcy
    simp only [smul_eq_mul]
    rw [h0, h1]
  rw [hpp]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by rfl))

/-- The presentation map is surjective (dx and dy generate Omega). -/
theorem presMap_range (n : Nat) : LinearMap.range (presMap n) = ⊤ := by
  rw [eq_top_iff, ← span_dX_dY n]
  rw [Submodule.span_le]
  intro z hz
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact ⟨Finsupp.single 0 1, by rw [presMap_single_zero]; simp⟩
  · exact ⟨Finsupp.single 1 1, by rw [presMap_single_one]; simp⟩

/-- Route 3.1: the explicit quotient presentation is isomorphic to Omega_{A0/k}. -/
noncomputable def omegaQuotEquiv (n : Nat) (hn : 1 ≤ n) :
    OmegaQuot n ≃ₗ[B n] Omega n :=
  (Submodule.quotEquivOfEq (Submodule.span (B n) ({relVec n} : Set (Fin 2 →₀ B n)))
    (LinearMap.ker (presMap n)) (ker_presMap n hn).symm).trans
    ((LinearMap.quotKerEquivRange (presMap n)).trans
      ((LinearEquiv.ofEq (LinearMap.range (presMap n)) ⊤ (presMap_range n)).trans
        Submodule.topEquiv))

#print axioms ker_presMap
#print axioms omegaQuotEquiv
end LeanFormal.IUT.XiFPaper.Mzk1G1OmegaQuotientPresentationActual
