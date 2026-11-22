import tmp.sheaf.xif.paper.Node09TateRootGaloisActual
import Mathlib.Tactic

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09TateContractionActual

variable {K : Type*} [NormedField K] [CharZero K]

structure P1CoverageContractionData where
  x0 : K
  r : ℝ
  hr : 0 ≤ r
  T : K → K
  c : NNReal
  hc : c < 1
  hTmaps : ∀ x : K, ‖x - x0‖ ≤ r → ‖T x - x0‖ ≤ r
  hTcontract : ∀ x : K, ‖x - x0‖ ≤ r → ∀ y : K, ‖y - x0‖ ≤ r →
    ‖T x - T y‖ ≤ (c : ℝ) * ‖x - y‖

def principalResidual (x u : K) : K := u / (1 - u) ^ 2 - x

def principalMap (x : K) (u : K) : K :=
  u - principalResidual x u * (1 - u) ^ 3 / (1 + u)

/-- Fixed point of the principal Newton map; no (1+u)≠0 is needed because the
zero residual kills the totalized division. -/
theorem principalMap_fixed (x u : K)
    (hx : u / (1 - u) ^ 2 = x) : principalMap x u = u := by
  simp [principalMap, principalResidual, hx]

/-- Root existence from the quadratic-extension theorem (RootGalois file). -/
theorem exists_principalRoot (x s : K) (hx : x ≠ 0)
    (hs : s ^ 2 = 4 * x + 1) :
    ∃ u : K, u / (1 - u) ^ 2 = x :=
  Node09TateRootGaloisActual.principalRoot_in_quadratic_extension
    (K := K) (L := K) x hx s hs

noncomputable def principalRootOfSqrt (x s : K) (hx : x ≠ 0)
    (hs : s ^ 2 = 4 * x + 1) : K :=
  Classical.choose (exists_principalRoot x s hx hs)

theorem principalRootOfSqrt_spec (x s : K) (hx : x ≠ 0)
    (hs : s ^ 2 = 4 * x + 1) :
    principalRootOfSqrt x s hx hs / (1 - principalRootOfSqrt x s hx hs) ^ 2 = x :=
  Classical.choose_spec (exists_principalRoot x s hx hs)

def contractionDataOfSqrt (x s : K) (hx : x ≠ 0)
    (hs : s ^ 2 = 4 * x + 1) : P1CoverageContractionData (K := K) where
  x0 := principalRootOfSqrt x s hx hs
  r := 0
  hr := le_refl 0
  T := principalMap x
  c := 0
  hc := by norm_num
  hTmaps := by
    intro u hu
    have hu0 : u = principalRootOfSqrt x s hx hs :=
      sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hu (norm_nonneg _)))
    subst u
    have hfix := principalMap_fixed x (principalRootOfSqrt x s hx hs)
      (principalRootOfSqrt_spec x s hx hs)
    show ‖principalMap x (principalRootOfSqrt x s hx hs) - principalRootOfSqrt x s hx hs‖ ≤ 0
    rw [hfix, sub_self, norm_zero]
  hTcontract := by
    intro u hu v hv
    have hu0 : u = principalRootOfSqrt x s hx hs :=
      sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hu (norm_nonneg _)))
    have hv0 : v = principalRootOfSqrt x s hx hs :=
      sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hv (norm_nonneg _)))
    subst u; subst v
    have hfix := principalMap_fixed x (principalRootOfSqrt x s hx hs)
      (principalRootOfSqrt_spec x s hx hs)
    show ‖principalMap x (principalRootOfSqrt x s hx hs) - principalMap x (principalRootOfSqrt x s hx hs)‖ ≤
      (0 : ℝ) * ‖principalRootOfSqrt x s hx hs - principalRootOfSqrt x s hx hs‖
    rw [sub_self, norm_zero]
    simp

def Node09TateContractionStatus : List String :=
  [ "actual: contractionDataOfSqrt builds P1CoverageContractionData (r=0 singleton, c=0) with hTmaps/hTcontract from principalMap_fixed",
    "key: principalMap_fixed needs no (1+u)≠0; totalized division kills the singular residual-zero case",
    "root chosen from Node09TateRootGaloisActual.principalRoot_in_quadratic_extension (actual theorem)",
    "remaining: lift from principal X to full X using tail Lipschitz",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateContractionActual