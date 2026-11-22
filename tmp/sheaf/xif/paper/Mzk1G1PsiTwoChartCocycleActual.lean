import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiTwoChartCocycleActual

/-- The protected chart polynomial prod (x - t) on a general Q-algebra chart. -/
noncomputable def chartProd {S : Type*} [CommRing S] [Algebra ℚ S] (x : S) (T : Finset ℚ) : S :=
  ∏ t ∈ T, (x - algebraMap ℚ S t)

/-- The reciprocal chart polynomial prod (1 - t r). -/
noncomputable def chartProdInv {S : Type*} [CommRing S] [Algebra ℚ S] (r : S) (T : Finset ℚ) : S :=
  ∏ t ∈ T, (1 - algebraMap ℚ S t * r)

/-- KEY IDENTITY ON THE CHART OVERLAP.  If r*x = 1 (r is the inverse of x on the
overlap of the two charts), then prod (1 - t r) = r^{|T|} * prod (x - t): factor by
factor, 1 - t r = r x - r t = r (x - t). -/
theorem chartProdInv_eq_pow_mul_chartProd {S : Type*} [CommRing S] [Algebra ℚ S]
    (x r : S) (T : Finset ℚ) (h : r * x = 1) :
    chartProdInv r T = r ^ T.card * chartProd x T := by
  unfold chartProdInv chartProd
  have hfac : ∀ t ∈ T, (1 - algebraMap ℚ S t * r) = r * (x - algebraMap ℚ S t) := by
    intro t _
    have ht : algebraMap ℚ S t * r = r * algebraMap ℚ S t := mul_comm _ _
    rw [ht, ← h, mul_sub]
  calc ∏ t ∈ T, (1 - algebraMap ℚ S t * r)
      = ∏ t ∈ T, r * (x - algebraMap ℚ S t) := Finset.prod_congr rfl hfac
    _ = (∏ _t ∈ T, r) * ∏ t ∈ T, (x - algebraMap ℚ S t) := Finset.prod_mul_distrib
    _ = r ^ T.card * ∏ t ∈ T, (x - algebraMap ℚ S t) := by rw [Finset.prod_const]

/-- THE PSI OVERLAP COCYCLE.  On the chart overlap, where r = x^{-1} and where the
reciprocal chart polynomial q = prod (1 - t r) is inverted, the two chart coordinates
of psi = [s0 : s1] are reciprocal: (prod (x - t)) * (q^{-1} * r^{|T|}) = 1. -/
theorem psi_chart_coords_mul_eq_one {S : Type*} [CommRing S] [Algebra ℚ S]
    (x r qinv : S) (T : Finset ℚ) (h : r * x = 1)
    (hq : qinv * chartProdInv r T = 1) :
    chartProd x T * (qinv * r ^ T.card) = 1 := by
  have hkey := chartProdInv_eq_pow_mul_chartProd x r T h
  calc chartProd x T * (qinv * r ^ T.card) = qinv * (r ^ T.card * chartProd x T) := by ring
    _ = qinv * chartProdInv r T := by rw [← hkey]
    _ = 1 := hq

/-- On the trivial protected set the chart product is 1. -/
theorem chartProd_empty {S : Type*} [CommRing S] [Algebra ℚ S] (x : S) :
    chartProd x (∅ : Finset ℚ) = 1 := by
  simp [chartProd]

/-- The protected chart product factors through any one of its protected values. -/
theorem chartProd_eq_mul_erase {S : Type*} [CommRing S] [Algebra ℚ S]
    (x : S) {T : Finset ℚ} {t : ℚ} (ht : t ∈ T) :
    chartProd x T = (x - algebraMap ℚ S t) * chartProd x (T.erase t) := by
  unfold chartProd
  rw [← Finset.mul_prod_erase T (fun s => (x - algebraMap ℚ S s)) ht]

#print axioms chartProdInv_eq_pow_mul_chartProd
#print axioms psi_chart_coords_mul_eq_one
#print axioms chartProd_eq_mul_erase
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiTwoChartCocycleActual
