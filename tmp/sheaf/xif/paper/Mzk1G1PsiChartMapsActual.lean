import tmp.sheaf.xif.paper.Mzk1G1FermatAffineChartActual
import tmp.sheaf.xif.paper.Mzk1G1FermatSecondChartActual
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual

variable (n : Nat)

/-! ## First chart U0 = Spec A0, A0 = Q[x,y]/(x^n + y^n - 1) -/

/-- The x-coordinate function on the first Fermat chart. -/
def chartX : R n := Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The y-coordinate function on the first Fermat chart. -/
def chartY : R n := Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The actual Fermat equation x^n + y^n = 1 holds on the first chart. -/
theorem chartX_pow_add_chartY_pow_eq_one :
    chartX n ^ n + chartY n ^ n = 1 := by
  have hmem : fermatEquation n ∈
      Ideal.span ({fermatEquation n} : Set (MvPolynomial (Fin 2) ℚ)) :=
    Ideal.subset_span (by simp)
  have hmk : Ideal.Quotient.mk (Ideal.span ({fermatEquation n} :
      Set (MvPolynomial (Fin 2) ℚ))) (fermatEquation n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hsub : chartX n ^ n + chartY n ^ n - 1 = 0 := by
    rw [chartX, chartY, ← map_pow, ← map_pow, ← map_add, ← map_one (Ideal.Quotient.mk _),
      ← map_sub]
    exact hmk
  exact sub_eq_zero.mp hsub

/-- The protected chart product u = prod_{t in T} (x - t) on the first chart. -/
noncomputable def psiChart0Coord (T : Finset ℚ) : R n :=
  ∏ t ∈ T, (chartX n - algebraMap ℚ (R n) t)

/-- The 0-fibre of the first chart of psi is exactly the union of the fibers x = t,
t in T: a prime contains the chart product iff it contains one of the linear factors. -/
theorem psiChart0Coord_mem_iff (T : Finset ℚ) (P : Ideal (R n)) [P.IsPrime] :
    psiChart0Coord n T ∈ P ↔ ∃ t ∈ T, chartX n - algebraMap ℚ (R n) t ∈ P := by
  induction T using Finset.induction_on with
  | empty =>
      have hempty : psiChart0Coord n (∅ : Finset ℚ) = 1 := by simp [psiChart0Coord]
      rw [hempty]
      constructor
      · intro h
        have htop : P = ⊤ := by
          rw [Ideal.eq_top_iff_one]
          exact h
        exact absurd htop (inferInstance : P.IsPrime).ne_top
      · rintro ⟨t, ht, _⟩
        simp at ht
  | insert b s hb ih =>
      unfold psiChart0Coord
      rw [Finset.prod_insert hb]
      constructor
      · intro hmem
        rcases (inferInstance : P.IsPrime).mem_or_mem hmem with h | h
        · exact ⟨b, Finset.mem_insert_self b s, h⟩
        · obtain ⟨t, ht, hmem'⟩ := ih.mp h
          exact ⟨t, Finset.mem_insert_of_mem ht, hmem'⟩
      · rintro ⟨t, ht, hmem⟩
        rw [Finset.mem_insert] at ht
        rcases ht with rfl | ht
        · exact Ideal.mul_mem_right _ P hmem
        · exact Ideal.mul_mem_left P _ (ih.mpr ⟨t, ht, hmem⟩)

/-- The first chart morphism of the two-section map psi = [s0 : s1]:
Spec A0 -> Spec Q[u], u = prod (x - t). -/
noncomputable def psiChart0Map (T : Finset ℚ) :
    FermatChart n ⟶ Spec (CommRingCat.of (Polynomial ℚ)) :=
  Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom (algebraMap ℚ (R n)) (psiChart0Coord n T)))

/-! ## Second chart U1 = Spec A1, A1 = Q[s,r]/(1 + s^n - r^n) -/

/-- The s-coordinate on the second Fermat chart. -/
def chartS : R2 n := Ideal.Quotient.mk _ (MvPolynomial.X 0)

/-- The r-coordinate on the second Fermat chart (r = 1/x on the overlap). -/
def chartR : R2 n := Ideal.Quotient.mk _ (MvPolynomial.X 1)

/-- The actual second-chart Fermat equation 1 + s^n = r^n holds. -/
theorem one_add_chartS_pow_eq_chartR_pow :
    1 + chartS n ^ n = chartR n ^ n := by
  have hmem : secondEquation n ∈
      Ideal.span ({secondEquation n} : Set (MvPolynomial (Fin 2) ℚ)) :=
    Ideal.subset_span (by simp)
  have hmk : Ideal.Quotient.mk (Ideal.span ({secondEquation n} :
      Set (MvPolynomial (Fin 2) ℚ))) (secondEquation n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hsub : 1 + chartS n ^ n - chartR n ^ n = 0 := by
    rw [chartS, chartR, ← map_pow, ← map_pow, ← map_one (Ideal.Quotient.mk _), ← map_add, ← map_sub]
    exact hmk
  exact sub_eq_zero.mp hsub

/-- The reciprocal chart polynomial q = prod (1 - t r) on the second chart. -/
noncomputable def psiChartInfDenom (T : Finset ℚ) : R2 n :=
  ∏ t ∈ T, (1 - algebraMap ℚ (R2 n) t * chartR n)

/-- The second chart of psi is the principal open D(q) inside U1. -/
noncomputable abbrev psiChartInfDomain (T : Finset ℚ) : Type :=
  Localization.Away (psiChartInfDenom n T)

/-- The second chart coordinate v = q^{-1} * r^{|T|}: on the r = 0 fiber (the part of
Y_n outside the first chart) this equals 0, so psi is regular there. -/
noncomputable def psiChartInfCoord (T : Finset ℚ) : psiChartInfDomain n T :=
  IsLocalization.mk' (psiChartInfDomain n T) (chartR n ^ T.card)
    ⟨psiChartInfDenom n T, Submonoid.mem_powers _⟩

/-- The second chart coordinate is q^{-1} r^{|T|}: multiply by q recovers r^{|T|}. -/
theorem psiChartInfCoord_spec (T : Finset ℚ) :
    psiChartInfCoord n T * algebraMap (R2 n) (psiChartInfDomain n T) (psiChartInfDenom n T) =
      algebraMap (R2 n) (psiChartInfDomain n T) (chartR n ^ T.card) :=
  IsLocalization.mk'_spec _ _ _

/-- The second chart morphism of the two-section map psi: Spec A1[1/q] -> Spec Q[v],
v = q^{-1} r^{|T|}. -/
noncomputable def psiChartInfMap (T : Finset ℚ) :
    Spec (CommRingCat.of (psiChartInfDomain n T)) ⟶
      Spec (CommRingCat.of (Polynomial ℚ)) :=
  Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom (algebraMap ℚ (psiChartInfDomain n T)) (psiChartInfCoord n T)))

#print axioms chartX_pow_add_chartY_pow_eq_one
#print axioms psiChart0Coord_mem_iff
#print axioms psiChart0Map
#print axioms one_add_chartS_pow_eq_chartR_pow
#print axioms psiChartInfCoord_spec
#print axioms psiChartInfMap
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
