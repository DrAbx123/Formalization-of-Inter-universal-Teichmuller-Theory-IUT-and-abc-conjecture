import tmp.sheaf.xif.paper.Node09TateLaurentExpansionActual
import tmp.sheaf.xif.paper.Node09TateNewtonPolygonActual

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09TateZeroCountActual

universe u
variable {K : Type u} [NormedField K]

/-- Principal term of the Tate X Laurent series. -/
def tatePrincipalX (u : K) : K := u / (1 - u) ^ 2

/-- Principal term is even under inversion. -/
theorem tatePrincipalX_inv (u : K) (hu : u ≠ 0) :
    tatePrincipalX u⁻¹ = tatePrincipalX u := by
  unfold tatePrincipalX
  field_simp [hu]
  ring

/-- Algebraic core of the Newton-polygon zero count: two parameters have the same
principal term exactly when they agree or are inverse to each other. -/
theorem tatePrincipalX_eq_iff (u v : K) (h1 : 1 - u ≠ 0) (h2 : 1 - v ≠ 0) :
    tatePrincipalX u = tatePrincipalX v ↔ u = v ∨ u * v = 1 := by
  constructor
  · intro h
    have hfac : (u - v) * (1 - u * v) = 0 := by
      unfold tatePrincipalX at h
      field_simp [h1, h2] at h
      linear_combination h
    rcases mul_eq_zero.mp hfac with hzero | hone
    · exact Or.inl (sub_eq_zero.mp hzero)
    · exact Or.inr (sub_eq_zero.mp hone).symm
  · rintro (rfl | huv)
    · rfl
    · have hu : u ≠ 0 := by
        intro hzero
        rw [hzero, zero_mul] at huv
        exact one_ne_zero huv.symm
      have hv : v = u⁻¹ := eq_inv_of_mul_eq_one_right huv
      subst v
      rw [tatePrincipalX_inv u hu]

/-- If X = principal + remainder and the remainder difference is smaller than the
principal difference, then X(u)=X(v) forces u=v or uv=1: this is the exact
zero-count comparison shape of the Newton-polygon/Rouche step. -/
theorem tateBranches_of_x_eq_of_remainder_lt
    (R : K → K) (u v : K) (h1 : 1 - u ≠ 0) (h2 : 1 - v ≠ 0)
    (hX : tatePrincipalX u + R u = tatePrincipalX v + R v)
    (hlt : ‖R v - R u‖ < ‖tatePrincipalX u - tatePrincipalX v‖) :
    u = v ∨ u * v = 1 := by
  have hdiff : tatePrincipalX u - tatePrincipalX v = R v - R u := by
    linear_combination hX
  have hzero : tatePrincipalX u - tatePrincipalX v = 0 := by
    by_contra hne
    have hnorm : ‖tatePrincipalX u - tatePrincipalX v‖ = ‖R v - R u‖ := by
      rw [hdiff]
    rw [hnorm] at hlt
    exact lt_irrefl _ hlt
  exact (tatePrincipalX_eq_iff u v h1 h2).mp (sub_eq_zero.mp hzero)

def Node09TateZeroCountStatus : List String :=
  [ "actual: tatePrincipalX u = u/(1-u)^2 is inversion-even, and tatePrincipalX u = tatePrincipalX v iff u = v or u*v = 1 (denominators nonzero)",
    "actual: tateBranches_of_x_eq_of_remainder_lt: if X = principal + remainder and ||R v - R u|| < ||principal u - principal v||, then X(u)=X(v) forces u=v or uv=1; this is the exact algebraic zero-count/branch step",
    "MISSING: the strict remainder comparison ||R v - R u|| < ||principal u - principal v|| for the actual X on the fundamental annulus. The available bounds are only norms of R(u), R(v) separately (xPositiveTail_norm_le, xNegativeSeries_norm_le), not a difference bound against the principal term; a Newton-polygon/Rouche argument or a Lipschitz/derivative bound for the remainder is needed",
    "MISSING: after u=v or uv=1, normalize to q^Z orbits using q-periodicity and the fundamental domain; then the Y inversion branch selects between u and u^{-1}",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateZeroCountActual