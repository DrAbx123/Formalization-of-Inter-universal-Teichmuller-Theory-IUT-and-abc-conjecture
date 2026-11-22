import tmp.sheaf.xif.paper.S1983EtThSignatureBridgeActual

/-!
# S1990: the normal form of the affine coordinate ring and the fixed subring

This file closes G3 of S1983: the invariant ring of the affine coordinate ring
R' = F'[x,y]/(y^2 - (x^3 + (61/64)x^2 - (125/64)x)) under the actual elliptic
involution (x,y) |-> (x,-y) is exactly F'[x].

The proof constructs the normal form R' = F'[x] (+) F'[x]*y explicitly:

* E : MvPolynomial (Fin 2) F' ~= Polynomial (Polynomial F') is the algebra
  equivalence sending x to the constant polynomial C X and y to the
  polynomial variable X.  Thus the Weierstrass relation becomes
  g = X^2 - C f, where f = X^3 + (61/64)X^2 - (125/64)X.
* g is monic of degree two.  For any representative P, the remainder
  E P % g has degree at most one, hence is C q * X + C p; its class in R'
  is p(x) + q(x)*y.
* Conversely, two such degree-at-most-one forms with the same class have the
  same remainder (division by a monic polynomial is well defined on the
  quotient).  Hence the normal form is unique.
* The involution fixes p(x) and sends q(x)*y to -q(x)*y.  A fixed element
  therefore has q = -q, hence q = 0 over the characteristic-zero field F'.

No axiom, no sorry, no postulated quotient.  The final theorem is
S1990CoarseQuotientIsAffineLine : S1983CoarseQuotientIsAffineLine.
-/

noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S1990GenusZeroFixedSubringActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual
open LeanFormal.IUT.XiFPaper.S1964QuotientCFActual
open LeanFormal.IUT.XiFPaper.S1983EtThSignatureBridgeActual

/-! ## 1. The coordinate ring and the two coordinate classes -/

abbrev K := S1726K

abbrev R := S1726CoordinateRing

abbrev I : Ideal (MvPolynomial (Fin 2) K) :=
  Ideal.span {S1726AffinePolynomial}

/-- The quotient map F'[x,y] -> R'. -/
abbrev mk : MvPolynomial (Fin 2) K →+* R := Ideal.Quotient.mk I

/-- The class of x in the affine coordinate ring. -/
abbrev x : R := mk (MvPolynomial.X 0)

/-- The class of y in the affine coordinate ring. -/
abbrev y : R := mk (MvPolynomial.X 1)

/-! ## 2. The polynomial model: x becomes a coefficient, y the variable -/

/-- Swap the two multivariable indices, so that y (index 1) is split off
as the polynomial variable by finSuccEquiv. -/
noncomputable def E : MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) :=
  (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)).trans
    ((MvPolynomial.finSuccEquiv K 1).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1))))

theorem E_X0 : E (MvPolynomial.X 0) = Polynomial.C Polynomial.X := by
  simp only [E, AlgEquiv.trans_apply]
  rw [show MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)
      (MvPolynomial.X 0) = MvPolynomial.X 1 by simp]
  rw [show MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 1) =
      Polynomial.C (MvPolynomial.X 0) from by
    simpa using (MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 1)
      (j := (0 : Fin 1)))]
  simp

theorem E_X1 : E (MvPolynomial.X 1) = Polynomial.X := by
  simp only [E, AlgEquiv.trans_apply]
  rw [show MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)
      (MvPolynomial.X 1) = MvPolynomial.X 0 by simp]
  rw [MvPolynomial.finSuccEquiv_X_zero]
  simp

theorem E_C (a : K) : E (MvPolynomial.C a) = Polynomial.C (Polynomial.C a) := by
  have h := E.commutes a
  simpa [MvPolynomial.algebraMap_eq, Polynomial.algebraMap_eq] using h

/-- The cubic x^3 + (61/64)x^2 - (125/64)x of the S1726 model. -/
noncomputable def fpoly : Polynomial K :=
  Polynomial.X ^ 3 + Polynomial.C (61/64 : K) * Polynomial.X ^ 2 +
    Polynomial.C (-125/64 : K) * Polynomial.X

/-- The Weierstrass relation in the polynomial model:
T^2 = C f, i.e. y^2 = x^3 + (61/64)x^2 - (125/64)x. -/
noncomputable def g : Polynomial (Polynomial K) :=
  Polynomial.X ^ 2 - Polynomial.C fpoly

theorem E_affinePolynomial : E S1726AffinePolynomial = g := by
  rw [S1726AffinePolynomial_eq]
  simp [g, fpoly, E_X0, E_X1, E_C]

theorem g_monic : g.Monic := by
  rw [g]
  exact Polynomial.monic_X_pow_sub_C fpoly (by norm_num)

theorem g_degree : g.degree = 2 := by
  rw [g]
  exact Polynomial.degree_X_pow_sub_C (by norm_num : 0 < 2) fpoly

theorem g_natDegree : g.natDegree = 2 := by
  rw [g]
  exact Polynomial.natDegree_X_pow_sub_C

theorem g_ne_one : g ≠ 1 := by
  intro h
  have hd := g_degree
  rw [h] at hd
  norm_num at hd

theorem E_symm_X : E.symm Polynomial.X = MvPolynomial.X 1 := by
  rw [← E_X1, AlgEquiv.symm_apply_apply]

theorem E_symm_C_X : E.symm (Polynomial.C Polynomial.X) = MvPolynomial.X 0 := by
  rw [← E_X0, AlgEquiv.symm_apply_apply]

theorem E_symm_g : E.symm g = S1726AffinePolynomial := by
  rw [← E_affinePolynomial, AlgEquiv.symm_apply_apply]

/-! ## 3. The class of p(x) and of q(x)*y -/

theorem mk_C (a : K) : mk (MvPolynomial.C a) = algebraMap K R a :=
  Ideal.Quotient.mk_algebraMap K I a

theorem S1990_PolyToCoordinateRing_fpoly :
    S1983PolyToCoordinateRing fpoly =
      x ^ 3 + algebraMap K R (61/64) * x ^ 2 + algebraMap K R (-125/64) * x := by
  simp [S1983PolyToCoordinateRing, fpoly, x]

theorem mk_E_symm_C (p : Polynomial K) :
    mk (E.symm (Polynomial.C p)) = S1983PolyToCoordinateRing p := by
  let Ψ : Polynomial K →ₐ[K] R :=
    (Ideal.Quotient.mkₐ K I).comp (E.symm.toAlgHom.comp Polynomial.CAlgHom)
  have hΨ : Ψ = S1983PolyToCoordinateRing := by
    apply Polynomial.algHom_ext
    simp [Ψ, S1983PolyToCoordinateRing_X, E_symm_C_X]
  have h := congrArg (fun f : Polynomial K →ₐ[K] R => f p) hΨ
  simpa [Ψ] using h

theorem mk_E_symm_C_mul_X (p : Polynomial K) :
    mk (E.symm (Polynomial.C p * Polynomial.X)) =
      S1983PolyToCoordinateRing p * y := by
  rw [map_mul, map_mul, E_symm_X, mk_E_symm_C p]

/-- The normal form of the Weierstrass coordinate ring in the S1726 model:
y^2 = x^3 + (61/64)x^2 - (125/64)x. -/
theorem S1990_y_sq : y ^ 2 = S1983PolyToCoordinateRing fpoly := by
  have h0 : mk (MvPolynomial.X 1 ^ 2 - (MvPolynomial.X 0 ^ 3 +
      MvPolynomial.C (61/64 : K) * MvPolynomial.X 0 ^ 2 +
      MvPolynomial.C (-125/64 : K) * MvPolynomial.X 0)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mem_span_singleton.mpr ⟨1, ?_⟩
    rw [S1726AffinePolynomial_eq]
    ring
  have h2 : y ^ 2 =
      x ^ 3 + mk (MvPolynomial.C (61/64 : K)) * x ^ 2 +
        mk (MvPolynomial.C (-125/64 : K)) * x := by
    have h := h0
    simp only [map_sub, map_add, map_mul, map_pow] at h
    exact sub_eq_zero.mp h
  rw [h2, mk_C, mk_C, ← S1990_PolyToCoordinateRing_fpoly]

/-! ## 4. Division by the monic relation g -/

/-- If two representatives have the same class in R', their remainders
modulo g agree.  This is the well-definedness of the reduction map. -/
theorem modByMonic_eq_of_mk_eq {P Q : MvPolynomial (Fin 2) K} (h : mk P = mk Q) :
    E P %ₘ g = E Q %ₘ g := by
  have hmem : P - Q ∈ I := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
  have hdvd : g ∣ E P - E Q := by
    refine ⟨E c, ?_⟩
    calc E P - E Q = E (P - Q) := by rw [map_sub]
      _ = E (S1726AffinePolynomial * c) := by rw [hc]
      _ = g * E c := by rw [map_mul, E_affinePolynomial]
  exact Polynomial.modByMonic_eq_of_dvd_sub g_monic hdvd

/-- Existence of the normal form: every class in R' is p(x) + q(x)*y, with
p and q the coefficients of the remainder of a representative modulo g. -/
theorem mk_eq_normalForm (P : MvPolynomial (Fin 2) K) :
    mk P = S1983PolyToCoordinateRing ((E P %ₘ g).coeff 0) +
      S1983PolyToCoordinateRing ((E P %ₘ g).coeff 1) * y := by
  set rem := E P %ₘ g with hrem
  have hdiv : g ∣ E P - rem := by
    refine ⟨E P /ₘ g, ?_⟩
    rw [hrem, Polynomial.modByMonic_eq_sub_mul_div]
    ring
  have hmem : P - E.symm rem ∈ I := by
    have hE : E (P - E.symm rem) = E P - rem := by simp
    have hdvd : g ∣ E (P - E.symm rem) := by rw [hE]; exact hdiv
    obtain ⟨c, hc⟩ := hdvd
    have hP : P - E.symm rem = S1726AffinePolynomial * E.symm c := by
      apply E.injective
      rw [map_sub, map_mul, E_affinePolynomial,
        AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      exact hE.symm.trans hc
    rw [hP]
    exact Ideal.mem_span_singleton.mpr ⟨E.symm c, rfl⟩
  have hmk : mk P = mk (E.symm rem) := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hmem
  rw [hmk]
  have hlt : rem.natDegree ≤ 1 := by
    have hlt' : rem.natDegree < g.natDegree :=
      Polynomial.natDegree_modByMonic_lt (E P) g_monic g_ne_one
    have : g.natDegree = 2 := g_natDegree
    omega
  have hrep : rem = Polynomial.C (rem.coeff 1) * Polynomial.X +
      Polynomial.C (rem.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hlt
  have hc0 : (Polynomial.C (rem.coeff 1) * Polynomial.X +
      Polynomial.C (rem.coeff 0)).coeff 0 = rem.coeff 0 := by simp
  have hc1 : (Polynomial.C (rem.coeff 1) * Polynomial.X +
      Polynomial.C (rem.coeff 0)).coeff 1 = rem.coeff 1 := by simp
  rw [hrep, hc0, hc1]
  have hsymm : E.symm (Polynomial.C (rem.coeff 1) * Polynomial.X +
      Polynomial.C (rem.coeff 0)) =
      E.symm (Polynomial.C (rem.coeff 1) * Polynomial.X) +
        E.symm (Polynomial.C (rem.coeff 0)) := by rw [map_add]
  rw [hsymm, map_add, mk_E_symm_C_mul_X, mk_E_symm_C]
  ring

/-- A degree bound: a polynomial of the form C p + C q * X has degree < 2. -/
theorem degree_linear_lt_two (p q : Polynomial K) :
    (Polynomial.C p + Polynomial.C q * Polynomial.X).degree < (2 : WithBot ℕ) := by
  have h1 : (Polynomial.C p).degree ≤ (0 : WithBot ℕ) := Polynomial.degree_C_le
  have h2 : (Polynomial.C q * Polynomial.X).degree ≤ (1 : WithBot ℕ) :=
    Polynomial.degree_C_mul_X_le q
  calc (Polynomial.C p + Polynomial.C q * Polynomial.X).degree
      ≤ max (Polynomial.C p).degree (Polynomial.C q * Polynomial.X).degree :=
        Polynomial.degree_add_le _ _
    _ ≤ (1 : WithBot ℕ) := max_le (le_trans h1 (by norm_num)) h2
    _ < (2 : WithBot ℕ) := by norm_num

/-- Uniqueness of the normal form: two decompositions of the same element
as p(x) + q(x)*y have the same coefficients. -/
theorem normalForm_unique {p q p' q' : Polynomial K}
    (h : S1983PolyToCoordinateRing p + S1983PolyToCoordinateRing q * y =
      S1983PolyToCoordinateRing p' + S1983PolyToCoordinateRing q' * y) :
    p = p' ∧ q = q' := by
  let P : MvPolynomial (Fin 2) K :=
    E.symm (Polynomial.C p + Polynomial.C q * Polynomial.X)
  let Q : MvPolynomial (Fin 2) K :=
    E.symm (Polynomial.C p' + Polynomial.C q' * Polynomial.X)
  have hP : mk P = S1983PolyToCoordinateRing p +
      S1983PolyToCoordinateRing q * y := by
    have hsymm : E.symm (Polynomial.C p + Polynomial.C q * Polynomial.X) =
        E.symm (Polynomial.C p) + E.symm (Polynomial.C q * Polynomial.X) := by
      rw [map_add]
    simp only [P, hsymm, map_add, mk_E_symm_C, mk_E_symm_C_mul_X]
  have hQ : mk Q = S1983PolyToCoordinateRing p' +
      S1983PolyToCoordinateRing q' * y := by
    have hsymm : E.symm (Polynomial.C p' + Polynomial.C q' * Polynomial.X) =
        E.symm (Polynomial.C p') + E.symm (Polynomial.C q' * Polynomial.X) := by
      rw [map_add]
    simp only [Q, hsymm, map_add, mk_E_symm_C, mk_E_symm_C_mul_X]
  have hmk : mk P = mk Q := by rw [hP, hQ, h]
  have hmod := modByMonic_eq_of_mk_eq hmk
  have hEP : E P = Polynomial.C p + Polynomial.C q * Polynomial.X := by simp [P]
  have hEQ : E Q = Polynomial.C p' + Polynomial.C q' * Polynomial.X := by simp [Q]
  have hselfP : E P %ₘ g = E P :=
    (Polynomial.modByMonic_eq_self_iff g_monic).mpr (by
      rw [hEP, g_degree]
      exact degree_linear_lt_two p q)
  have hselfQ : E Q %ₘ g = E Q :=
    (Polynomial.modByMonic_eq_self_iff g_monic).mpr (by
      rw [hEQ, g_degree]
      exact degree_linear_lt_two p' q')
  rw [hselfP, hselfQ, hEP, hEQ] at hmod
  constructor
  · have h0 := congrArg (fun z : Polynomial (Polynomial K) => z.coeff 0) hmod
    simpa using h0
  · have h1 := congrArg (fun z : Polynomial (Polynomial K) => z.coeff 1) hmod
    simpa using h1

/-! ## 5. The fixed subring is exactly K[x] -/

theorem fixed_imp_mem_range (r : R) (hr : S1898CoordEndo r = r) :
    r ∈ Set.range S1983PolyToCoordinateRing := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) r
  let A := (E P %ₘ g).coeff 0
  let B := (E P %ₘ g).coeff 1
  have hdec : mk P = S1983PolyToCoordinateRing A +
      S1983PolyToCoordinateRing B * y :=
    mk_eq_normalForm P
  have hσ : S1898CoordEndo (mk P) =
      S1983PolyToCoordinateRing A + S1983PolyToCoordinateRing (-B) * y := by
    rw [hdec]
    simp only [map_add, map_mul, S1983PolyToCoordinateRing_mem,
      S1898CoordEndo_y, map_neg]
    ring
  have heq : S1983PolyToCoordinateRing A + S1983PolyToCoordinateRing (-B) * y =
      S1983PolyToCoordinateRing A + S1983PolyToCoordinateRing B * y := by
    rw [← hσ, hr, hdec]
  have hB : B = 0 := by
    have hneg : -B = B := (normalForm_unique heq).2
    have hsum : B + B = 0 := neg_eq_iff_add_eq_zero.mp hneg
    have h2 : (2 : Polynomial K) * B = 0 := by
      simpa [two_mul] using hsum
    have h2ne : (2 : Polynomial K) ≠ 0 := by
      norm_num
    exact (mul_eq_zero.mp h2).resolve_left h2ne
  refine ⟨A, ?_⟩
  rw [hdec, hB]
  simp

/-- The normal form theorem: every element of R' has a unique expression
p(x) + q(x)*y. -/
theorem S1990_normalForm (r : R) :
    ∃! pq : Polynomial K × Polynomial K,
      r = S1983PolyToCoordinateRing pq.1 + S1983PolyToCoordinateRing pq.2 * y := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) r
  let A := (E P %ₘ g).coeff 0
  let B := (E P %ₘ g).coeff 1
  have hdec : mk P = S1983PolyToCoordinateRing A +
      S1983PolyToCoordinateRing B * y :=
    mk_eq_normalForm P
  refine ⟨(A, B), hdec, ?_⟩
  rintro ⟨p, q⟩ hp
  have hpq := normalForm_unique (hp.symm.trans hdec)
  exact Prod.ext hpq.1 hpq.2

/-- The fixed subring of the actual affine coordinate ring under the elliptic
involution is exactly the image of K[X]. -/
theorem S1990InvariantSubring_eq_range :
    S1983InvariantSubring = Set.range S1983PolyToCoordinateRing := by
  ext r
  constructor
  · intro hr
    exact fixed_imp_mem_range r hr
  · rintro ⟨p, rfl⟩
    exact S1983PolyToCoordinateRing_mem p

/-- G3 of S1983 is closed: the fixed subring of the actual affine coordinate
ring under S1898CoordEndo is exactly K[x]; equivalently the coarse quotient
of the once-punctured elliptic curve by +-1 is the affine line. -/
theorem S1990CoarseQuotientIsAffineLine : S1983CoarseQuotientIsAffineLine :=
  S1990InvariantSubring_eq_range

/-- The S1983-named form of the same theorem, for consumers that search for
the gap name. -/
theorem S1983CoarseQuotientIsAffineLine_holds : S1983CoarseQuotientIsAffineLine :=
  S1990CoarseQuotientIsAffineLine

/-! ## 6. Axiom footprint -/

#print axioms E_X0
#print axioms E_X1
#print axioms E_affinePolynomial
#print axioms mk_E_symm_C
#print axioms mk_E_symm_C_mul_X
#print axioms S1990_y_sq
#print axioms modByMonic_eq_of_mk_eq
#print axioms mk_eq_normalForm
#print axioms normalForm_unique
#print axioms fixed_imp_mem_range
#print axioms S1990_normalForm
#print axioms S1990InvariantSubring_eq_range
#print axioms S1990CoarseQuotientIsAffineLine
#print axioms S1983CoarseQuotientIsAffineLine_holds

end LeanFormal.IUT.XiFPaper.S1990GenusZeroFixedSubringActual