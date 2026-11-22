import Mathlib
import LeanFormal.IUT.Foundations.AlgebraicGeometry.PermutationTorsorQuotient

/-!
# M2 local split case: idempotents and coordinate primitives

For a local commutative ring S, the only idempotents are 0 and 1.  This is the
input for the local permutation lemma on S^n.  This scratch proves the local
idempotent fact and the primality of the coordinate idempotents; the full
coordinate-permutation classification is recorded as the residual below.
-/

open Polynomial

universe u

namespace SplitCaseLocalPermutation

variable {S : Type u} [CommRing S]

/-- In a local ring, an idempotent is 0 or 1. -/
theorem idempotent_eq_zero_or_one [IsLocalRing S] {e : S}
    (he : e * e = e) : e = 0 ∨ e = 1 := by
  by_cases h : IsUnit e
  · obtain ⟨u, rfl⟩ := h
    have hu : (u : S) * (u : S) = (u : S) := he
    have h1 : (u : S) = 1 := by
      have := congrArg (fun x : S => (↑u⁻¹ : S) * x) hu
      simpa [mul_assoc] using this
    exact Or.inr h1
  · have h1u : IsUnit (1 - e) := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with heu | h1e
      · exact False.elim (h heu)
      · exact h1e
    rcases h1u with ⟨u, hu⟩
    have he0 : e * (1 - e) = 0 := by
      rw [mul_sub, he, mul_one, sub_self]
    have hzero : e * (u : S) = 0 := by
      rw [hu, he0]
    have heq : e = 0 := by
      calc e = e * (u : S) * (↑u⁻¹ : S) := by
            rw [mul_assoc, Units.mul_inv, mul_one]
        _ = 0 := by rw [hzero, zero_mul]
    exact Or.inl heq

/-- Pointwise idempotent functions on a finite type over a local ring take only
the values 0 and 1. -/
theorem pi_idempotent_apply_eq_zero_or_one [IsLocalRing S] {n : Type u}
    {e : n → S} (he : IsIdempotentElem e) (i : n) : e i = 0 ∨ e i = 1 :=
  idempotent_eq_zero_or_one (congrFun he.eq i)

/-- Coordinate idempotent at i. -/
noncomputable def coordIdem (n : Type u) [DecidableEq n] (i : n) : n → S :=
  Pi.single i 1

theorem coordIdem_idem (n : Type u) [DecidableEq n] (i : n) :
    IsIdempotentElem (coordIdem (S := S) n i) := by
  ext j
  by_cases h : j = i <;> simp [coordIdem, h]

theorem coordIdem_ne_zero [Nontrivial S] (n : Type u) [DecidableEq n] (i : n) :
    coordIdem (S := S) n i ≠ 0 := by
  intro h
  have := congrFun h i
  simp [coordIdem] at this

/-- The coordinate idempotent is primitive: every idempotent supported on it is
0 or itself. -/
theorem coordIdem_primitive [IsLocalRing S] (n : Type u) [DecidableEq n] (i : n) :
    IsIdempotentElem (coordIdem (S := S) n i) ∧
      coordIdem (S := S) n i ≠ 0 ∧
      ∀ f : n → S, IsIdempotentElem f →
        f * coordIdem (S := S) n i = f → f = 0 ∨ f = coordIdem (S := S) n i := by
  refine ⟨coordIdem_idem n i, coordIdem_ne_zero n i, ?_⟩
  intro f hf hfe
  by_cases hi : f i = 1
  · right
    ext j
    by_cases hji : j = i
    · subst hji
      simpa [coordIdem] using hi
    · have hfj : f j = 0 := by
        have hval := congrFun hfe j
        have hcoord : coordIdem (S := S) n i j = 0 := by
          simp [coordIdem, hji]
        simpa [hcoord] using hval.symm
      simp [coordIdem, hji, hfj]
  · left
    ext j
    by_cases hji : j = i
    · have hfi : f i = 0 ∨ f i = 1 :=
        pi_idempotent_apply_eq_zero_or_one hf i
      rw [← hji] at hfi
      rcases hfi with h0 | h1
      · exact h0
      · exact False.elim (hi (by rwa [hji] at h1))
    · have hval := congrFun hfe j
      have hcoord : coordIdem (S := S) n i j = 0 := by
        simp [coordIdem, hji]
      simpa [hcoord] using hval.symm


/-- A primitive idempotent function on a finite coordinate set has a unique
coordinate where it takes the value 1. -/
theorem primitive_idempotent_support_unique [IsLocalRing S] {n : Type u}
    [Fintype n] [DecidableEq n] {e : n → S}
    (he : IsIdempotentElem e) (hne : e ≠ 0)
    (hprim : ∀ f : n → S, IsIdempotentElem f → f * e = f → f = 0 ∨ f = e) :
    ∃! i : n, e i = 1 := by
  have hval : ∀ i, e i = 0 ∨ e i = 1 := fun i =>
    pi_idempotent_apply_eq_zero_or_one he i
  have hex : ∃ i, e i = 1 := by
    by_contra h
    have hz : e = 0 := by
      funext i
      rcases hval i with h0 | h1
      · exact h0
      · exact False.elim (h ⟨i, h1⟩)
    exact hne hz
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  let f : n → S := coordIdem (S := S) n i
  have hf : IsIdempotentElem f := coordIdem_idem n i
  have hfe : f * e = f := by
    ext k
    by_cases hk : k = i
    · subst hk
      simp [f, coordIdem, hi]
    · have hfk : f k = 0 := by simp [f, coordIdem, hk]
      simp [hfk]
  have hf0 : f ≠ 0 := coordIdem_ne_zero n i
  have hfe' : f ≠ e := by
    intro h
    have := congrFun h j
    have hfj : f j = 0 := by simp [f, coordIdem, hji]
    rw [hfj, hj] at this
    exact zero_ne_one this
  exact hprim f hf hfe |>.elim hf0 hfe'


/-- An S-algebra automorphism of S^n maps a coordinate idempotent to a function
with a unique coordinate equal to 1. -/
theorem algEquiv_coordIdem_support_unique [IsLocalRing S] {n : Type u}
    [Fintype n] [DecidableEq n] (φ : (n → S) ≃ₐ[S] (n → S)) (i : n) :
    ∃! j : n, φ (coordIdem (S := S) n i) j = 1 := by
  let e : n → S := coordIdem (S := S) n i
  have he : IsIdempotentElem e := coordIdem_idem n i
  have hφe : IsIdempotentElem (φ e) := by
    show (φ e) * (φ e) = φ e
    rw [← map_mul, he.eq]
  have hne : φ e ≠ 0 := by
    intro h
    have : e = 0 := φ.injective (by simpa using h)
    exact coordIdem_ne_zero n i this
  have hprim : ∀ f : n → S, IsIdempotentElem f →
      f * (φ e) = f → f = 0 ∨ f = φ e := by
    intro f hf hfe
    let ψ : n → S := φ.symm f
    have hψ : IsIdempotentElem ψ := by
      show ψ * ψ = ψ
      change φ.symm f * φ.symm f = φ.symm f
      rw [← map_mul, hf.eq]
    have hψe : ψ * e = ψ := by
      apply φ.injective
      change φ (φ.symm f * e) = φ (φ.symm f)
      rw [map_mul, φ.apply_symm_apply]
      simpa [ψ, hfe]
    rcases coordIdem_primitive n i |>.2.2 ψ hψ (by simpa [e] using hψe) with h0 | h1
    · left
      change ψ = 0 at h0
      change f = 0
      simpa [ψ, h0] using (φ.apply_symm_apply f).symm
    · right
      change ψ = e at h1
      change f = φ e
      simpa [ψ, h1] using (φ.apply_symm_apply f).symm
  exact primitive_idempotent_support_unique hφe hne hprim

/-- The coordinate permutation induced by an S-algebra automorphism of S^n. -/
noncomputable def localPermutation [IsLocalRing S] {n : Type u}
    [Fintype n] [DecidableEq n] (φ : (n → S) ≃ₐ[S] (n → S)) (i : n) : n :=
  (algEquiv_coordIdem_support_unique (S := S) φ i).choose

/-- The defining property of the local coordinate permutation. -/
theorem localPermutation_spec [IsLocalRing S] {n : Type u}
    [Fintype n] [DecidableEq n] (φ : (n → S) ≃ₐ[S] (n → S)) (i : n) :
    φ (coordIdem (S := S) n i) (localPermutation (S := S) φ i) = 1 :=
  (algEquiv_coordIdem_support_unique (S := S) φ i).choose_spec.1


/-- The automorphism sends the coordinate idempotent at i to the coordinate
idempotent at the induced local coordinate permutation. -/
theorem algEquiv_coordIdem_eq_coordIdem [IsLocalRing S] {n : Type u}
    [Fintype n] [DecidableEq n] (φ : (n → S) ≃ₐ[S] (n → S)) (i : n) :
    φ (coordIdem (S := S) n i) = coordIdem (S := S) n (localPermutation (S := S) φ i) := by
  ext k
  let e : n → S := φ (coordIdem (S := S) n i)
  have he : IsIdempotentElem e := by
    show (φ (coordIdem (S := S) n i)) * (φ (coordIdem (S := S) n i)) =
      φ (coordIdem (S := S) n i)
    rw [← map_mul, (coordIdem_idem n i).eq]
  by_cases hk : k = localPermutation (S := S) φ i
  · subst hk
    rw [localPermutation_spec]
    simp [coordIdem]
  · have hcoord0 : coordIdem (S := S) n (localPermutation (S := S) φ i) k = 0 := by
      simp [coordIdem, hk]
    rw [hcoord0]
    rcases pi_idempotent_apply_eq_zero_or_one he k with h0 | h1
    · exact h0
    · exact False.elim (hk ((algEquiv_coordIdem_support_unique (S := S) φ i).unique h1
        (localPermutation_spec (S := S) φ i)))

/-- The local coordinate permutation is injective. -/
theorem localPermutation_injective [IsLocalRing S] {n : Type u}
    [Fintype n] [DecidableEq n] (φ : (n → S) ≃ₐ[S] (n → S)) :
    Function.Injective (localPermutation (S := S) φ) := by
  intro i j h
  have hcoord : φ (coordIdem (S := S) n i) = φ (coordIdem (S := S) n j) := by
    rw [algEquiv_coordIdem_eq_coordIdem (S := S) φ i,
      algEquiv_coordIdem_eq_coordIdem (S := S) φ j, h]
  have hci : coordIdem (S := S) n i = coordIdem (S := S) n j :=
    φ.injective hcoord
  have hcoordval := congrFun hci i
  by_cases hij : i = j
  · exact hij
  · simp [coordIdem, hij] at hcoordval

/-- The local coordinate permutation as a permutation. -/
noncomputable def localPermutationEquiv [IsLocalRing S] {n : Type u}
    [Fintype n] [DecidableEq n] (φ : (n → S) ≃ₐ[S] (n → S)) : Equiv.Perm n :=
  Equiv.ofBijective (localPermutation (S := S) φ)
    ⟨localPermutation_injective (S := S) φ,
      (Finite.injective_iff_surjective.mp (localPermutation_injective (S := S) φ))⟩


/-- Coordinate idempotents are moved by the pi-permutation algebra equivalence. -/
theorem piCongrLeft_coordIdem [IsLocalRing S] {n : Type u}
    [Fintype n] [DecidableEq n] (σ : Equiv.Perm n) (i : n) :
    (AlgEquiv.piCongrLeft S (fun _ : n => S) σ) (coordIdem (S := S) n i) =
      coordIdem (S := S) n (σ i) := by
  ext j
  rw [AlgEquiv.piCongrLeft_apply, Equiv.piCongrLeft_apply]
  by_cases h : j = σ i
  · simp [coordIdem, h]
  · have h' : σ.symm j ≠ i := fun hji => h (by simpa using congrArg σ hji)
    simp [coordIdem, h, h']

/-- Every S-algebra automorphism of S^n is induced by a coordinate permutation. -/
theorem localPiAlgEquiv_eq_perm [IsLocalRing S] {n : Type u}
    [Fintype n] [DecidableEq n] (φ : (n → S) ≃ₐ[S] (n → S)) :
    φ = AlgEquiv.piCongrLeft S (fun _ : n => S) (localPermutationEquiv (S := S) φ) := by
  let Ψ : (n → S) ≃ₐ[S] (n → S) :=
    AlgEquiv.piCongrLeft S (fun _ : n => S) (localPermutationEquiv (S := S) φ)
  have hcoord : ∀ i, φ (Pi.basisFun S n i) = Ψ (Pi.basisFun S n i) := by
    intro i
    rw [Pi.basisFun_apply]
    change φ (coordIdem (S := S) n i) = Ψ (coordIdem (S := S) n i)
    rw [algEquiv_coordIdem_eq_coordIdem (S := S) φ i]
    exact (piCongrLeft_coordIdem (S := S) (localPermutationEquiv (S := S) φ) i).symm
  have hlin : φ.toAlgHom.toLinearMap = Ψ.toAlgHom.toLinearMap :=
    (Pi.basisFun S n).ext hcoord
  apply AlgEquiv.ext
  intro x
  exact LinearMap.congr_fun hlin x


section PermutationFixedPoints

variable {G : Type u} [Group G] [Fintype G] (n : Type u) [MulAction G n] [Fintype n]

/-- Fixed points of the coordinate permutation action are functions on the
orbit quotient. -/
noncomputable def localFixedPointsEquivOrbitFunctions :
    FixedPoints.subalgebra S (n → S) G ≃ₐ[S]
      (MulAction.orbitRel.Quotient G n → S) :=
  PermutationTorsorQuotient.fixedPointsEquivOrbitFunctions (R := S) (G := G) (ι := n)

/-- The fixed subalgebra of the coordinate permutation action is finite etale
over the local base S (it is a finite free product of copies of S). -/
theorem localFixedPoints_finiteEtale [IsLocalRing S] :
    Algebra.Etale S (FixedPoints.subalgebra S (n → S) G) ∧
      Module.Finite S (FixedPoints.subalgebra S (n → S) G) :=
  PermutationTorsorQuotient.fixedPoints_finiteEtale_orbits (R := S) (G := G) (ι := n)


/-- Fixed-point equivalence for a coordinate permutation action given by a
monoid homomorphism G → Perm n. -/
noncomputable def localFixedPointsEquivOrbitFunctions_of_permHom
    (σ : G →* Equiv.Perm n) :
    letI : MulAction G n := MulAction.compHom n σ
    FixedPoints.subalgebra S (n → S) G ≃ₐ[S]
      (MulAction.orbitRel.Quotient G n → S) := by
  letI : MulAction G n := MulAction.compHom n σ
  exact localFixedPointsEquivOrbitFunctions (S := S) (G := G) n

/-- Fixed subalgebra of a coordinate permutation action is finite etale over S. -/
theorem localFixedPoints_finiteEtale_of_permHom [IsLocalRing S]
    (σ : G →* Equiv.Perm n) :
    letI : MulAction G n := MulAction.compHom n σ
    Algebra.Etale S (FixedPoints.subalgebra S (n → S) G) ∧
      Module.Finite S (FixedPoints.subalgebra S (n → S) G) := by
  letI : MulAction G n := MulAction.compHom n σ
  exact localFixedPoints_finiteEtale (S := S) (G := G) n

end PermutationFixedPoints

end SplitCaseLocalPermutation
