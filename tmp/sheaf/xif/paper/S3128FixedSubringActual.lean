import tmp.sheaf.xif.paper.S3128CoordinateRingTransferActual
import tmp.sheaf.xif.paper.S3128AffineQuotientActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
open LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
open LeanFormal.IUT.XiFPaper.S3128SignRankTwoActual
open LeanFormal.IUT.XiFPaper.S3128SignActionActual
open LeanFormal.IUT.XiFPaper.S3128CoordinateRingTransferActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
namespace LeanFormal.IUT.XiFPaper.S3128FixedSubringActual
variable {l : PrimeGeFive}
abbrev Kx (p : Polynomial (K l)) : S1348CoordinateRing l :=
  Polynomial.aeval (S3128x l) p

theorem S3128Kx_smul_y (p : Polynomial (K l)) :
    p • S3128y (l := l) = Kx p * S3128y (l := l) := by
  rw [Algebra.smul_def]
  congr 1
  change (S3119CoordinateRingEquiv l).symm
    ((algebraMap (Polynomial (K l)) (CR l)) p) = Kx p
  rw [← S3128CoordinateRingEquiv_aeval]
  simp [Kx]

theorem S3128NegQuotientHom_Kx (p : Polynomial (K l)) :
    S3119NegQuotientHom (l := l) (Kx p) = Kx p := by
  rw [← S3128SignGen_smul_eq_hom]
  exact S3128SignGen_smul_Kx p

theorem S3128exists_decomp (a : S1348CoordinateRing l) :
    ∃ p q : Polynomial (K l), a = Kx p + Kx q * S3128y (l := l) := by
  let p := (S3128Basis (l := l)).repr a 0
  let q := (S3128Basis (l := l)).repr a 1
  refine ⟨p, q, ?_⟩
  have h := (S3128Basis (l := l)).sum_repr a
  rw [Fin.sum_univ_two] at h
  rw [S3128Basis_zero, S3128Basis_one, S3128Kx_smul_one,
    S3128Kx_smul_y] at h
  exact h.symm

theorem S3128gen_smul_decomp (p q : Polynomial (K l)) :
    S3128SignGen • (Kx p + Kx q * S3128y (l := l)) =
      Kx p + Kx q * (-S3128y (l := l) - S3128x (l := l)) := by
  rw [S3128SignGen_smul_eq_hom, map_add, map_mul]
  rw [show S3119NegQuotientHom (l := l) (Kx p) = Kx p from by
        rw [← S3128SignGen_smul_eq_hom]; exact S3128SignGen_smul_Kx p]
  rw [show S3119NegQuotientHom (l := l) (Kx q) = Kx q from by
        rw [← S3128SignGen_smul_eq_hom]; exact S3128SignGen_smul_Kx q]
  rw [show S3119NegQuotientHom (l := l) (S3128y l) =
        -S3128y l - S3128x l from by
      rw [← S3128SignGen_smul_eq_hom]; exact S3128SignGen_smul_y]

theorem S3128_invariant_mem_range (a : S1348CoordinateRing l)
    (ha : ∀ g : S3128SignGroup, g • a = a) :
    ∃ p : Polynomial (K l), Kx p = a := by
  obtain ⟨p, q, rfl⟩ := S3128exists_decomp a
  have hgen : S3128SignGen • (Kx p + Kx q * S3128y (l := l)) =
      Kx p + Kx q * S3128y (l := l) := ha S3128SignGen
  rw [S3128gen_smul_decomp] at hgen
  have hzero : Kx q * S3128t (l := l) = 0 := by
    rw [S3128t]
    linear_combination -hgen
  have hq0 : Kx q = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact (S3128t_ne_zero h).elim
  have hq : q = 0 := by
    have hy : q • S3128y (l := l) = 0 := by
      rw [S3128Kx_smul_y, hq0, zero_mul]
    have hy' : q • S3128Basis (l := l) 1 = 0 := by
      simpa [S3128Basis_one] using hy
    have hc := congrArg (fun z => (S3128Basis (l := l)).repr z 1) hy'
    simpa [S3128Basis.repr_self] using hc
  refine ⟨p, ?_⟩
  rw [hq]
  change Kx p = Kx p + Kx (0 : Polynomial (K l)) * S3128y (l := l)
  rw [show Kx (0 : Polynomial (K l)) = 0 from map_zero _]
  simp

theorem S3128_fixedSubring_eq_range :
    S3128FixedSubring S3128SignGroup (S1348CoordinateRing l) =
      (Polynomial.aeval (R := K l) (S3128x l)).range.toSubring := by
  ext a
  constructor
  · intro ha
    have ha' : ∀ g : S3128SignGroup, g • a = a := by
      simpa [S3128FixedSubring] using ha
    obtain ⟨p, hp⟩ := S3128_invariant_mem_range a ha'
    change a ∈ (Polynomial.aeval (R := K l) (S3128x l)).range
    rw [AlgHom.mem_range]
    exact ⟨p, hp⟩
  · intro ha
    change a ∈ (Polynomial.aeval (R := K l) (S3128x l)).range at ha
    rw [AlgHom.mem_range] at ha
    obtain ⟨p, hp⟩ := ha
    change ∀ g : S3128SignGroup, g • a = a
    rw [← hp]
    intro g
    fin_cases g <;> simp [S3128Sign_smul_def, S3128SignSmul,
      S3128NegQuotientHom_Kx]

theorem S3128Kx_eq_zero {p : Polynomial (K l)}
    (h : Kx p = 0) : p = 0 := by
  have h1 : p • (1 : S1348CoordinateRing l) = 0 := by
    rw [S3128Kx_smul_one,
      show (Polynomial.aeval (S3128x l)) p = Kx p from rfl, h]
  have h2 : p • S3128Basis (l := l) 0 = 0 := by
    simpa [S3128Basis_zero] using h1
  have hc := congrArg (fun z => (S3128Basis (l := l)).repr z 0) h2
  simpa [S3128Basis.repr_self] using hc

theorem S3128Kx_injective : Function.Injective (Kx (l := l)) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply S3128Kx_eq_zero
  have hpq' : (Polynomial.aeval (S3128x l)) p =
      (Polynomial.aeval (S3128x l)) q := by
    simpa [Kx] using hpq
  change (Polynomial.aeval (S3128x l)) (p - q) = 0
  rw [map_sub, hpq', sub_self]

noncomputable def S3128KxEquiv :
    Polynomial (K l) ≃ₐ[K l]
      (Polynomial.aeval (R := K l) (S3128x l)).range :=
  AlgEquiv.ofInjective (Polynomial.aeval (R := K l) (S3128x l))
    S3128Kx_injective

noncomputable instance S3128FixedSubringAlgebra :
    Algebra (S3128FixedSubring S3128SignGroup (S1348CoordinateRing l))
      (S1348CoordinateRing l) :=
  (S3128FixedSubring S3128SignGroup (S1348CoordinateRing l)).subtype.toAlgebra

noncomputable def S3128KxRingHom :
    Polynomial (K l) →+*
      S3128FixedSubring S3128SignGroup (S1348CoordinateRing l) where
  toFun p := ⟨Kx p, by
    rw [S3128_fixedSubring_eq_range]
    exact ⟨p, rfl⟩⟩
  map_one' := by ext; simp [Kx]
  map_mul' := by intro p q; ext; simp [Kx, map_mul]
  map_zero' := by ext; simp [Kx]
  map_add' := by intro p q; ext; simp [Kx, map_add]

noncomputable def S3128KxRingEquiv :
    Polynomial (K l) ≃+*
      S3128FixedSubring S3128SignGroup (S1348CoordinateRing l) :=
  RingEquiv.ofBijective S3128KxRingHom ⟨by
    intro p q h
    apply S3128Kx_injective
    simpa [S3128KxRingHom] using congrArg Subtype.val h, by
    intro s
    have hs : ∀ g : S3128SignGroup, g • s.val = s.val := s.property
    obtain ⟨p, hp⟩ := S3128_invariant_mem_range s.val hs
    exact ⟨p, by ext; simpa [S3128KxRingHom] using hp⟩⟩

noncomputable instance S3128KxRingHomInvPair :
    RingHomInvPair (S3128KxRingEquiv (l := l)).toRingHom
      (S3128KxRingEquiv (l := l)).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (S3128KxRingEquiv (l := l))

noncomputable instance S3128KxRingHomInvPairSymm :
    RingHomInvPair (S3128KxRingEquiv (l := l)).symm.toRingHom
      (S3128KxRingEquiv (l := l)).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (S3128KxRingEquiv (l := l))

noncomputable def S3128FreeLinearEquiv :
    LinearEquiv (σ := (S3128KxRingEquiv (l := l)).toRingHom)
      (σ' := (S3128KxRingEquiv (l := l)).symm.toRingHom)
      (S1348CoordinateRing l) (S1348CoordinateRing l) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' p a := by
    change p • a = (S3128KxRingEquiv (l := l) p) • a
    rw [Algebra.smul_def, Algebra.smul_def]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, S3128Kx_smul_one]
    rfl

noncomputable instance S3128ModuleFreeFixed :
    Module.Free (S3128FixedSubring S3128SignGroup (S1348CoordinateRing l))
      (S1348CoordinateRing l) :=
  Module.Free.of_equiv (S3128FreeLinearEquiv (l := l))

noncomputable instance S3128ModuleFlatFixed :
    Module.Flat (S3128FixedSubring S3128SignGroup (S1348CoordinateRing l))
      (S1348CoordinateRing l) :=
  Module.Flat.of_free

#check S3128FreeLinearEquiv
#check S3128ModuleFreeFixed
#check S3128ModuleFlatFixed
#check S3128KxRingHom
#check S3128KxRingEquiv
#check S3128FixedSubringAlgebra
#check S3128Kx_eq_zero
#check S3128Kx_injective
#check S3128KxEquiv
#check S3128_fixedSubring_eq_range
#check S3128_invariant_mem_range
#check S3128exists_decomp
end LeanFormal.IUT.XiFPaper.S3128FixedSubringActual
end
