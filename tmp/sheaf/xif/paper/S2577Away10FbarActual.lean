import tmp.sheaf.xif.paper.S2537ConcreteLocalizationActual
import tmp.sheaf.xif.paper.S2541ConcreteRedRootActual
import tmp.sheaf.xif.paper.S2584PrimeDegreeOneActual
import tmp.sheaf.xif.paper.S2553Mod613DegreeActual
import tmp.sheaf.xif.paper.S2572F613IrreducibleActual
import tmp.sheaf.xif.paper.S2003Psi5ModelActual

noncomputable section
set_option maxHeartbeats 16000000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2541ConcreteRedRootActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2553Mod613DegreeActual
open LeanFormal.IUT.XiFPaper.S2572F613IrreducibleActual
open LeanFormal.IUT.XiFPaper.S2003Psi5ModelActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual

namespace LeanFormal.IUT.XiFPaper.S2577Away10FbarActual

abbrev O : Type := A
abbrev A10 : Type := R
abbrev K : Type := S1720Field

noncomputable def W : S2584PrimeDegreeOneWitness :=
  Classical.choice S2584_witness_nonempty

noncomputable def g : O →+* ZMod 613 :=
  W.residueEquiv.toRingHom.comp (Ideal.Quotient.mk W.p)

lemma ten_not_mem_p : (10 : O) ∉ W.p := by
  intro hx
  have h10_under : (10 : ℤ) ∈ W.p.under ℤ := by
    rw [Ideal.mem_under]
    simpa using hx
  have hspan : (10 : ℤ) ∈ Ideal.span {(613 : ℤ)} := by
    rw [W.p_liesOver.over]
    exact h10_under
  have hdvd := Ideal.mem_span_singleton.mp hspan
  norm_num at hdvd

lemma g_ten_ne_zero : g (10 : O) ≠ 0 := by
  intro h0
  have hmk : Ideal.Quotient.mk W.p (10 : O) = 0 := by
    apply W.residueEquiv.injective
    rw [map_zero]
    simpa [g] using h0
  exact ten_not_mem_p (Ideal.Quotient.eq_zero_iff_mem.mp hmk)

lemma hgUnit : ∀ y : Submonoid.powers (10 : O), IsUnit (g y) := by
  intro y
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y.1 (10 : O)).mp y.2
  rw [← hn, map_pow]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero n g_ten_ne_zero)

noncomputable def φ10 : A10 →+* ZMod 613 :=
  IsLocalization.lift (M := Submonoid.powers (10 : O)) (S := A10)
    (P := ZMod 613) (g := g) hgUnit

lemma φ10_comp_algebraMap : φ10.comp (algebraMap O A10) = g :=
  IsLocalization.lift_comp (M := Submonoid.powers (10 : O)) (S := A10)
    (P := ZMod 613) (g := g) hgUnit

lemma φ10_comp_int : φ10.comp (algebraMap ℤ A10) = Int.castRingHom (ZMod 613) := by
  rw [IsScalarTower.algebraMap_eq ℤ O A10, ← RingHom.comp_assoc, φ10_comp_algebraMap]
  ext z
  simp [g]

lemma φ10_surjective : Function.Surjective φ10 := by
  intro z
  obtain ⟨x, rfl⟩ := W.residueEquiv.surjective z
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨algebraMap O A10 c, ?_⟩
  rw [show φ10 (algebraMap O A10 c) = g c by
    rw [← RingHom.comp_apply, φ10_comp_algebraMap]]
  rfl

def p10 : Ideal A10 := RingHom.ker φ10

lemma p10_max : p10.IsMaximal := RingHom.ker_isMaximal_of_surjective φ10 φ10_surjective

noncomputable def e : A10 ⧸ p10 ≃+* ZMod 613 :=
  RingHom.quotientKerEquivOfSurjective φ10_surjective

lemma S2003Psi5Z_map_K :
    S2132Psi5Z.map (Int.castRingHom K) =
      Polynomial.C ((2 : K) ^ 36) * S2057Psi5F := by
  have h := congrArg (Polynomial.map (algebraMap ℚ K)) S2003Psi5Z_model
  have hcompQ : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K := by
    ext z; simp
  simpa [S2057Psi5F, Polynomial.map_map, Polynomial.map_mul, Polynomial.map_C,
    hcompQ, map_pow] using h

lemma algebraMap_RK_comp : (algebraMap A10 K).comp (algebraMap O A10) = algebraMap O K := by
  simpa [RingHom.algebraMap_toAlgebra] using liftRK_comp

def lead : O := 343597383680

def u : A10 := algebraMap O A10 ((5 : O) ^ 35) *
  (IsLocalization.Away.invSelf (10 : O)) ^ 36

lemma lead_mul_five : lead * (5 : O) ^ 35 = (10 : O) ^ 36 := by
  norm_num [lead]

lemma u_mul_lead : algebraMap O A10 lead * u = 1 := by
  unfold u
  rw [← mul_assoc, ← map_mul, lead_mul_five, map_pow, ← mul_pow]
  rw [show algebraMap O A10 (10 : O) * IsLocalization.Away.invSelf (10 : O) = 1 from
    IsLocalization.Away.mul_invSelf (S := A10) (x := (10 : O))]
  norm_num

def f10' : A10[X] := C u * S2132Psi5Z.map (algebraMap ℤ A10)

lemma f10'_coeff_12 : f10'.coeff 12 = 1 := by
  unfold f10'
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
  have hcoeffZ : S2132Psi5Z.coeff 12 = (343597383680 : ℤ) := by
    unfold S2132Psi5Z
    norm_num [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_pow]
  rw [hcoeffZ]
  rw [show algebraMap ℤ A10 (343597383680 : ℤ) = algebraMap O A10 lead by
    rw [IsScalarTower.algebraMap_apply ℤ O A10]
    norm_num [lead]]
  rw [mul_comm]
  exact u_mul_lead

lemma f10'_natDegree_le : f10'.natDegree ≤ 12 := by
  unfold f10'
  calc (C u * S2132Psi5Z.map (algebraMap ℤ A10)).natDegree
      ≤ (S2132Psi5Z.map (algebraMap ℤ A10)).natDegree := natDegree_C_mul_le _ _
    _ ≤ S2132Psi5Z.natDegree := Polynomial.natDegree_map_le
    _ ≤ 12 := by unfold S2132Psi5Z; compute_degree!

lemma f10'_natDegree : f10'.natDegree = 12 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero f10'_natDegree_le
  rw [f10'_coeff_12]
  norm_num

theorem f10'_monic : f10'.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, f10'_natDegree, f10'_coeff_12]

lemma f10'_map_scalar :
    f10'.map (algebraMap A10 K) =
      Polynomial.C ((5 : K)⁻¹) * S2057Psi5F := by
  unfold f10'
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map]
  have hcomp : (algebraMap A10 K).comp (algebraMap ℤ A10) = Int.castRingHom K := by
    rw [IsScalarTower.algebraMap_eq ℤ O A10, ← RingHom.comp_assoc, algebraMap_RK_comp]
    ext z; simp
  rw [hcomp, S2003Psi5Z_map_K]
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  have hmul : algebraMap O K lead * algebraMap A10 K u = 1 := by
    have h := congrArg (algebraMap A10 K) u_mul_lead
    simpa [map_mul, IsScalarTower.algebraMap_apply O A10 K] using h
  have hleadK : algebraMap O K lead = (2 : K) ^ 36 * 5 := by
    rw [show lead = algebraMap ℤ O (343597383680 : ℤ) from rfl]
    rw [← IsScalarTower.algebraMap_apply ℤ O K]
    norm_num
  have hB : algebraMap A10 K u = ((2 : K) ^ 36 * 5)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    simpa [hleadK] using hmul
  rw [hB]
  field_simp

lemma u_isUnit : IsUnit u :=
  isUnit_iff_exists.mpr ⟨algebraMap O A10 lead, by
    rw [mul_comm]; exact u_mul_lead, u_mul_lead⟩

lemma f10'_map_φ :
    f10'.map φ10 = Polynomial.C (φ10 u) *
      S2132Psi5Z.map (Int.castRingHom (ZMod 613)) := by
  unfold f10'
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, φ10_comp_int]

lemma f10'_map_φ_irreducible : Irreducible (f10'.map φ10) := by
  rw [f10'_map_φ]
  apply (irreducible_isUnit_mul (isUnit_C.mpr (u_isUnit.map φ10))).mpr
  rw [← F613_eq_map]
  exact F613_irreducible

abbrev fbar10 : (A10 ⧸ p10)[X] := f10'.map (Ideal.Quotient.mk p10)

lemma quotient_comp : e.toRingHom.comp (Ideal.Quotient.mk p10) = φ10 := by
  ext x
  change (RingHom.quotientKerEquivOfSurjective φ10_surjective)
    (Ideal.Quotient.mk p10 x) = φ10 x
  exact RingHom.quotientKerEquivOfSurjective_apply_mk (f := φ10) φ10_surjective x

lemma fbar10_map_e : f10'.map φ10 = fbar10.map e.toRingHom := by
  rw [show φ10 = e.toRingHom.comp (Ideal.Quotient.mk p10) from quotient_comp.symm]
  rw [Polynomial.map_map]

theorem fbar10_irreducible : Irreducible fbar10 := by
  have hI' : Irreducible (fbar10.map e.toRingHom) := by
    rw [← fbar10_map_e]
    exact f10'_map_φ_irreducible
  have heI : Irreducible ((Polynomial.mapEquiv e) fbar10) := by
    simpa [Polynomial.mapEquiv] using hI'
  exact (MulEquiv.irreducible_iff (f := Polynomial.mapEquiv e)).mp heI

theorem fbar10_natDegree : fbar10.natDegree = 12 := by
  have hdeg : (f10'.map φ10).natDegree = 12 := by
    rw [f10'_map_φ]
    rw [Polynomial.natDegree_C_mul (IsUnit.ne_zero (u_isUnit.map φ10))]
    rw [← F613_eq_map, F613_natDegree]
  have h := congrArg Polynomial.natDegree fbar10_map_e
  rw [Polynomial.natDegree_map_eq_of_injective (f := e.toRingHom) e.injective] at h
  exact h.symm.trans hdeg

#check f10'_monic
#check f10'_map_scalar
#check fbar10_irreducible
#check fbar10_natDegree
#print axioms f10'_monic
#print axioms f10'_map_scalar
#print axioms fbar10_irreducible
#print axioms fbar10_natDegree

end LeanFormal.IUT.XiFPaper.S2577Away10FbarActual
end