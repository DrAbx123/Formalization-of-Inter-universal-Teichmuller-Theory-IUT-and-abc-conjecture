import tmp.sheaf.xif.paper.S2537ConcreteLocalizationActual
import tmp.sheaf.xif.paper.S2540AbstractPermBarActual
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
namespace LeanFormal.IUT.XiFPaper.S2541ConcreteRedRootActual
attribute [local instance] Ideal.Quotient.field
local instance : IsFractionRing A K :=
  IsIntegralClosure.isFractionRing_of_finite_extension ℤ ℚ K A
theorem h10K_ne : algebraMap A K (10 : A) ≠ 0 := by
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  exact hAK.ne h10A
noncomputable def liftRK_hy : ∀ m : M, IsUnit (algebraMap A K (m : A)) := by
  intro m
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m : A) (10 : A)).mp m.2
  rw [← hn, map_pow]
  exact IsUnit.pow n (isUnit_iff_ne_zero.mpr h10K_ne)
noncomputable def liftRK : R →+* K :=
  IsLocalization.lift (M := M) (g := algebraMap A K) liftRK_hy
lemma liftRK_comp : liftRK.comp (algebraMap A R) = algebraMap A K :=
  IsLocalization.lift_comp _
noncomputable instance : Algebra R K := liftRK.toAlgebra
local instance : SMul R K := Algebra.toSMul
local instance : SMul A K := Algebra.toSMul
local instance : SMul K L := Algebra.toSMul
local instance : SMul R L := Algebra.toSMul
local instance : SMul A L := Algebra.toSMul
noncomputable instance : IsScalarTower A R K := by
  apply IsScalarTower.of_algebraMap_eq'
  ext a
  exact (DFunLike.congr_fun liftRK_comp a).symm
noncomputable instance : IsFractionRing R K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (R := A) (M := M) R K
noncomputable instance : IsScalarTower R K L := by
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext M
  change liftAL.comp (algebraMap A R) =
    (algebraMap K L).comp (liftRK.comp (algebraMap A R))
  rw [liftAL_comp, liftRK_comp]
  exact (IsScalarTower.algebraMap_eq A K L).symm
noncomputable instance : FaithfulSMul R L := by
  rw [faithfulSMul_iff_algebraMap_injective]
  rw [IsScalarTower.algebraMap_eq R K L]
  exact (RingHom.injective (algebraMap K L)).comp (IsFractionRing.injective R K)

#check (inferInstance : IsFractionRing R K)
#check (inferInstance : IsScalarTower R K L)

noncomputable instance : IsDomain R := (IsFractionRing.injective R K).isDomain
noncomputable instance : IsIntegralClosure S R L := S2537_isIntegralClosure
noncomputable instance : IsDomain S := (IsIntegralClosure.algebraMap_injective S R L).isDomain

open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
open LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual

theorem concrete_redRoot_bijective
    (f : R[X]) (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] [P.IsMaximal]
    (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap R L)).Splits) :
    Function.Bijective
      (redRoot (f := f) (p := p) (P := P) (hmonic := hmonic)) :=
  redRoot_bijective (f := f) (p := p) (P := P)
    (hmonic := hmonic) (hsep := hsep) (hsplit := hsplit)

noncomputable def concrete_permBar
    (f : R[X]) (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] [P.IsMaximal]
    (hmonic : f.Monic) (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap R L)).Splits)
    [Fintype (R ⧸ p)] [Fintype (S ⧸ P)] :
    Equiv.Perm ((fbar f p).rootSet (S ⧸ P)) :=
  permBar (f := f) (p := p) (P := P)

#print axioms concrete_redRoot_bijective
#print axioms concrete_permBar

#check (inferInstance : FaithfulSMul R L)
end LeanFormal.IUT.XiFPaper.S2541ConcreteRedRootActual
end
