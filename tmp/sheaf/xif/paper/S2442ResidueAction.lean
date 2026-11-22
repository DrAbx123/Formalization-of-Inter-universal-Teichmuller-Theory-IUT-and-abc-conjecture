import tmp.sheaf.xif.paper.S2442InertiaAPI
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2442ResidueAction

open LeanFormal.IUT

variable (p : Nat) [Fact (Nat.Prime p)]

abbrev PadicValuationSubring (p : Nat) [Fact (Nat.Prime p)] : Type :=
  (Valued.v (R := PadicAlgCl p)).valuationSubring

abbrev PadicResidueField (p : Nat) [Fact (Nat.Prime p)] : Type :=
  IsLocalRing.ResidueField (PadicValuationSubring p)

theorem PadicAlgCl_norm_map (σ : LocalAbsoluteGalois p) (x : PadicAlgCl p) :
    ‖σ x‖ = ‖x‖ := by
  have h := spectralNorm_eq_of_equiv (K := ℚ_[p]) (L := PadicAlgCl p) σ x
  simpa [PadicAlgCl.spectralNorm_eq] using h.symm

theorem PadicAlgCl_valuation_map_eq (σ : LocalAbsoluteGalois p) (x : PadicAlgCl p) :
    Valued.v (σ x) = Valued.v x := by
  apply NNReal.coe_injective
  rw [PadicAlgCl.valuation_coe, PadicAlgCl.valuation_coe, PadicAlgCl_norm_map]

noncomputable def PadicValuationSubringAut (σ : LocalAbsoluteGalois p) :
    PadicValuationSubring p ≃+* PadicValuationSubring p where
  toFun x := ⟨σ x, by
    have hx : Valued.v (x : PadicAlgCl p) ≤ 1 := x.2
    rw [Valuation.mem_valuationSubring_iff]
    rw [PadicAlgCl_valuation_map_eq]
    exact hx⟩
  invFun x := ⟨σ.symm x, by
    have hx : Valued.v (x : PadicAlgCl p) ≤ 1 := x.2
    rw [Valuation.mem_valuationSubring_iff]
    rw [PadicAlgCl_valuation_map_eq]
    exact hx⟩
  left_inv := by
    intro x
    apply Subtype.ext
    simp
  right_inv := by
    intro x
    apply Subtype.ext
    simp
  map_mul' := by
    intro x y
    apply Subtype.ext
    simp
  map_add' := by
    intro x y
    apply Subtype.ext
    simp

noncomputable def PadicValuationSubringAction :
    LocalAbsoluteGalois p →* RingAut (PadicValuationSubring p) where
  toFun := PadicValuationSubringAut p
  map_one' := by
    ext x
    rfl
  map_mul' := by
    intro σ τ
    ext x
    rfl

noncomputable def PadicResidueAction :
    LocalAbsoluteGalois p →* RingAut (PadicResidueField p) :=
  (IsLocalRing.ResidueField.mapAut).comp (PadicValuationSubringAction p)

/-- Kernel of the residue-field action. -/
def PadicResidueKernel : Subgroup (LocalAbsoluteGalois p) :=
  (PadicResidueAction p).ker

instance PadicResidueKernel_normal : (PadicResidueKernel p).Normal :=
  MonoidHom.normal_ker (PadicResidueAction p)

/-- Exact missing: the residue-kernel equals the prime-to-p torsion inertia. -/
def PadicResidueKernelEqualsInertia : Prop :=
  PadicResidueKernel p =
    LeanFormal.IUT.XiFPaper.S2442InertiaAPI.PadicAbsoluteGaloisInertia p

/-- Exact missing: residue action reaches the full Gal(Fpbar/Fp) (surjectivity). -/
def PadicResidueActionSurjective : Prop :=
  Function.Surjective (PadicResidueAction p)

#check PadicValuationSubringAut
#check PadicResidueAction
#check PadicResidueKernel
#check PadicResidueKernel_normal
#check PadicResidueKernelEqualsInertia
#check PadicResidueActionSurjective
#print axioms PadicValuationSubringAut
#print axioms PadicResidueAction
#print axioms PadicResidueKernel_normal

end LeanFormal.IUT.XiFPaper.S2442ResidueAction

end