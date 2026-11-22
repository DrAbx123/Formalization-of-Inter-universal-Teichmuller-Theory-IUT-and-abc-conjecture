import tmp.sheaf.xif.paper.Mzk1Ind1ValuationDataActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparison
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1KernelIntegersActual
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NormalizedLogNormComparison
open LeanFormal.IUT.XiFPaper.Mzk1Ind1ValuationDataActual
open scoped Valued

abbrev completionField := LeanFormal.IUT.NormalizedLogNormComparison.completionField

theorem completion_valued_one_iff_norm_one {u : completionField} (hu : u ≠ 0) :
    (Valued.v u : WithZero (Multiplicative ℤ)) = 1 ↔ ‖u‖ = 1 :=
  (norm_one_iff_valued_one hu).symm

def completionIntegersToFieldUnits (u : (Integers completionField)ˣ) :
    completionFieldˣ :=
  Units.map (Subring.subtype (Integers completionField)).toMonoidHom u


def completionKernelToIntegers
    (u : (unitValuationHom (F := completionField)).ker) :
    (Integers completionField)ˣ := by
  exact unitOfNormOne ⟨((u : completionFieldˣ) : completionField), by
    exact (completion_valued_one_iff_norm_one
      (Units.ne_zero (u : completionFieldˣ))).mp
      ((unitValuationHom_eq_one_iff (F := completionField)
        (u : completionFieldˣ)).mp (MonoidHom.mem_ker.mp u.2))⟩

def completionIntegersToKernel
    (u : (Integers completionField)ˣ) :
    (unitValuationHom (F := completionField)).ker := by
  exact ⟨completionIntegersToFieldUnits u, by
    rw [MonoidHom.mem_ker]
    exact (unitValuationHom_eq_one_iff (F := completionField)
      (completionIntegersToFieldUnits u)).mpr
      ((completion_valued_one_iff_norm_one
        (Units.ne_zero (completionIntegersToFieldUnits u))).mpr
        (by simpa [completionIntegersToFieldUnits] using norm_unit_eq_one u))⟩

#print axioms completionKernelToIntegers
#print axioms completionIntegersToKernel


noncomputable def completionKernelEquivIntegers :
    (unitValuationHom (F := completionField)).ker ≃*
      (Integers completionField)ˣ where
  toFun := completionKernelToIntegers
  invFun := completionIntegersToKernel
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv u := by
    apply Units.ext
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Units.ext
    apply Subtype.ext
    rfl


abbrev completionWQuotient : Type :=
  (Integers completionField)ˣ ⧸ CommGroup.torsion (Integers completionField)ˣ

instance completionWQuotientNormal :
    (CommGroup.torsion (Integers completionField)ˣ).Normal :=
  Subgroup.normal_of_comm _

instance completionKernelTorsionNormal :
    (CommGroup.torsion (unitValuationHom (F := completionField)).ker).Normal :=
  Subgroup.normal_of_comm _

noncomputable def completionKernelTimesMuEquiv :
    ((unitValuationHom (F := completionField)).ker ⧸
        CommGroup.torsion (unitValuationHom (F := completionField)).ker) ≃*
      completionWQuotient :=
  QuotientGroup.congr
    (CommGroup.torsion (unitValuationHom (F := completionField)).ker)
    (CommGroup.torsion (Integers completionField)ˣ)
    completionKernelEquivIntegers completionKernelEquivIntegers.map_torsion

#print axioms completionKernelTimesMuEquiv

#print axioms completionKernelEquivIntegers

#print axioms completionIntegersToFieldUnits
end LeanFormal.IUT.XiFPaper.Mzk1Ind1KernelIntegersActual