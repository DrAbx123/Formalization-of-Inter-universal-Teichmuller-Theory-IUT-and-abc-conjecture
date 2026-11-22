import tmp.sheaf.xif.paper.S2687Split2161Actual
import tmp.sheaf.xif.paper.S2696GaussianPlace2161Actual
noncomputable section
open LeanFormal.IUT
namespace LeanFormal.IUT.XiFPaper.S2698RingOfIntegersBridgeActual
local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
abbrev O := NumberField.RingOfIntegers GaussianField
abbrev RO := NumberField.RingOfIntegers ℚ
theorem algebraMap_bridge (z : ℤ) :
    (algebraMap ℤ O z) = algebraMap RO O (Rat.ringOfIntegersEquiv.symm z) := by
  apply NumberField.RingOfIntegers.coe_injective
  simp
theorem comap_bridge (I : Ideal O) :
    Ideal.comap (algebraMap RO O) I =
      Ideal.comap (Rat.ringOfIntegersEquiv : RO →+* ℤ)
        (Ideal.comap (algebraMap ℤ O) I) := by
  ext y
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap]
  change (algebraMap RO O) y ∈ I ↔
    (algebraMap ℤ O) (Rat.ringOfIntegersEquiv y) ∈ I
  constructor
  · intro hy
    have h := algebraMap_bridge (Rat.ringOfIntegersEquiv y)
    rw [← h]
    simpa using hy
  · intro hy
    have h := algebraMap_bridge (Rat.ringOfIntegersEquiv y)
    rw [h] at hy
    simpa using hy

#check algebraMap_bridge
#check comap_bridge
#print axioms comap_bridge
end LeanFormal.IUT.XiFPaper.S2698RingOfIntegersBridgeActual
end