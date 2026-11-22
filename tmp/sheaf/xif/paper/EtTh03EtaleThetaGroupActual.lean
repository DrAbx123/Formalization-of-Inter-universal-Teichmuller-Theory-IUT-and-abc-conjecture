import LeanFormal.IUT.IUTII.Theta.EtaleThetaQuotient
import LeanFormal.IUT.IUTII.Theta.EtaleTateDirection

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: theta group|EtaleThetaQuotient|EtaleTateDirection -> hits IUTII/Theta/EtaleThetaQuotient.lean:29/32/40/43/46/50/58, EtaleTateDirection.lean:17/20/24/28/32/35/39/51/54 -> REUSE (aliases; no re-proof).

# [EtTh] 03: etale theta quotient layer (theta group / Tate direction) - tree reuse

Corpus: papers/motizuki_corpus/text/The Etale Theta Function and its Frobenioid-theoretic
Manifestations.txt (theta groups and their lower-central quotients).
Tree realization reused: thetaDerivedSubgroup / thetaCommutatorKernel /
ThetaQuotient / EllipticAbelianization / thetaToElliptic (EtaleThetaQuotient:29-58);
integral Tate direction: integralTateReduction surjectivity/kernel and the canonical
generator order (EtaleTateDirection:17-54).  HONEST LIMIT (file header of
EtaleThetaQuotient): this is the algebraic quotient layer only; the geometric
fundamental group, profinite topology and etale realization are later obligations.
-/

namespace LeanFormal.IUT.XiFPaper.EtTh03EtaleThetaGroupActual

open LeanFormal.IUT

universe u

variable (G : Type u) [Group G]

/-- The theta commutator kernel is normal (tree instance). -/
theorem etTh_thetaCommutatorKernel_normal : (thetaCommutatorKernel G).Normal :=
  inferInstance

/-- The theta commutator kernel lies in the derived subgroup (reused from
EtaleThetaQuotient:46). -/
theorem etTh_thetaCommutatorKernel_le_derivedSubgroup :
    thetaCommutatorKernel G ≤ thetaDerivedSubgroup G :=
  thetaCommutatorKernel_le_derivedSubgroup G

variable (l : PrimeGeFive)

/-- The integral Tate reduction is surjective (reused from EtaleTateDirection:24). -/
theorem etTh_integralTateReduction_surjective :
    Function.Surjective (integralTateReduction l) :=
  integralTateReduction_surjective l

/-- The integral Tate reduction kernel is the multiples of the prime label
(reused from EtaleTateDirection:28). -/
theorem etTh_integralTateReduction_kernel :
    (integralTateReduction l).ker = AddSubgroup.zmultiples (l.value : ℤ) :=
  integralTateReduction_kernel l

#check etTh_thetaCommutatorKernel_normal
#check etTh_thetaCommutatorKernel_le_derivedSubgroup
#check etTh_integralTateReduction_surjective
#check etTh_integralTateReduction_kernel

end LeanFormal.IUT.XiFPaper.EtTh03EtaleThetaGroupActual