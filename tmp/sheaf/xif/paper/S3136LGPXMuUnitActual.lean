import tmp.sheaf.xif.paper.S3136LGPLocalMonoidActual

/-! # Stage-4 host: candidate X-mu unit-group portion of the LGP X-mu prime-strip

Source anchors: IUT III, Prop. 3.7, (iii), (iv) (pp. 109--111);
IUT III, Def. 3.8, (i), (ii) (pp. 112--113).  The F^LGP x mu-prime-strip needs
both a value-group (boxplus-triangle) portion and a unit-group (x mu) portion.
The unit-group portion records the actual units modulo the mu_{2l}-ambiguity of
the 2l-th roots of the theta values (IUT III, Prop. 3.4, (ii); the 2l-th root
normalization).

This file constructs the actual CANDIDATE unit-group portion from the actual
unit group of the algebraic closure of the completion, the actual mu_{2l} root
set, and the actual 2l-th root data:
* muTwoLAlgClosedSubgroup: the actual mu_{2l} subgroup of the unit group;
* LGPXMuUnitCandidate: the actual mu_{2l}-quotient of the unit group together
  with the canonical root class and its 2l-th power relation;
* rootClass_wellDefined: any two actual 2l-th roots give the same quotient
  class (the mu_{2l}-ambiguity is exactly absorbed);
* LGPXMuUnitIdentificationMissing: the exact additional data needed to
  identify this candidate with the paper's X-mu unit-group portion (IUT III,
  Prop. 3.7, (iii), (iv); Def. 3.8, (i), (ii)).

LABEL: prerequisite component only, NOT the paper's X-mu-prime-strip.  Consumer:
lattice stream, IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPXMuUnitActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.LGPThetaActionActual
open LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.S3136LGPLocalMonoidActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual mu_{2l} subgroup of the unit group of the algebraic closure of the
completion: the units whose (2l)-th power is 1. -/
def muTwoLAlgClosedSubgroup (b : Bad (nativePlaceSelection T)) :
    Subgroup (AlgebraicClosure (Completion (qVPlace T b)))ˣ where
  carrier := muTwoLAlgClosed (l := l) T b
  one_mem' := by
    change (1 : (AlgebraicClosure (Completion (qVPlace T b)))ˣ) ^ (2 * l.value) = 1
    rw [one_pow]
  mul_mem' := by
    intro a c ha hc
    change (a * c) ^ (2 * l.value) = 1
    rw [mul_pow, ha, hc, mul_one]
  inv_mem' := by
    intro a ha
    change a⁻¹ ^ (2 * l.value) = 1
    rw [inv_pow, ha, inv_one]

/-- The candidate X-mu unit-group portion: the mu_{2l}-quotient of the actual unit
group, with the canonical root class. -/
structure LGPXMuUnitCandidate (b : Bad (nativePlaceSelection T)) where
  /-- The actual mu_{2l} subgroup of the actual unit group. -/
  muSubgroup : Subgroup (AlgebraicClosure (Completion (qVPlace T b)))ˣ
  /-- The canonical root class in the mu_{2l}-quotient. -/
  rootClass : ((AlgebraicClosure (Completion (qVPlace T b)))ˣ ⧸ muSubgroup)
  rootClass_eq : rootClass =
    QuotientGroup.mk' muSubgroup (hodgeTwoLthRoot T b)
  rootClass_pow_twoL :
    rootClass ^ (2 * l.value) =
      QuotientGroup.mk' muSubgroup (qVAlgClosedUnit T b)

/-- Any two actual 2l-th roots have the same image in the mu_{2l}-quotient: the
root class is well defined (the mu_{2l}-ambiguity is exactly absorbed). -/
theorem rootClass_wellDefined (b : Bad (nativePlaceSelection T))
    (R : NatRootSystem (qVAlgClosedUnit T b)) :
    (QuotientGroup.mk' (muTwoLAlgClosedSubgroup T b) (R.root (2 * l.value)) :
        (AlgebraicClosure (Completion (qVPlace T b)))ˣ ⧸
          muTwoLAlgClosedSubgroup T b) =
      QuotientGroup.mk' (muTwoLAlgClosedSubgroup T b) (hodgeTwoLthRoot T b) := by
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply]
  have hmem := TwoLthRootKummerActual.twoLthRoot_ratio_mem_mu (l := l) T b R (hodgeTwoLRootSystem T b)
  have hrew : (R.root (2 * l.value))⁻¹ * hodgeTwoLthRoot T b =
      (hodgeTwoLRootSystem T b).root (2 * l.value) / R.root (2 * l.value) := by
    rw [div_eq_inv_mul]
    rfl
  rw [hrew]
  exact hmem

/-- The actual candidate X-mu unit-group portion built from the actual unit,
mu_{2l} and 2l-th root data. -/
noncomputable def lgpXMuUnitCandidate (b : Bad (nativePlaceSelection T)) :
    LGPXMuUnitCandidate T b where
  muSubgroup := muTwoLAlgClosedSubgroup T b
  rootClass := QuotientGroup.mk' (muTwoLAlgClosedSubgroup T b) (hodgeTwoLthRoot T b)
  rootClass_eq := rfl
  rootClass_pow_twoL := by
    rw [← map_pow, hodgeTwoLthRoot_pow]

/-- The candidate unit group is the actual algebraic-closure unit group. -/
theorem lgpXMuUnitCandidate_unitGroup (b : Bad (nativePlaceSelection T)) :
    (lgpXMuUnitCandidate T b).muSubgroup = muTwoLAlgClosedSubgroup T b := rfl

/-- The candidate root class is the class of the actual 2l-th root. -/
theorem lgpXMuUnitCandidate_rootClass (b : Bad (nativePlaceSelection T)) :
    (lgpXMuUnitCandidate T b).rootClass =
      QuotientGroup.mk' (muTwoLAlgClosedSubgroup T b) (hodgeTwoLthRoot T b) := rfl

/-- Exact identification data needed to identify the candidate X-mu unit-group
portion with the paper's X-mu unit portion of the F^LGP x mu-prime-strip
(IUT III, Prop. 3.7, (iii), (iv), pp. 109--111; Def. 3.8, (i), (ii), pp. 112--113).
* unitPortionSubquotient: identification of our mu_{2l}-quotient with the
  paper's unit portion Psi_FLGP(HT)_v^x inside the tensor packet.
* xMuAction: the F_l^x x mu-action data on the unit portion, i.e. the x mu
  part of the F^LGP x mu-prime-strip structure.
* labelComponents: the label-j components of the unit portion (j in {1,...,l*}).
* lgpLinkCompatibility: compatibility with the Theta x mu LGP-link of
  Def. 3.8, (ii). -/
structure LGPXMuUnitIdentificationMissing (b : Bad (nativePlaceSelection T)) where
  unitPortionSubquotient : Prop
  xMuAction : Prop
  labelComponents : Prop
  lgpLinkCompatibility : Prop

/-- The exact identification gap for the candidate X-mu unit-group portion. -/
def LGPXMuUnitIdentificationGap (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (LGPXMuUnitIdentificationMissing T b)

#check muTwoLAlgClosedSubgroup
#check rootClass_wellDefined
#check lgpXMuUnitCandidate
#check lgpXMuUnitCandidate_unitGroup
#check lgpXMuUnitCandidate_rootClass
#check LGPXMuUnitIdentificationGap

end LeanFormal.IUT.XiFPaper.S3136LGPXMuUnitActual
end