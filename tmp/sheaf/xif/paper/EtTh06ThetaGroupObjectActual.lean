import LeanFormal.IUT.IUTII.Theta.EtaleThetaQuotient
import LeanFormal.IUT.IUTII.Theta.EtaleTateDirection

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: theta group|ThetaQuotient|thetaToElliptic|thetaPowerKernel|EtaleThetaQuotient -> hits IUTII/Theta/EtaleThetaQuotient.lean:29/32/35/40/43/46/50/58/62/65/69/73/77/80/83 -> REUSE (class A algebraic quotient layer; no re-proof).

# [EtTh] 06: theta group object interface (lower-central quotient layer, class A)

Corpus: papers/motizuki_corpus/text/The Etale Theta Function and its Frobenioid-theoretic
Manifestations.txt (theta groups and lower-central quotients).
Tree realization reused: ThetaQuotient = G / [G,[G,G]]-type quotient;
thetaToElliptic : ThetaQuotient -> EllipticAbelianization with its mk formula;
thetaPowerKernel / ellipticPowerKernel normal; mod-l quotients.  HONEST LIMIT:
the geometric fundamental group/profinite topology/etale realization are later
obligations (file header), so this is the algebraic object layer only, NOT a
construction of the paper's theta group.
-/

namespace LeanFormal.IUT.XiFPaper.EtTh06ThetaGroupObjectActual

open LeanFormal.IUT

universe u

variable (G : Type u) [Group G]

/-- The theta commutator kernel is normal (tree instance). -/
theorem etTh_thetaCommutatorKernel_normal : (thetaCommutatorKernel G).Normal :=
  inferInstance

/-- The theta quotient maps to the elliptic abelianization by the identity on
representatives (reused from EtaleThetaQuotient:58). -/
theorem etTh_thetaToElliptic_mk (g : G) :
    thetaToElliptic G (QuotientGroup.mk g) = QuotientGroup.mk g :=
  thetaToElliptic_mk G g

/-- The l-th power kernel of the theta quotient is normal (tree instance). -/
theorem etTh_thetaPowerKernel_normal (l : Nat) : (thetaPowerKernel G l).Normal :=
  inferInstance

/-- The l-th power kernel of the elliptic abelianization is normal (tree instance). -/
theorem etTh_ellipticPowerKernel_normal (l : Nat) :
    (ellipticPowerKernel G l).Normal :=
  inferInstance

/-- Class A object-layer interface for the theta group quotient data. -/
structure EtThThetaGroupObject where
  /-- the theta quotient map compatibility for all representatives -/
  thetaToElliptic_compat : ∀ g : G,
    thetaToElliptic G (QuotientGroup.mk g) = QuotientGroup.mk g

/-- The canonical class A object instance. -/
def etThThetaGroupObject : EtThThetaGroupObject G :=
  { thetaToElliptic_compat := thetaToElliptic_mk G }

/-- The object instance's compatibility lemma. -/
theorem etThThetaGroupObject_apply (g : G) :
    (etThThetaGroupObject G).thetaToElliptic_compat g =
      thetaToElliptic_mk G g :=
  rfl

#check etTh_thetaCommutatorKernel_normal
#check etTh_thetaToElliptic_mk
#check etTh_thetaPowerKernel_normal
#check EtThThetaGroupObject
#check etThThetaGroupObject

end LeanFormal.IUT.XiFPaper.EtTh06ThetaGroupObjectActual