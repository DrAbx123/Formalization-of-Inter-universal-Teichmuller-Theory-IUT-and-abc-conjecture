import Mathlib
import LeanFormal.IUT.Audit.Status

/-! # S3131 [GenEll] detailed paper-input statement schemas + citations -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3131GenEllInputDetailedActual

universe u

/-- Definition 1.2/1.5 shape: BD-class of height functions (bounded discrepancy). -/
def BDClass {X : Type u} (ht logDiff logCond : X → Real) (eps : Real) : Prop :=
  ∃ C : Real, ∀ x : X, ht x ≤ (1 + eps) * (logDiff x + logCond x) + C

/-- Example 1.3 shape: natural subsets of rational points (compactly bounded etc.). -/
def NaturalPointSubset (inSubset : Prop) : Prop := inSubset

/-- Proposition 1.4/1.7 shape: height/conduct/log-different properties used in the
reduction (basic height properties; conductors and log differents). -/
def HeightConductorLogDiffProperties (heightProps conductorProps : Prop) : Prop :=
  heightProps ∧ conductorProps

/-- Theorem 2.1 shape: (i) effective Mordell/ABC/Vojta for all hyperbolic curves over
number fields  <=>  (ii) ABC for Sigma-supported compactly bounded subsets.
The REDUCTION DIRECTION used is (ii) => (i). -/
def GenEllTheorem21 (generalCase compactlyBoundedCase : Prop) : Prop :=
  generalCase ↔ compactlyBoundedCase

def GenEllReductionDirection (generalCase compactlyBoundedCase : Prop) : Prop :=
  compactlyBoundedCase → generalCase

def S3131GenEllDetailedCitations : List (String × String) :=
  [ ("Definition 1.2", "BD-classes of height functions (corpus ~line 200)"),
    ("Definition 1.5", "compactly bounded away from infinity (corpus ~line 280)"),
    ("Example 1.3", "various natural subsets of the set of points (corpus line 231+)"),
    ("Proposition 1.4", "basic properties of heights (corpus line 294)"),
    ("Proposition 1.7", "conductors and log differents (corpus line 524)"),
    ("Theorem 2.1", "compactly bounded subsets and the ABC conjecture: equivalence (i)<=>(ii) (corpus lines 615-687); proof uses noncritical Belyi maps [Mzk1], Elkies technique, Props 1.4/1.7") ]

theorem S3131GenEllDetailedCitations_length : S3131GenEllDetailedCitations.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.S3131GenEllInputDetailedActual
end