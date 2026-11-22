import tmp.sheaf.xif.paper.S3136LGPXMuUnitActual
import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import Brauer.KummerH2

/-! # Stage-4 host: existing-tool reuse — unconditional 2l-th roots in the algebraic closure

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103); IUT II theta values;
IUT III, Prop. 3.7, (iii), (iv) (pp. 109--111).

EXISTING-TOOL REUSE (per Lead directive): instead of the conditional
NatRootSystem hypotheses of the earlier root files, this file uses
* LeanFormal.IUT.AlgebraicClosureRootSystem.rootSystemOfAlgClosed
  (LeanFormal/IUT/IUTII/Kummer/NatRootSystem.lean:75): every unit of an
  algebraically closed field has a compatible NatRootSystem;
* Brauer.exists_root (tmp/local-cft-port Brauer library,
  Brauer/KummerH2.lean:52): every unit has an n-th root in an algebraically
  closed extension.

Consequences (actual, unconditional):
* lgpAlgClosedRootSystem b: the NatRootSystem of the actual q_v unit;
* lgpAlgClosedTwoLthRoot b: an actual 2l-th root of the actual q_v unit;
* lgpAlgClosedTwoLthRoot_pow: its (2l)-th power is the q_v unit;
* lgpAlgClosedTwoLthRoot_brauer: root existence from the Brauer Kummer library;
* lgpAlgClosedTwoLthRoot_ratio_mem_mu: any existing actual root (in particular
  the completion root of the earlier files) differs from this one by an actual
  mu_{2l}-element -- the mu_{2l}-ambiguity is the only ambiguity.

LABEL: prerequisite component only.  Consumer: lattice, stepxi C2, qpilot M2.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPToolReuseRootActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual compatible root system of the q_v unit, from the existing
algebraic-closure root-system tool. -/
noncomputable def lgpAlgClosedRootSystem (b : Bad (nativePlaceSelection T)) :
    NatRootSystem (qVAlgClosedUnit T b) :=
  AlgebraicClosureRootSystem.rootSystemOfAlgClosed (qVAlgClosedUnit T b)

/-- The actual 2l-th root of the q_v unit in the algebraic closure. -/
noncomputable def lgpAlgClosedTwoLthRoot (b : Bad (nativePlaceSelection T)) :
    (AlgebraicClosure (Completion (qVPlace T b)))ˣ :=
  (lgpAlgClosedRootSystem T b).root (2 * l.value)

/-- Its (2l)-th power is the actual q_v unit. -/
theorem lgpAlgClosedTwoLthRoot_pow (b : Bad (nativePlaceSelection T)) :
    lgpAlgClosedTwoLthRoot T b ^ (2 * l.value) = qVAlgClosedUnit T b :=
  (lgpAlgClosedRootSystem T b).pow_self (2 * l.value)
    (Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)

/-- Root existence, from the existing algebraic-closure root-system tool. -/
theorem lgpAlgClosedTwoLthRoot_exists (b : Bad (nativePlaceSelection T)) :
    ∃ c : (AlgebraicClosure (Completion (qVPlace T b)))ˣ,
      c ^ (2 * l.value) = qVAlgClosedUnit T b :=
  ⟨lgpAlgClosedTwoLthRoot T b, lgpAlgClosedTwoLthRoot_pow T b⟩

/-- Any root-system root and this one differ by an actual mu_{2l}-element: the
mu_{2l}-ambiguity is the only ambiguity of the 2l-th root. -/
theorem lgpAlgClosedTwoLthRoot_ratio_mem_mu
    (b : Bad (nativePlaceSelection T))
    (R : NatRootSystem (qVAlgClosedUnit T b)) :
    (R.root (2 * l.value) / lgpAlgClosedTwoLthRoot T b) ∈
      muTwoLAlgClosed (l := l) T b :=
  TwoLthRootKummerActual.twoLthRoot_ratio_mem_mu (l := l) T b
    (lgpAlgClosedRootSystem T b) R

/-- Root existence directly from the existing Brauer Kummer library tool
`Brauer.exists_root` (n-th roots in an algebraically closed field). -/
theorem lgpAlgClosedTwoLthRoot_brauer (b : Bad (nativePlaceSelection T)) :
    ∃ c : (AlgebraicClosure (Completion (qVPlace T b)))ˣ,
      c ^ (2 * l.value) = qVAlgClosedUnit T b :=
  Brauer.exists_root (Ω := AlgebraicClosure (Completion (qVPlace T b)))
    (2 * l.value) (Nat.mul_pos (by norm_num) l.prime.pos)
    (qVAlgClosedUnit T b)

#check lgpAlgClosedRootSystem
#check lgpAlgClosedTwoLthRoot
#check lgpAlgClosedTwoLthRoot_pow
#check lgpAlgClosedTwoLthRoot_exists
#check lgpAlgClosedTwoLthRoot_brauer
#check lgpAlgClosedTwoLthRoot_ratio_mem_mu

end LeanFormal.IUT.XiFPaper.S3136LGPToolReuseRootActual
end