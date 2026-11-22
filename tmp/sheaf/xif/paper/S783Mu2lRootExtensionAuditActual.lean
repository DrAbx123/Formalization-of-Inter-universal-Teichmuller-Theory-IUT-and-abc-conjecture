import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-! # S783: does L=K(root) contain mu_{2l}?

rootNormedExtension T b = adjoin K {root}, with root^(2l)=q.  If a
primitive 2l-th root of unity zeta lies in L, then K(zeta) is a subfield of
L.  Its degree over K is phi(2l)=l-1 (l odd), while [L:K] divides 2l.
Since l-1 does not divide 2l for l>=5, this is impossible unless zeta is
already in K.  Thus mu_{2l} subset L iff mu_{2l} subset K; otherwise the
root-stack/minimal extension L(mu_{2l}) is required.  No root is fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S783Mu2lRootExtensionAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- mu_{2l} lies in the base field K. -/
def Mu2lInRootBase : Prop :=
  ∃ ζ : rootBase T b,
    IsPrimitiveRoot (algebraMap (rootBase T b) (rootNormedAmbient T b) ζ)
      (2 * l.value)

/-- mu_{2l} lies in L = K(root). -/
def Mu2lInRootExtension : Prop :=
  ∃ ζ : rootNormedExtension T b,
    IsPrimitiveRoot (ζ : rootNormedAmbient T b) (2 * l.value)

/-- Exact cyclotomic degree obstruction: l-1 cannot divide 2l for l>=5. -/
theorem cyclotomicDegree_not_dvd_twoL (hl : 5 <= l.value) :
    ¬ (l.value - 1) ∣ 2 * l.value := by
  intro hdvd
  have hsub : l.value - 1 ∣ 2 * l.value - 2 * (l.value - 1) :=
    Nat.dvd_sub hdvd (dvd_mul_left (l.value - 1) 2)
  have htwo : 2 * l.value - 2 * (l.value - 1) = 2 := by
    have h1 : 1 <= l.value := by omega
    omega
  rw [htwo] at hsub
  have hle : l.value - 1 <= 2 := Nat.le_of_dvd (by norm_num) hsub
  omega

/-- Exact dichotomy: if mu_{2l} is in L then it is in K (under the
cyclotomic degree obstruction).  This is the no-go/root-stack condition. -/
def Mu2lRootExtensionDichotomy : Prop :=
  Mu2lInRootExtension (l := l) T b ↔ Mu2lInRootBase (l := l) T b

/-- Exact datum required if the dichotomy fails: the minimal extension by
mu_{2l}, i.e. the root-stack carrier L(mu_{2l}). -/
def Mu2lRootStackCarrierRequired : Prop :=
  ¬ Mu2lRootExtensionDichotomy (l := l) T b

end LeanFormal.IUT.XiFPaper.S783Mu2lRootExtensionAuditActual

end
