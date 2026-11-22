import tmp.sheaf.xif.paper.OrigXiFPaperLineBundleActual
import tmp.sheaf.xif.paper.ThetaLinkLogKummerActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2148PaperLineBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.OrigXiFPaperLineBundle

universe ua uv upi umon ui uL uC uG

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}

/-! ## 1. S2038 paper O strip/q skeleton (exact interface) -/

/-- The four paper q-pilot identifications at the concrete structure level. -/
abbrev S2148FourQPilotIdentifications
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) : Prop :=
  O.paper_strip_identification ∧
  O.paper_lineBundle_identification ∧
  O.paper_logKummer_identification ∧
  O.paper_qPilot_log_identification

/-- The strip/q skeleton of the S2038 paper O interface: actual one-column q
(with its positivity and contracting inequality), and the actual (1,0)/(0,0)
strips.  It deliberately omits the four paper identifications. -/
structure S2148PaperOStripSkeleton
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) where
  q : Real
  q_eq_source : q = I.oneColumnQAtZero
  q_pos : 0 < q
  q_lt_one : q < 1
  qPilotStrip : FPrimeStrip V
  qPilotStrip_eq : qPilotStrip = I.primeStripAt 1 0
  thetaPilotStrip : FPrimeStrip V
  thetaPilotStrip_eq : thetaPilotStrip = I.primeStripAt 0 0

/-- Actual skeleton, conditional only on q < 1; positivity and the two strip
equalities are theorems. -/
noncomputable def s2148PaperOStripSkeleton
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (hq : I.oneColumnQAtZero < 1) :
    S2148PaperOStripSkeleton (Label := Label) (Choice := Choice) (G := G)
      (envStrip := envStrip) O where
  q := I.oneColumnQAtZero
  q_eq_source := rfl
  q_pos := I.oneColumnQAtZero_pos
  q_lt_one := hq
  qPilotStrip := I.primeStripAt 1 0
  qPilotStrip_eq := rfl
  thetaPilotStrip := I.primeStripAt 0 0
  thetaPilotStrip_eq := rfl

/-- The exact S2038 paper O interface: skeleton plus the four paper
identifications.  This is the type consumed by S2040's S2038PaperOActual. -/
structure S2148PaperOInterface
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip) where
  skeleton : S2148PaperOStripSkeleton (Label := Label) (Choice := Choice)
    (G := G) (envStrip := envStrip) O
  paperO_identifications : S2148FourQPilotIdentifications O

/-- Skeleton plus the four identifications gives the exact paper O interface. -/
noncomputable def s2148PaperOInterfaceOfSkeleton
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    (S : S2148PaperOStripSkeleton (Label := Label) (Choice := Choice)
      (G := G) (envStrip := envStrip) O)
    (h : S2148FourQPilotIdentifications O) :
    S2148PaperOInterface (Label := Label) (Choice := Choice) (G := G)
      (envStrip := envStrip) O where
  skeleton := S
  paperO_identifications := h

/-! ## 2. Native arithmetic-root totalization (OrigXiFPaperLineBundleData) -/

/-- Exact first field of OrigXiFPaperLineBundleData: a native source/lattice
input whose arithmetic root is the paper original input's root. -/
abbrev S2148NativeArithmeticRootData
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) : Type _ :=
  OrigXiFPaperLineBundleData I

/-- Exact missing proposition for the native line-bundle totalization. -/
def S2148NativeArithmeticRootRequired
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (S2148NativeArithmeticRootData (l := l) (V := V) I)

/-- The required proposition is exactly the nonemptiness of
OrigXiFPaperLineBundleData. -/
theorem s2148NativeArithmeticRootRequired_iff
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) :
    S2148NativeArithmeticRootRequired (l := l) (V := V) I ↔
      Nonempty (OrigXiFPaperLineBundleData I) :=
  Iff.rfl

/-- Field-explicit form of the exact first missing: the native totalization and
its arithmetic-root equality. -/
structure S2148NativeArithmeticRootObligation
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) where
  X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l
  arithmetic_root_eq : X.S.arithmetic = I.initial.arithmetic

end LeanFormal.IUT.XiFPaper.S2148PaperLineBundleActual
end
