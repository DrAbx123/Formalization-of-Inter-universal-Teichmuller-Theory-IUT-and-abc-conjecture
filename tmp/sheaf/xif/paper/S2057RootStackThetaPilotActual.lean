import tmp.sheaf.xif.paper.S798OtRootStackSectionActual
import tmp.sheaf.xif.paper.TwoLthRootKummerActual
import tmp.sheaf.xif.paper.S201RootThetaNormLActual
import tmp.sheaf.xif.paper.S2040ActualThetaLink312
import tmp.sheaf.xif.paper.S346OrbifoldStructuralSheafActual
import tmp.sheaf.xif.paper.S342QVFamilyRootImpossibleActual
import Mathlib.CategoryTheory.Action
import Mathlib.Algebra.Group.TypeTags.Basic

/-! # S2057: the actual root-stack Theta-pilot object on q[2u]

Layer: O (S2040 actual Theta-link, first missing).

This file attacks the first missing component of S2040:
the actual root-stack Theta-pilot object on the double-underlined q-parameter
q[2u], together with its connection to
S2040ActualThetaLink312.S2040ThetaLinkDisplacement and its thetaLink.

## What is constructed unconditionally

* KummerRootStack: the genuine action groupoid of 2l-th roots of the actual
  q-section in the finite root-stack extension L(mu_{2l}) (S782/S798).  Its
  objects are roots r with r ^ (2l) = qSection; its morphisms are the
  mu_{2l}-multiples, so the groupoid has mu_{2l}-many morphisms between
  distinct roots (it is not a discrete set quotient).  It is a Groupoid
  (Mathlib ActionCategory).  This is the root stack around
  hodgeTwoLthRoot / q[2u], not a completion object.
* S2057RootStackThetaPilotObject: the actual finite root-stack Theta-pilot
  data: the distinguished q[2u] object, its 2l-th power q[1u], the
  Theta values q[2u]^(j^2), the mu_{2l} unit, and the real root scalar.
* s2057RootStackThetaPilotObject: an inhabitant of that object, built from
  the actual finite root-stack extension.  Its scalar is the actual L-norm
  rootNormedElementNorm; rootStackTheta_pow proves
  rootStackTheta^(2l) = ||q[1u]||.
* S2057PaperUnitsAmbientData + s2057Displacement: the exact paper
  O^×/O^×mu/ambient-value data needed by the S2040 displacement.  Given that
  data and the paper q identification Opaper.q = ||q[1u]||, the S2040
  S2040ThetaLinkDisplacement is *constructed* with root stack scalar equal to
  the actual root norm, and the S2040 thetaLink generator law is derived.

## What is NOT constructed (exact first missing)

The paper's O^tri(T_X) root-stack carrier of IUT I Example 3.2(iv) and its
identification with the finite extension are not in the tree.  The closest
recorded object is
S346OrbifoldStructuralSheafActual.OrbifoldStructuralSheafCarrierSpec;
it has no inhabitant and is only a spec.  The paper q parameter is not the repo
qVFamily (S342: the repo q has order coprime to l, so no completion 2l-th
root; the paper q must admit a 2l-th root in its O^tri carrier).  These are
recorded as fields of S2057FirstMissing; no inhabitant is asserted.

No completion root, no fake stack, no free conclusion field, no sorry/axiom.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2057RootStackThetaPilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S798OtRootStackSectionActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.S2040ActualThetaLink312
open LeanFormal.IUT.XiFPaper.S346OrbifoldStructuralSheafActual
open LeanFormal.IUT.XiFPaper.S342QVFamilyRootImpossibleActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTII.Theta.UnitGeneratedMonoidComparison
open CategoryTheory

universe u ua uv upi umon uL uC uG uX ulab

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. The actual root scalar of q[2u] -/

/-- The normalized norm of the actual q[1u] section.  This is the real number
whose 2l-th root is the root-stack scalar. -/
abbrev paperQNorm : Real := ‖(sourceRootQUnit T b : rootBase T b)‖

/-- The actual finite root-stack scalar q[2u] is the L-norm of the root.
It is not a completion root: it lives in the finite root-stack extension
L(mu_{2l}). -/
noncomputable def rootStackTheta : Real := rootNormedElementNorm T b

theorem rootStackTheta_pos : 0 < rootStackTheta (l := l) T b :=
  norm_pos_iff.mpr (by
    simpa [rootNormedElement] using Units.ne_zero (sourceRoot T b))

theorem rootStackTheta_pow :
    rootStackTheta (l := l) T b ^ (2 * l.value) = paperQNorm (l := l) T b :=
  rootNormedElementNorm_pow_twoL T b

/-- The actual root-stack scalar is the real 2l-th root of the paper q. -/
theorem rootStackTheta_eq_s2040Theta
    {q : Real} (hq : q = paperQNorm (l := l) T b) (hqpos : 0 < q) :
    rootStackTheta (l := l) T b = s2040Theta l q := by
  have hpow : rootStackTheta (l := l) T b ^ (2 * l.value) = q := by
    rw [rootStackTheta_pow, ← hq]
  have hpos : 0 < rootStackTheta (l := l) T b := rootStackTheta_pos T b
  have hs : 0 < s2040Theta l q := s2040Theta_pos hqpos
  have hn : 2 * l.value ≠ 0 := Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  refine (pow_left_inj₀ hpos.le hs.le hn).mp ?_
  exact hpow.trans (s2040Theta_pow (l := l) hqpos.le).symm

/-! ## 2. The mu_{2l}-root-stack groupoid -/

/-- The mu_{2l} group of the finite root-stack extension. -/
abbrev RootStackMu : Type := rootsOfUnity (2 * l.value) (rootStackExtension T b)

/-- The objects of the root stack: 2l-th roots of the actual q-section in
L(mu_{2l}). -/
abbrev RootSet : Type :=
  {r : (rootStackExtension T b)ˣ // r ^ (2 * l.value) = (stackQSection T b).1}

instance : MulAction (RootStackMu (l := l) T b) (RootSet (l := l) T b) where
  smul ζ r := ⟨(ζ : (rootStackExtension T b)ˣ) * r.1, by
    rw [mul_pow, ζ.2, r.2, one_mul]⟩
  one_smul r := Subtype.ext (by
    change (1 : (rootStackExtension T b)ˣ) * r.1 = r.1
    rw [one_mul])
  mul_smul a c r := Subtype.ext (by
    change ((a : (rootStackExtension T b)ˣ) * (c : (rootStackExtension T b)ˣ)) * r.1 =
      (a : (rootStackExtension T b)ˣ) * ((c : (rootStackExtension T b)ˣ) * r.1)
    rw [mul_assoc])

/-- The actual root-stack groupoid [roots / mu_{2l}], realized as the action
groupoid of mu_{2l} on the actual roots.  It is a groupoid by
ActionCategory.instGroupoid, not a set quotient (S355's degenerate quotient is
not used). -/
abbrev KummerRootStack : Type := ActionCategory (RootStackMu (l := l) T b) (RootSet (l := l) T b)

instance kummerRootStackGroupoid : Groupoid (KummerRootStack (l := l) T b) :=
  inferInstance

/-- The distinguished q[2u] object: the actual root section. -/
noncomputable def rootStackPointSet : RootSet (l := l) T b :=
  ⟨(stackRootSection T b).1, congrArg Prod.fst (stackRootSection_pow T b)⟩

noncomputable def rootStackPoint : KummerRootStack (l := l) T b :=
  (rootStackPointSet (l := l) T b : KummerRootStack (l := l) T b)

/-! ## 3. The actual root-stack Theta-pilot object -/

/-- The actual root-stack Theta-pilot object on q[2u].

The object is built on the finite root-stack extension: root is the actual
2l-th root, qSection its 2l-th power, thetaValue j is q[2u]^(j^2), and mu is
the primitive 2l-th root of unity.  All fields are tied to the concrete
S782/S798 data, not left arbitrary. -/
structure S2057RootStackThetaPilotObject where
  /-- The distinguished q[2u] object of the root-stack groupoid. -/
  q2u : KummerRootStack (l := l) T b
  q2u_eq : q2u = rootStackPoint (l := l) T b
  /-- The actual root in the finite root-stack extension. -/
  root : (rootStackExtension T b)ˣ
  root_eq : root = (stackRootSection T b).1
  root_pow : root ^ (2 * l.value) = (stackQSection T b).1
  /-- The actual q[1u] section. -/
  qSection : (rootStackExtension T b)ˣ
  qSection_eq : qSection = (stackQSection T b).1
  /-- The real scalar of q[2u]. -/
  rootStackTheta : Real
  rootStackTheta_eq : rootStackTheta = rootNormedElementNorm T b
  rootStackTheta_pow : rootStackTheta ^ (2 * l.value) = paperQNorm (l := l) T b
  /-- The Theta values q[2u]^(j^2) in the root-stack carrier. -/
  thetaValue : SignedLabel l.value → StackSectionCarrier T b
  thetaValue_eq : ∀ j, thetaValue j = stackRootSection T b ^ (gaussExponent j.1).toNat
  /-- The primitive mu_{2l} unit. -/
  mu : (rootStackExtension T b)ˣ
  mu_eq : mu = stackMuUnit T b
  mu_pow : mu ^ (2 * l.value) = 1
  /-- The norm of the Theta value is the j^2-power of the root scalar. -/
  thetaValue_norm : ∀ j, ‖((thetaValue j).1 : rootStackExtension T b)‖ =
    rootStackTheta ^ (gaussExponent j.1).toNat
  /-- The divisor coordinate of the Theta value is order/(2l) * j^2. -/
  thetaValue_divisor : ∀ j, (thetaValue j).2 =
    Multiplicative.ofAdd ((((qVFamily T b).order : Real) / (2 * l.value)) *
      (gaussExponent j.1).toNat)

theorem stackMuUnit_pow :
    (stackMuUnit (l := l) T b) ^ (2 * l.value) = 1 := by
  ext
  simp [stackMuUnit, stackMuRoot_pow]

/-- The actual root-stack Theta-pilot object exists unconditionally on the
finite root-stack extension. -/
noncomputable def s2057RootStackThetaPilotObject :
    S2057RootStackThetaPilotObject (l := l) T b where
  q2u := rootStackPoint (l := l) T b
  q2u_eq := rfl
  root := (stackRootSection T b).1
  root_eq := rfl
  root_pow := congrArg Prod.fst (stackRootSection_pow T b)
  qSection := (stackQSection T b).1
  qSection_eq := rfl
  rootStackTheta := rootNormedElementNorm T b
  rootStackTheta_eq := rfl
  rootStackTheta_pow := rootStackTheta_pow (l := l) T b
  thetaValue := fun j => stackRootSection T b ^ (gaussExponent j.1).toNat
  thetaValue_eq := fun j => rfl
  mu := stackMuUnit T b
  mu_eq := rfl
  mu_pow := stackMuUnit_pow (l := l) T b
  thetaValue_norm := by
    intro j
    change ‖(((stackRootSection T b).1 : (rootStackExtension T b)ˣ) :
        rootStackExtension T b) ^ (gaussExponent j.1).toNat‖ = _
    rw [norm_pow]
    rw [show ‖((stackRootSection T b).1 : rootStackExtension T b)‖ =
        rootNormedElementNorm T b from by
      unfold stackRootSection stackLUnitMap rootNormedUnit rootNormedElementNorm
        rootNormedElement
      rfl]
  thetaValue_divisor := by
    intro j
    change (stackRootSection T b).2 ^ (gaussExponent j.1).toNat = _
    change Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value)) ^
        (gaussExponent j.1).toNat = _
    rw [← ofAdd_nsmul]
    congr 1
    rw [nsmul_eq_mul]
    ring

theorem s2057RootStackThetaPilotObject_available :
    Nonempty (S2057RootStackThetaPilotObject (l := l) T b) :=
  ⟨s2057RootStackThetaPilotObject (l := l) T b⟩

theorem s2057_rootStackTheta_actual :
    (s2057RootStackThetaPilotObject (l := l) T b).rootStackTheta =
      rootStackTheta (l := l) T b := rfl

theorem s2057_root_pow :
    (s2057RootStackThetaPilotObject (l := l) T b).root ^ (2 * l.value) =
      (s2057RootStackThetaPilotObject (l := l) T b).qSection := by
  show (stackRootSection T b).1 ^ (2 * l.value) = (stackQSection T b).1
  exact congrArg Prod.fst (stackRootSection_pow T b)

theorem s2057_thetaValue_eq (j : SignedLabel l.value) :
    (s2057RootStackThetaPilotObject (l := l) T b).thetaValue j =
      stackRootSection T b ^ (gaussExponent j.1).toNat := rfl

/-- The actual finite root is the same algebraic-closure root as
hodgeTwoLthRoot: both are the root of the same qVFamily q in the algebraic
closure.  This is a definitional equality, not a comparison of two choices. -/
theorem sourceRoot_eq_hodgeTwoLthRoot :
    sourceRoot T b =
      (hodgeTwoLthRoot T b :
        (AlgebraicClosure (Completion (qVPlace (l := l) T b)))ˣ) := rfl

/-- The root element used by the finite root-stack carrier is hodgeTwoLthRoot. -/
theorem rootNormedElement_eq_hodgeTwoLthRoot :
    (rootNormedElement T b : rootNormedAmbient T b) =
      (hodgeTwoLthRoot T b :
        AlgebraicClosure (Completion (qVPlace (l := l) T b))) := by
  simpa [rootNormedElement] using
    congrArg Units.val (sourceRoot_eq_hodgeTwoLthRoot (l := l) T b)

/-- The distinguished root-stack object is the image of the actual root unit
(which is hodgeTwoLthRoot by rootNormedElement_eq_hodgeTwoLthRoot) in the
finite root-stack extension. -/
theorem s2057_rootStackPoint_eq_rootNormedUnit :
    ((rootStackPointSet T b).1 : rootStackExtension T b) =
      algebraMap (rootNormedExtension T b) (rootStackExtension T b)
        ((rootNormedUnit T b : (rootNormedExtension T b)ˣ) :
          rootNormedExtension T b) := rfl

/-! ## 4. The paper O^×/O^×mu/ambient data and the S2040 displacement -/

variable {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, 0} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip.{umon, uv, upi} V}
variable {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
variable (Opaper : S2038PaperOActual (I := I) (G := G) (envStrip := envStrip)
  (Label := Label) (Choice := Choice) (l := l) (V := V) O)

/-- The paper O^×/O^×mu/ambient-value data of the S2040 displacement.  This is
exactly the part of S2040ThetaLinkDisplacement other than the two strips and
the root-stack scalar; it is the actual O^×/O^×mu unit link and the ambient
value groups/degrees/generators.  No inhabitant is asserted. -/
structure S2057PaperUnitsAmbientData where
  unitsMu : S2040UnitsMuLink
  ambientQ : Type
  [commGroupQ : CommGroup ambientQ]
  ambientTheta : Type
  [commGroupTheta : CommGroup ambientTheta]
  embedQ : unitsMu.U →* ambientQ
  embedTheta : unitsMu.V →* ambientTheta
  intDegreeQ : ambientQ →* Multiplicative Int
  intDegreeTheta : ambientTheta →* Multiplicative Int
  logDegreeQ : ambientQ →* Multiplicative Real
  logDegreeTheta : ambientTheta →* Multiplicative Real
  injQ : Function.Injective embedQ
  injTheta : Function.Injective embedTheta
  unitDegreeQ : ∀ a : unitsMu.U, intDegreeQ (embedQ a) = 1
  unitDegreeTheta : ∀ b : unitsMu.V, intDegreeTheta (embedTheta b) = 1
  generatorQ : ambientQ
  generatorTheta : ambientTheta
  generatorQ_logDegree : (logDegreeQ generatorQ).toAdd = Real.log Opaper.q
  generatorTheta_logDegree :
    (logDegreeTheta generatorTheta).toAdd = Real.log (rootNormedElementNorm T b)
  generatorQ_degree_ne_zero : (intDegreeQ generatorQ).toAdd ≠ 0
  generatorTheta_degree_ne_zero : (intDegreeTheta generatorTheta).toAdd ≠ 0

attribute [instance] S2057PaperUnitsAmbientData.commGroupQ
  S2057PaperUnitsAmbientData.commGroupTheta

/-- The paper q identification: the S2038 q is the actual normalized q[1u]
norm.  This is an exact source identification, not a definition. -/
def S2057PaperQIdentification : Prop := Opaper.q = paperQNorm (l := l) T b

/-- The S2040 Theta-link displacement built from the actual root-stack
object.  The root-stack scalar is the actual root norm; the power relation is
proved from the root-stack object and the paper q identification.  The paper
unit/ambient data are supplied by D. -/
noncomputable def s2057Displacement
    (D : S2057PaperUnitsAmbientData (l := l) T b Opaper)
    (hq : S2057PaperQIdentification (l := l) T b Opaper) :
    S2040ThetaLinkDisplacement Opaper where
  unitsMu := D.unitsMu
  thetaPilotStrip := Opaper.thetaPilotStrip
  thetaPilotStrip_eq := Opaper.thetaPilotStrip_eq
  qPilotStrip := Opaper.qPilotStrip
  qPilotStrip_eq := Opaper.qPilotStrip_eq
  rootStackTheta := rootNormedElementNorm T b
  rootStackTheta_eq := rootStackTheta_eq_s2040Theta T b hq Opaper.q_pos
  rootStack_pow := by
    rw [rootNormedElementNorm_pow_twoL]
    exact hq.symm
  ambientQ := D.ambientQ
  commGroupQ := D.commGroupQ
  ambientTheta := D.ambientTheta
  commGroupTheta := D.commGroupTheta
  embedQ := D.embedQ
  embedTheta := D.embedTheta
  intDegreeQ := D.intDegreeQ
  intDegreeTheta := D.intDegreeTheta
  logDegreeQ := D.logDegreeQ
  logDegreeTheta := D.logDegreeTheta
  injQ := D.injQ
  injTheta := D.injTheta
  unitDegreeQ := D.unitDegreeQ
  unitDegreeTheta := D.unitDegreeTheta
  generatorQ := D.generatorQ
  generatorTheta := D.generatorTheta
  generatorQ_logDegree := D.generatorQ_logDegree
  generatorTheta_logDegree := D.generatorTheta_logDegree
  generatorQ_degree_ne_zero := D.generatorQ_degree_ne_zero
  generatorTheta_degree_ne_zero := D.generatorTheta_degree_ne_zero

/-- The S2040 thetaLink attached to the constructed displacement sends the
q-pilot generator to the Theta-pilot generator. -/
theorem s2057ThetaLink_generator
    (D : S2057PaperUnitsAmbientData (l := l) T b Opaper)
    (hq : S2057PaperQIdentification (l := l) T b Opaper) :
    (s2057Displacement (l := l) T b Opaper D hq).thetaLink
        (distinguishedGenerator (s2057Displacement (l := l) T b Opaper D hq).embedQ
          (s2057Displacement (l := l) T b Opaper D hq).generatorQ) =
      distinguishedGenerator (s2057Displacement (l := l) T b Opaper D hq).embedTheta
        (s2057Displacement (l := l) T b Opaper D hq).generatorTheta :=
  S2040ThetaLinkDisplacement.thetaLink_generator
    (s2057Displacement (l := l) T b Opaper D hq)

/-! ## 5. The exact first missing chain -/

variable {X : Type uX} {label : Type ulab} [Fintype label]
variable (P : PaperSignedHull X label)

/- The paper q-pilot log identification used by S2040ThetaLink312 is
reused from S2040. -/

/-- Exact first missing chain of the root-stack Theta-pilot object:

1. the actual paper O^tri(T_X) root-stack carrier (S346 spec); it is not the
   completion root (S342) and has no inhabitant in the tree;
2. the paper q identification Opaper.q = ||q[1u]||;
3. the paper O^×/O^×mu/ambient-value data of the S2040 displacement;
4. the q-pilot log identification and the paper hull normalization.

No inhabitant is asserted.  The finite root-stack object of section 3 is
constructed; what remains here is its paper identification and the paper
O/ambient data, not a root in the completion. -/
structure S2057FirstMissing where
  paperCarrier : OrbifoldStructuralSheafCarrierSpec.{0} T b
  paperQ_eq : S2057PaperQIdentification (l := l) (T := T) (b := b) (Opaper := Opaper)
  unitsAmbient : S2057PaperUnitsAmbientData (l := l) (T := T) (b := b) (Opaper := Opaper)
  qPilotLogIdentification : S2040QPilotLogIdentification O Opaper
  hull_normalization : P.signedHullLogVolume = Real.log (rootNormedElementNorm T b)

/-- From the exact first-missing chain one obtains the actual S2040ThetaLink312
with the root-stack scalar supplied by the actual finite root-stack object. -/
theorem s2057ThetaLink312_of_firstMissing
    (M : S2057FirstMissing (l := l) T b Opaper P) :
    Nonempty (S2040ThetaLink312 O Opaper P) :=
  ⟨{ theaterLink := I.linkAt 0 0 1 0
     theaterLink_eq := rfl
     displacement := s2057Displacement (l := l) T b Opaper M.unitsAmbient M.paperQ_eq
     qPilotLogIdentification := M.qPilotLogIdentification
     hull_normalization := M.hull_normalization }⟩

/-- The first-missing chain implies the paper inclusion. -/
theorem s2057_inclusion_of_firstMissing
    (M : S2057FirstMissing (l := l) T b Opaper P) :
    O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume := by
  obtain ⟨L⟩ := s2057ThetaLink312_of_firstMissing (l := l) T b Opaper P M
  exact L.link_implies_inclusion

/-- The first-missing chain implies the paper 3.12 inequality. -/
theorem s2057_paper312_of_firstMissing
    (M : S2057FirstMissing (l := l) T b Opaper P) :
    -|Real.log Opaper.q| ≤ P.signedHullLogVolume := by
  obtain ⟨L⟩ := s2057ThetaLink312_of_firstMissing (l := l) T b Opaper P M
  exact L.paper312_inequality

/-- S342: the completion has no 2l-th root of the actual q.  This is why the
root-stack object above is built in the finite extension, not in the
completion. -/
theorem s2057_completion_root_impossible :
    ¬ Nonempty (TwoLthRootData T b) :=
  twoLthRootData_impossible T b

/-- The exact paper carrier shape over the repo q: a monoid carrier with a
q[1u] section, a q[2u] root section, and a monoid hom to the completion which
sends the q-section to the actual qVFamily q.  This is the shape in which the
paper q would be the repo q. -/
structure S2057PaperRootStackCarrierSpec where
  carrier : Type
  [monoid : Monoid carrier]
  qSection : carrier
  rootSection : carrier
  root_pow : rootSection ^ (2 * l.value) = qSection
  eval : carrier →* Completion ((nativeBadLift T).lift b)
  eval_qSection : eval qSection = (qVFamily T b).q

attribute [instance] S2057PaperRootStackCarrierSpec.monoid

/-- **No-go**: no paper O^tri carrier with a monoid-hom evaluation to the
completion can have the repo qVFamily q as its q[1u] section.  Its root section
would give a completion 2l-th root of qVFamily, contradicting S342.  Hence the
actual paper root-stack object requires the paper q_v (with 2l | order), not
the repo qVFamily; this is the precise first missing in the source, not a
missing proof about the finite root stack. -/
theorem s2057_paperRootStackCarrier_impossible :
    ¬ Nonempty (S2057PaperRootStackCarrierSpec (l := l) T b) := by
  rintro ⟨C⟩
  let root : (Completion ((nativeBadLift T).lift b))ˣ :=
    Units.mk0 (C.eval C.rootSection) (by
      intro h0
      have hpow : (C.eval C.rootSection) ^ (2 * l.value) = (qVFamily T b).q := by
        rw [← map_pow, C.root_pow, C.eval_qSection]
      rw [h0, zero_pow (Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)] at hpow
      exact (qVFamily T b).q_ne_zero hpow.symm)
  have hpow : root ^ twoLExponent l = qVUnit T b := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    show (C.eval C.rootSection) ^ (2 * l.value) = (qVFamily T b).q
    rw [← map_pow, C.root_pow, C.eval_qSection]
  exact twoLthRootData_impossible T b ⟨{ root := root, root_pow := hpow }⟩

/-! ## 6. Axiom probes -/

#print axioms s2057RootStackThetaPilotObject_available
#print axioms s2057_root_pow
#print axioms s2057_thetaValue_eq
#print axioms s2057Displacement
#print axioms s2057ThetaLink_generator
#print axioms s2057ThetaLink312_of_firstMissing
#print axioms s2057_paperRootStackCarrier_impossible
#print axioms sourceRoot_eq_hodgeTwoLthRoot
#print axioms rootNormedElement_eq_hodgeTwoLthRoot
#print axioms s2057_rootStackPoint_eq_rootNormedUnit

end LeanFormal.IUT.XiFPaper.S2057RootStackThetaPilotActual
end
