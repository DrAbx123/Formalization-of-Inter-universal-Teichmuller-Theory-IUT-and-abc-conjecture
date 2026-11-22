import tmp.sheaf.xif.paper.PaperC3TensorBlockActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # mu_{2l} diagonal tensor action on the paper C3 tensor block

The carrier below is definitionally the PaperC3TensorBlockActual.Block carrier,

  MuBlock = ArithmeticTensorTupleBlock (fun v _ => G.place v) (fun _ => ()).

For actual per-completion roots muUnity : forall v, rootsOfUnity (2l) K_v, form
diag(mu) = tensor_v mu_v.  The diagonal action is multiplication by diag(mu).
On the actual q-parameter image point qUnit^(j^2), the action is the pure tensor
of mu_v * qUnit_v^(j^2), and equals diag(mu) * image point.  No root of q is used
as paper theta.

The mu_{2l} orbit is constructed; hull containment is recorded as an exact gap.

No sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperMuTwoLTensorActionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual

universe u

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type} [Fintype V]
variable {l : PrimeGeFive}
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- The actual tensor block carrier (definitionally Block). -/
abbrev MuBlock (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V) : Type :=
  ArithmeticTensorTupleBlock (fun v (_ : Unit) => G.place v) (fun _ => ())

/-- The carrier is definitionally the PaperC3TensorBlockActual Block. -/
theorem MuBlock_eq_Block : MuBlock (G := G) = Block (G := G) := rfl

/-- The actual q-parameter image point qUnit^(j^2) in the block. -/
noncomputable def muQParameterImagePoint (j : SignedLabel l.value) : MuBlock (G := G) :=
  finitePadicTensorTprod (p := p)
    (fun v => CommonPrimeCompletion (G.place v))
    (fun v => (((G.qUnit v : G.valueCarrier v) ^
      (gaussExponent j.1).toNat) : CommonPrimeCompletion (G.place v)))

variable (muUnity : ∀ v : V,
  rootsOfUnity (2 * l.value) (CommonPrimeCompletion (G.place v)))

/-- The actual local mu_{2l} factor at v. -/
noncomputable def muTwoLFactor (v : V) :
    CommonPrimeCompletion (G.place v) :=
  (((muUnity v : rootsOfUnity (2 * l.value)
      (CommonPrimeCompletion (G.place v))) :
    (CommonPrimeCompletion (G.place v))ˣ) :
    CommonPrimeCompletion (G.place v))

/-- The actual diagonal tensor element diag(mu). -/
noncomputable def muTwoLDiagonalTensor : MuBlock (G := G) :=
  finitePadicTensorTprod (p := p)
    (fun v => CommonPrimeCompletion (G.place v))
    (fun v => muTwoLFactor (G := G) (l := l) muUnity v)

/-- The actual diagonal tensor action on the block. -/
noncomputable def muTwoLDiagonalAction (x : MuBlock (G := G)) :
    MuBlock (G := G) :=
  muTwoLDiagonalTensor (G := G) (l := l) muUnity * x

/-- Each local diagonal factor is a (2l)-th root of unity. -/
theorem muTwoLFactor_pow (v : V) :
    (muTwoLFactor (G := G) (l := l) muUnity v) ^ (2 * l.value) = 1 := by
  unfold muTwoLFactor
  change ((((muUnity v : rootsOfUnity (2 * l.value)
    (CommonPrimeCompletion (G.place v))) :
      (CommonPrimeCompletion (G.place v))ˣ) :
        CommonPrimeCompletion (G.place v)) ^ (2 * l.value)) = 1
  rw [← Units.val_pow_eq_pow_val]
  have h := (muUnity v).property
  simpa using congrArg (fun z : (CommonPrimeCompletion (G.place v))ˣ =>
    (z : CommonPrimeCompletion (G.place v))) h

/-- Actual action on the q-parameter image point: multiplication by diag(mu). -/
theorem muTwoLDiagonalAction_muQParameterImagePoint
    (j : SignedLabel l.value) :
    muTwoLDiagonalAction (G := G) (l := l) muUnity
        (muQParameterImagePoint (G := G) (l := l) j) =
      muTwoLDiagonalTensor (G := G) (l := l) muUnity *
        muQParameterImagePoint (G := G) (l := l) j := rfl

/-- Coordinatewise product form of the action on the image point. -/
theorem muTwoLDiagonalAction_muQParameterImagePoint_tprod
    (j : SignedLabel l.value) :
    muTwoLDiagonalAction (G := G) (l := l) muUnity
        (muQParameterImagePoint (G := G) (l := l) j) =
      finitePadicTensorTprod (p := p)
        (fun v => CommonPrimeCompletion (G.place v))
        (fun v =>
          muTwoLFactor (G := G) (l := l) muUnity v *
            (((G.qUnit v : G.valueCarrier v) ^
              (gaussExponent j.1).toNat) :
              CommonPrimeCompletion (G.place v))) := by
  unfold muTwoLDiagonalAction muTwoLDiagonalTensor muQParameterImagePoint
  rw [finitePadicTensorTprod_mul_tprod]

/-- The actual mu_{2l} diagonal orbit of the q-parameter image points. -/
noncomputable def muTwoLQParameterOrbit : Set (MuBlock (G := G)) :=
  {x | ∃ j : SignedLabel l.value, 0 < j.1 ∧
    x = muTwoLDiagonalAction (G := G) (l := l) muUnity
      (muQParameterImagePoint (G := G) (l := l) j)}

/-- Every orbit element is the actual diagonal action on an image point. -/
theorem muTwoLQParameterOrbit_spec
    {x : MuBlock (G := G)} (hx : x ∈ muTwoLQParameterOrbit (G := G) (l := l) muUnity) :
    ∃ j : SignedLabel l.value, 0 < j.1 ∧
      x = muTwoLDiagonalAction (G := G) (l := l) muUnity
        (muQParameterImagePoint (G := G) (l := l) j) := hx

/-- Exact hull indeterminacy gap. -/
structure PaperMuTwoLHullIndeterminacyGap
    (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V) where
  orbit_subset_hull : Prop
  hull_invariant_under_action : Prop
  action_eq_tensor_mul : Prop

/-- Exact missing hull indeterminacy object. -/
def PaperMuTwoLHullIndeterminacyGapRequired : Prop :=
  Nonempty (PaperMuTwoLHullIndeterminacyGap (G := G) (l := l))

end LeanFormal.IUT.XiFPaper.PaperMuTwoLTensorActionActual

end
