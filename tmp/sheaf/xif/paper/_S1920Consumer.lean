import tmp.sheaf.xif.paper.S1920PaperFaithfulXiFActual

/-!
# Consumer check for S1920

Imports the produced olean of
`tmp.sheaf.xif.paper.S1920PaperFaithfulXiFActual` and consumes the bundled
paper-level xi-f theorem:

* the xi-f scalar comparison `-|log q| <= OrigXiFSignedThetaHullLogVolume D'`;
* the ray membership via the Theta-link consumer.

No `sorry`, no axiom.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1920Consumer

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkActual
open LeanFormal.IUT.XiFPaper.OrigXiFThetaLinkIdentificationActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1920PaperFaithfulXiFActual

local instance s1920cGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1920cFivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The scalar comparison consumed from the bundled paper-faithful xi-f theorem. -/
theorem s1920c_scalar (D : S1895PaperInput) {X : Type} [TopologicalSpace X]
    (D' : OrigXiFPaperSignedHullData X D.l) :
    -|Real.log ‖S1487Cand.q‖| ≤ OrigXiFSignedThetaHullLogVolume D' := by
  obtain ⟨-, -, -, -, hle⟩ := s1920_paperFaithful_xiF D D'
  exact hle

/-- The object's ray membership consumed from the same bundle. -/
theorem s1920c_ray (D : S1895PaperInput) {X : Type} [TopologicalSpace X]
    (D' : OrigXiFPaperSignedHullData X D.l) :
    (S1895PaperO D).qPilotLogVolume ∈
      hullLogVolumeRay (OrigXiFPaperSignedHull D').signedHullLogVolume := by
  obtain ⟨-, -, hray, -, -⟩ := s1920_paperFaithful_xiF D D'
  exact hray

/-- The link identification consumed from the bundle. -/
theorem s1920c_link (D : S1895PaperInput) {X : Type} [TopologicalSpace X]
    (D' : OrigXiFPaperSignedHullData X D.l) :
    OrigXiFThetaLinkIdentification (S1895PaperO D) D' (S1920PaperC3 D) :=
  (s1920_paperFaithful_xiF D D').2.1

#print axioms s1920c_scalar
#print axioms s1920c_ray
#print axioms s1920c_link

end LeanFormal.IUT.XiFPaper.S1920Consumer

end
