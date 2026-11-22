import tmp.sheaf.n8.closure.PaperToCurrentDonorsConstructed
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData
import Mathlib.Algebra.Group.ULift

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Paper donor construction 2

Attempts the remaining donors from SourceInitialThetaData clauses.

Actual:
- ClauseC torsion/Galois representation fields are actual; the Galois
  representation and SL2 containment are projected directly; the
  l-prime-to-bad-residue condition is actual.

Exact no-go:
- badFinite: ClauseB.bad_is_finite says each bad place is a finite place
  (NumberFieldPlace.IsFinite (finite p)), NOT that VbadMod is finite.  No
  Fintype can be derived from it.
- splitMultiplicativeReduction: ClauseB gives multiplicative reduction, not
  split-multiplicative; no production split card is derivable.

No arbitrary fill.  The torsion clause is assembled conditionally on the
missing label, surjectivity and six-torsion-independence donors.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.PaperDonorsConstructed2

universe u

variable {l : PrimeGeFive} (S : SourceInitialThetaData.{u} l)

/-- Exact target for the bad-place Fintype. -/
abbrev PaperBadFiniteTarget : Prop :=
  Nonempty (Fintype (PaperToCurrentDonorsConstructed.PaperBadPlaces S))

/-- ClauseB's actual finiteness lemma has the wrong type for a Fintype: it
says every bad Fmod-place is finite-kind, not that VbadMod is a finite set. -/
theorem clauseB_bad_is_finite_is_kind_only
    (p : NumberField.FinitePlace S.candidate.arithmetic.Fmod)
    (hp : p ∈ S.candidate.VbadMod) :
    NumberFieldPlace.IsFinite (NumberFieldPlace.finite p) :=
  S.clauseB.bad_is_finite p hp

/-- Exact no-go name for the bad Fintype. -/
def MissingBadFinite : Prop :=
  ¬ PaperBadFiniteTarget S

/-- Exact split-multiplicative target at the chosen bad lifts. -/
def PaperSplitTarget : Prop :=
  ∀ b : PaperToCurrentDonorsConstructed.PaperBadPlaces S,
    S.candidate.arithmetic.curve.HasSplitMultiplicativeReductionAt
      (PaperToCurrentDonorsConstructed.paperBadLift S b)

def MissingSplitMultiplicative : Prop :=
  ¬ PaperSplitTarget S

/-- Actual torsion/Galois fields from ClauseC. -/
abbrev PaperTorsionCarrier : Type u :=
  Multiplicative (S.candidate.arithmetic.curve.LTorsion l)

abbrev PaperGaloisCarrier : Type u :=
  AlgebraicClosure S.candidate.arithmetic.F ≃ₐ[S.candidate.arithmetic.F]
    AlgebraicClosure S.candidate.arithmetic.F

abbrev PaperRepresentationGroup : Type u :=
  ULift.{u} (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))

noncomputable def paperGaloisRepresentation (S : SourceInitialThetaData.{u} l) :
    PaperGaloisCarrier S →* PaperRepresentationGroup.{u} (l := l) :=
  (MulEquiv.ulift.symm.toMonoidHom).comp S.clauseC.galois_representation

def paperImageContainsSL2 (S : SourceInitialThetaData.{u} l) : Prop :=
  S.clauseC.standard_SL2_image ≤ S.clauseC.galois_representation.range

theorem paperImageContainsSL2_proved :
    paperImageContainsSL2 S :=
  S.clauseC.image_contains_SL2

def paperLTorsionCompatible (S : SourceInitialThetaData.{u} l) : Prop :=
  ∀ (p : NumberField.FinitePlace S.candidate.arithmetic.F)
    (hp : NumberFieldFinitePlace.comap p ∈ S.candidate.VbadMod),
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := S.candidate.arithmetic.Fmod) p))

theorem paperLTorsionCompatible_proved :
    paperLTorsionCompatible S :=
  S.clauseC.l_prime_to_bad_residue_characteristics

/-- Exact donors still needed for the torsion shell. -/
structure PaperTorsionDonors (S : SourceInitialThetaData.{u} l) where
  torsionLabel : PaperTorsionCarrier S → Fin 6
  representation_surjective :
    Function.Surjective (paperGaloisRepresentation S)
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent

/-- Conditional SourceTorsionClause: actual torsion carrier/Galois
representation/image/l-compatibility; label, surjectivity and six-torsion
independence are donors. -/
noncomputable def paperTorsionClause
    (D : PaperTorsionDonors S) :
    SourceTorsionClause.{u, u, u} l where
  torsionCarrier := PaperTorsionCarrier S
  torsionLabel := D.torsionLabel
  torsionNonempty := ⟨1⟩
  representationCarrier := PaperGaloisCarrier S
  representationGroup := PaperRepresentationGroup (l := l)
  representation := paperGaloisRepresentation S
  representation_surjective := D.representation_surjective
  imageContainsSL2 := paperImageContainsSL2 S
  imageContainsSL2_proved := paperImageContainsSL2_proved S
  sixTorsionIndependent := D.sixTorsionIndependent
  sixTorsionIndependent_proved := D.sixTorsionIndependent_proved
  lTorsionCompatible := paperLTorsionCompatible S
  lTorsionCompatible_proved := paperLTorsionCompatible_proved S

end LeanFormal.IUT.N8Closure.PaperDonorsConstructed2

end