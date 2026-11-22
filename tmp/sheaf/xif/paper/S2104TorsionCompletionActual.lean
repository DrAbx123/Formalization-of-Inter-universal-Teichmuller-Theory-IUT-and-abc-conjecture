/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import tmp.sheaf.xif.paper.S2093ArtinM2aBridge
import tmp.sheaf.xif.paper.S2102TorsionArtinActual

/-!
# S2104: M2a-torsion -- torsion of the profinite completion of L^x is mu(L)

Layer: O (original Theta-link / q-pilot).  Consumers: S2027's
localArtinTorsion / LocalArtinSourceData, and the S2093 report, whose exact
recorded missing object was

  TorsionCompletionIso U : Nonempty
    (CommGroup.torsion (unitProfiniteCompletion p U) ≃* mu p U).

S2093 proves the reciprocity isomorphism

  localReciprocityIsomorphism U :
    unitProfiniteCompletion p U ≃* Gal(L^ab / L),

and S2102 proves the torsion identification on the Galois side

  localArtinTorsionEquiv U :
    mu p U ≃* CommGroup.torsion (Gal(L^ab / L)).

The only structural point left is that Mathlib's profinite completion
ProfiniteCompletion.completion (GrpCat.of (localField p U)^x) has no
CommGroup instance (it is a limit of arbitrary finite quotients), so
CommGroup.torsion (unitProfiniteCompletion p U) does not even elaborate.
Here commutativity is transported back along the injective reciprocity
isomorphism: the target Gal(L^ab / L) is commutative (S2027), hence so is
the completion.  This is not an extra axiom and not a change of target: the
underlying group structure is the existing one, only mul_comm is added.

Composing the induced torsion equivalence with the inverse of S2102's torsion
identification gives the requested

  torsionCompletionEquivMu U :
    CommGroup.torsion (unitProfiniteCompletion p U) ≃* mu p U.

No sorry, admit or new axiom is introduced.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S2104TorsionCompletionActual

open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual

variable {p : Nat} [Fact (Nat.Prime p)]
variable (U : Index p)

/-- The profinite completion of L^x is commutative.

Mathlib's profinite completion of a group has no CommGroup instance in
general.  For L^x, the reciprocity isomorphism localReciprocityIsomorphism U
is injective into the commutative group Gal(L^ab / L);
MonoidHom.commGroupOfInjective transports commutativity back to the
completion.  The underlying Group structure is the existing one, so this
only supplies mul_comm. -/
noncomputable instance unitProfiniteCompletionCommGroup :
    CommGroup (unitProfiniteCompletion p U) :=
  MonoidHom.commGroupOfInjective
    (f := (LeanFormal.IUT.XiFPaper.S2093ArtinM2aBridge.localReciprocityIsomorphism (p := p) U).toMonoidHom)
    (LeanFormal.IUT.XiFPaper.S2093ArtinM2aBridge.localReciprocityIsomorphism (p := p) U).injective

/-- M2a-torsion.  The torsion of the profinite completion of L^x is the group
of roots of unity of L.  This is the composite of the torsion equivalence
induced by localReciprocityIsomorphism U and the inverse of S2102's
localArtinTorsionEquiv U, which computes the torsion of Gal(L^ab / L) as
mu(L). -/
noncomputable def torsionCompletionEquivMu :
    CommGroup.torsion (unitProfiniteCompletion p U) ≃* mu p U :=
  (LeanFormal.IUT.XiFPaper.S2027LocalArtinActual.torsionMulEquiv
      (LeanFormal.IUT.XiFPaper.S2093ArtinM2aBridge.localReciprocityIsomorphism (p := p) U)).trans
    (LeanFormal.IUT.XiFPaper.S2102TorsionArtinActual.localArtinTorsionEquiv (p := p) U).symm

/-- The same equivalence in the direction mu(L) -> torsion(L^x-hat). -/
noncomputable def muEquivTorsionCompletion :
    mu p U ≃* CommGroup.torsion (unitProfiniteCompletion p U) :=
  (torsionCompletionEquivMu (p := p) U).symm

/-- The exact type recorded as missing in the S2093 report. -/
def TorsionCompletionIso : Prop :=
  Nonempty (CommGroup.torsion (unitProfiniteCompletion p U) ≃* mu p U)

/-- M2a-torsion holds: the exact recorded missing type is inhabited. -/
theorem torsionCompletionIso_holds : TorsionCompletionIso (p := p) U :=
  ⟨torsionCompletionEquivMu (p := p) U⟩

/-- The equivalent topological-abelianization form, already supplied by S2102:
mu(L) ≃* torsion(TopologicalAbelianization(Gal(Qbar_p/L))). -/
theorem torsionTopologicalEquivMu_holds :
    Nonempty (mu p U ≃*
      CommGroup.torsion
        (TopologicalAbelianization (localGaloisGroup p U))) :=
  LeanFormal.IUT.XiFPaper.S2102TorsionArtinActual.localArtinTorsionTopological_holds (p := p) U

/-! ## Axiom probes -/

#check unitProfiniteCompletionCommGroup
#check torsionCompletionEquivMu
#check muEquivTorsionCompletion
#check TorsionCompletionIso
#check torsionCompletionIso_holds
#check torsionTopologicalEquivMu_holds

#print axioms unitProfiniteCompletionCommGroup
#print axioms torsionCompletionEquivMu
#print axioms muEquivTorsionCompletion
#print axioms torsionCompletionIso_holds
#print axioms torsionTopologicalEquivMu_holds

end LeanFormal.IUT.XiFPaper.S2104TorsionCompletionActual

end