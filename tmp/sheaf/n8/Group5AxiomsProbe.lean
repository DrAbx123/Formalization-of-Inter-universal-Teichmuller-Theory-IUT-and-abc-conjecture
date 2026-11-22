/-
N8 group5 — stage-2 trial statements: the (IPL) admissible-family relation layer.

Source: tmp/sheaf/n8/group5-STAGE1.md §5.1.  Paper anchor: IUT III,
Remark 3.11.1, (iii) (pagewise:9850--9865, 9869--9878) — the output data is
linked to the input data prime-strip "via full poly-isomorphisms induced by
operations in the algorithm".  The quantifier is over a family P of
poly-isomorphisms (there exists φ ∈ P), not over one selected representative.

Consumer: the (IPL) slot of IUT-III.StepXI through the only grounded (IPL)
implementation linkEvidenceOfQCMPWithIPL
(LeanFormal/IUT/IUTIII/StepXI/FiniteCertificateLinkEvidenceWiring.lean:169-185),
which consumes cardIPLExchangeShape over a CardIPLTransportSupply.  There the
relation polyIsoRel reads the second leg through the single field E.polyIso
(the G1 "full poly-isomorphism proxy"); the present file restores the family
quantifier at the relation layer and records the old relation as the special
case P = {E.polyIso} (only the inclusion polyIsoRel ⊆ familyRel is asserted,
per chapter C's QP ⊆ R and NOT R = QP).

Standalone trial file: imports only the IPL kernel/shell module, no Project
import, independent namespace; no production edit.  All three theorem-level
declarations are proved outright (no placeholder proof body), so the stage-2
placeholder registration does not apply.

Version anchor: LeanFormal/IUT/IUTIII/Theorem311/SourcePolyIsoTransportLaws.lean
SHA256 E064E76534E9542A6F66D0E077D01B0C7ADCB3F2ECFBDA8D1726FC9035EAEE53
(working tree, per group5-STAGE1.md §6).
-/
import LeanFormal.IUT.IUTIII.Theorem311.SourcePolyIsoTransportLaws

namespace LeanFormal.IUT.Tmp.N8Group5

open LeanFormal.IUT
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.Theorem311Source.PolyIsoTransport

universe u v w

/-- (IPL) admissible-family relation at the reduced kernel shell: a (output
side) and b (q-pilot/input side) are connected through some state m of the
link carrier whose second leg is read through *some* member φ of the family
P : Set (L.mid ≃ L.mid) — the reduced shadow of "via full poly-isomorphisms
of F-prime-strips induced by operations in the algorithm"
(Remark 3.11.1, (iii)).

Difference from polyIsoRel: the quantifier.  Here there exists φ ∈ P; in
polyIsoRel the witness is the fixed field E.polyIso. -/
def familyRel {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (P : Set (L.mid ≃ L.mid)) (a b : Choice) : Prop :=
  ∃ m : L.mid, L.left m = a ∧ ∃ φ ∈ P, L.right (φ m) = b

/-- **stage-2 main statement, (Ind1) form.**  The admissible-family relation
exchanges an (Ind1)-step on the output side against the inverse (Ind1)-step
on the q-pilot side.

hP is chapter C's coverage condition at the action layer: every member of the
family commutes with the (Ind1)-action (the reduced form of "induced by
operations in the algorithm").  It is not derivable from polyIsoRel_ind1_iff:
that law is about the single representative E.polyIso, and a family member φ
that does not commute with act1 breaks the exchange.

NL proof: (⇒) with witness (m, φ) read on b, use L.act1 (-g) m as the new
carrier state; the left leg is left_act1 followed by core1.ind1_inverse, the
right leg is hP (move φ past the action), right_act1, and the assumed right
leg.  (⇐) with witness (m, φ) read on core2.ind1 (-g) b, use L.act1 g m; the
right leg closes by ind1_inv_cancel.  Same route as polyIsoRel_ind1_iff, with
one extra hP rewrite. -/
theorem familyRel_ind1_iff {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (P : Set (L.mid ≃ L.mid))
    (hP : ∀ φ ∈ P, ∀ (g : Label) (m : L.mid), φ (L.act1 g m) = L.act1 g (φ m))
    (a b : Choice) (g : Label) :
    familyRel L P (core1.ind1 g a) b ↔ familyRel L P a (core2.ind1 (-g) b) := by
  constructor
  · rintro ⟨m, h1, φ, hφ, h2⟩
    refine ⟨L.act1 (-g) m, ?_, φ, hφ, ?_⟩
    · rw [L.left_act1, h1, core1.ind1_inverse]
    · rw [hP φ hφ (-g) m, L.right_act1, h2]
  · rintro ⟨m, h1, φ, hφ, h2⟩
    refine ⟨L.act1 g m, ?_, φ, hφ, ?_⟩
    · rw [L.left_act1, h1]
    · rw [hP φ hφ g m, L.right_act1, h2, ind1_inv_cancel core2 g b]

/-- **stage-2 main statement, (Ind2) form.**  The (Ind2) version of
familyRel_ind1_iff; hP now only asks commutation with the (Ind2)-action.
Everything is the (Ind2) replica of the (Ind1) route (act2, core1.ind2_inverse,
ind2_inv_cancel). -/
theorem familyRel_ind2_iff {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (P : Set (L.mid ≃ L.mid))
    (hP : ∀ φ ∈ P, ∀ (g : Label) (m : L.mid), φ (L.act2 g m) = L.act2 g (φ m))
    (a b : Choice) (g : Label) :
    familyRel L P (core1.ind2 g a) b ↔ familyRel L P a (core2.ind2 (-g) b) := by
  constructor
  · rintro ⟨m, h1, φ, hφ, h2⟩
    refine ⟨L.act2 (-g) m, ?_, φ, hφ, ?_⟩
    · rw [L.left_act2, h1, core1.ind2_inverse]
    · rw [hP φ hφ (-g) m, L.right_act2, h2]
  · rintro ⟨m, h1, φ, hφ, h2⟩
    refine ⟨L.act2 g m, ?_, φ, hφ, ?_⟩
    · rw [L.left_act2, h1]
    · rw [hP φ hφ g m, L.right_act2, h2, ind2_inv_cancel core2 g b]

/-- Consistency with the frozen (IPL) card: whenever a supply's single
poly-isomorphism E.polyIso belongs to P, the transported relation polyIsoRel
is contained in the family relation.  This is chapter C's one-directional
QP ⊆ R; it does NOT assert R = QP, so no existing consumer of
cardIPLExchangeShape is strengthened or weakened: the old law is recovered at
P = {E.polyIso} (up to this inclusion).

NL proof: unpack the polyIsoRel witness (m, h1, h2); the same m and
φ := E.polyIso ∈ P give the familyRel witness. -/
theorem polyIsoRel_le_familyRel {Label : Type u} {Choice : Type v} [AddGroup Label]
    {core1 core2 : Core Label Choice} (L : LinkSpan core1 core2)
    (E : CardIPLTransportSupply L) (P : Set (L.mid ≃ L.mid))
    (h : E.polyIso ∈ P) (a b : Choice) :
    polyIsoRel L E a b → familyRel L P a b := by
  rintro ⟨m, h1, h2⟩
  exact ⟨m, h1, E.polyIso, h, h2⟩

end LeanFormal.IUT.Tmp.N8Group5

open LeanFormal.IUT.Tmp.N8Group5
#print axioms familyRel
#print axioms familyRel_ind1_iff
#print axioms familyRel_ind2_iff
#print axioms polyIsoRel_le_familyRel
