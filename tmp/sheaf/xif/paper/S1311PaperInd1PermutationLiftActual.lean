import tmp.sheaf.xif.paper.S1264SourceCapsuleInd1Actual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S1311: the paper's Ind1 permutation and the canonical capsule slice

S1264SourceCapsuleInd1Actual records the first precise datum missing from the
paper's Ind1 automorphism:

* SourcePermutationCapsuleLift.index_compat asks that the source family
  permutation I.family.permutation, transported through I.index_equiv, map
  the canonical slice i |-> (i,n) of the capsule assignment to the same
  slice.

This file determines the logical status of that datum.

1.  We give the exact slice criterion: the lift exists if and only if the
    composite index permutation sends every (i,n) with i in the finite
    capsule to a pair (k,n) with k again in the finite capsule.
2.  We prove that this criterion is not a consequence of the OriginalInput
    fields.  For every supplied source datum S we build a genuine
    OriginalInput (over the actual concrete theater family of
    SourceUnitRegionHaarDataActual, with an actual HodgeTheaterLink system)
    whose family permutation is the row shift (i,n) |-> (i,n+1).  No
    SourcePermutationCapsuleLift exists for that input at n = 0 on the
    capsule {0,1}.  Hence no construction from I.family.permutation,
    I.family.permutationLink, and I.index_equiv alone can produce the lift.
    The row-shifted input is a model of the OriginalInput contract, not a
    claim about the paper's own family; it is precisely a model showing that
    the contract does not force the missing slice compatibility.
3.  Conversely, the concrete identity-permutation input of
    SourceUnitRegionHaarDataActual does admit the lift, so the obstruction is
    genuinely the slice compatibility and not a defect of the structure.

No sorry, axiom, or PUnit/True gate is used.  Nonempty appears only as the
existence property being characterized or refuted.  The counterexample input
is a legitimate OriginalInput: its permutationLink is the actual source link
at (sigma i) i, and the naturality square follows from the actual transitivity
of the source link system.
-/

namespace LeanFormal.IUT.XiFPaper.S1311PaperInd1PermutationLiftActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.S1264SourceCapsuleInd1Actual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. The exact slice criterion -/

/-- The source-index image of p under the family permutation, expressed in
    the Int x Int coordinate system.  This is the composite
    index_equiv o family.permutation o index_equiv.symm. -/
def sourcePermutationIndex
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (p : SourceTheorem311Index) : SourceTheorem311Index :=
  I.index_equiv (I.family.permutation (I.indexOf p.1 p.2))

/-- The composite index permutation is injective. -/
theorem sourcePermutationIndex_injective
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Function.Injective (sourcePermutationIndex I) := by
  intro p q hpq
  have h1 : I.family.permutation (I.indexOf p.1 p.2) =
      I.family.permutation (I.indexOf q.1 q.2) :=
    I.index_equiv.injective hpq
  have h2 : I.indexOf p.1 p.2 = I.indexOf q.1 q.2 :=
    I.family.permutation.injective h1
  exact I.indexOf_injective h2

/-- Exact criterion.  A SourcePermutationCapsuleLift exists precisely when
    the composite index permutation carries the canonical finite slice
    {(i,n) | i : Capsule j} into itself (the second coordinate is preserved
    and the first coordinate is again a capsule label). -/
theorem sourcePermutationCapsuleLift_nonempty_iff
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (j : Fin (capsuleLevels l)) :
    Nonempty (SourcePermutationCapsuleLift I n j) <->
      forall i : Capsule j.val, exists k : Capsule j.val,
        sourcePermutationIndex I (Int.ofNat i.val, n) =
          (Int.ofNat k.val, n) := by
  constructor
  . rintro ⟨L⟩ i
    exact ⟨L.perm i, by
      simpa [sourcePermutationIndex, canonicalCapsuleTheaterAssignment]
        using L.index_compat i⟩
  . intro h
    classical
    choose k hk using h
    let g : Capsule j.val -> Capsule j.val := k
    have hg_inj : Function.Injective g := by
      intro i i' hii
      have h1 : sourcePermutationIndex I (Int.ofNat i.val, n) =
          sourcePermutationIndex I (Int.ofNat i'.val, n) := by
        have hii' : k i = k i' := hii
        rw [hk i, hk i', hii']
      have h2 : (Int.ofNat i.val, n) = (Int.ofNat i'.val, n) :=
        sourcePermutationIndex_injective I h1
      have h4 : (i.val : Int) = (i'.val : Int) := congrArg Prod.fst h2
      exact Fin.ext (Int.ofNat.inj h4)
    have hg_bij : Function.Bijective g :=
      Finite.injective_iff_bijective.mp hg_inj
    refine ⟨{ perm := Equiv.ofBijective g hg_bij, index_compat := ?_ }⟩
    intro i
    simpa [sourcePermutationIndex, canonicalCapsuleTheaterAssignment]
      using hk i

/-! ## 2. The concrete identity-permutation input admits the lift -/

/-- For the concrete identity-permutation source input of
    SourceUnitRegionHaarDataActual, the canonical slice is fixed, so the
    identity capsule permutation supplies the lift. -/
theorem sourceHaarActual_lift
    (S : SourceDefinition31Data.{ua} l) (n : Int)
    (j : Fin (capsuleLevels l)) :
    Nonempty (SourcePermutationCapsuleLift
      (sourceHaarActualOriginalInput (l := l) S) n j) := by
  refine ⟨{ perm := Equiv.refl (Capsule j.val), index_compat := ?_ }⟩
  intro i
  simp [sourceHaarActualOriginalInput, sourceHaarActualFamily,
    canonicalCapsuleTheaterAssignment, OriginalInput.indexOf]
  rfl

/-! ## 3. A legitimate input with no lift: the row shift -/

/-- The row shift (i,n) |-> (i,n+1) of the source index. -/
def sourceIndexRowShift : Equiv.Perm SourceTheorem311Index where
  toFun p := (p.1, p.2 + 1)
  invFun p := (p.1, p.2 - 1)
  left_inv := by
    intro p
    ext <;> simp
  right_inv := by
    intro p
    ext <;> simp

/-- The concrete source family with its permutation replaced by sigma.  The
    permutationLink is the actual source link from sigma i to i; the
    naturality square is exactly the transitivity of the actual link system. -/
def permutedSourceHaarFamily
    (A : InitialThetaArithmeticData.{ua} l)
    (sigma : Equiv.Perm SourceTheorem311Index) :
    SourceHodgeTheaterFamily.{ua, 0, 0, 0, 0} l Unit :=
  { sourceHaarActualFamily (l := l) A with
    permutation := sigma
    permutationLink := fun i =>
      sourceHaarActualTheaterLink (l := l) A (sigma i) i
    permutation_naturality := by
      intro i j
      change HodgeTheaterLink.trans
          (sourceHaarActualTheaterLink (l := l) A (sigma i) (sigma j))
          (sourceHaarActualTheaterLink (l := l) A (sigma j) j) =
        HodgeTheaterLink.trans
          (sourceHaarActualTheaterLink (l := l) A (sigma i) i)
          (sourceHaarActualTheaterLink (l := l) A i j)
      rw [sourceHaarActualTheaterLink_trans, sourceHaarActualTheaterLink_trans] }

/-- The legitimate OriginalInput with the row-shift family permutation. -/
def rowShiftedSourceHaarInput
    (S : SourceDefinition31Data.{ua} l) :
    OriginalInput.{ua, 0, 0, 0, 0} l Unit where
  initial := S
  family := permutedSourceHaarFamily (l := l) S.arithmetic sourceIndexRowShift
  index_equiv := Equiv.refl SourceTheorem311Index
  arithmetic_alignment := by
    intro i
    rfl

/-- The index computation for the row-shifted input: the canonical slice point
    (i,n) is sent to (i,n+1). -/
theorem rowShiftedSourceHaarInput_index
    (S : SourceDefinition31Data.{ua} l) (n : Int) (i : Capsule 1) :
    sourcePermutationIndex (rowShiftedSourceHaarInput (l := l) S)
        (Int.ofNat i.val, n) = (Int.ofNat i.val, n + 1) := by
  simp [sourcePermutationIndex, rowShiftedSourceHaarInput,
    permutedSourceHaarFamily, sourceHaarActualFamily, sourceIndexRowShift,
    OriginalInput.indexOf]
  rfl

/-- No SourcePermutationCapsuleLift exists for the row-shifted input at
    n = 0 on the two-element capsule {0,1}. -/
theorem rowShiftedSourceHaarInput_no_lift
    (S : SourceDefinition31Data.{ua} l) :
    Not (Nonempty (SourcePermutationCapsuleLift
      (rowShiftedSourceHaarInput (l := l) S) 0
      ⟨1, one_lt_capsuleLevels l⟩)) := by
  rintro ⟨L⟩
  have h := L.index_compat (0 : Capsule 1)
  have hcomp : sourcePermutationIndex (rowShiftedSourceHaarInput (l := l) S)
      ((0 : Int), (0 : Int)) = ((0 : Int), (1 : Int)) := by
    simpa using rowShiftedSourceHaarInput_index (l := l) S 0 (0 : Capsule 1)
  have hh := congrArg Prod.snd h
  change (sourcePermutationIndex (rowShiftedSourceHaarInput (l := l) S)
    ((0 : Int), (0 : Int))).2 = (0 : Int) at hh
  rw [hcomp] at hh
  norm_num at hh

/-- Consequently the lift is not constructible uniformly from the
    OriginalInput fields: for every supplied source datum there is an
    OriginalInput over it with no lift. -/
theorem sourcePermutationCapsuleLift_not_uniform
    (S : SourceDefinition31Data.{ua} l) :
    Not (forall (I : OriginalInput.{ua, 0, 0, 0, 0} l Unit)
      (n : Int) (j : Fin (capsuleLevels l)),
        Nonempty (SourcePermutationCapsuleLift I n j)) := by
  intro hAll
  exact rowShiftedSourceHaarInput_no_lift (l := l) S
    (hAll (rowShiftedSourceHaarInput (l := l) S) 0
      ⟨1, one_lt_capsuleLevels l⟩)

/-! ## 4. Axiom probes -/

#print axioms sourcePermutationIndex_injective
#print axioms sourcePermutationCapsuleLift_nonempty_iff
#print axioms sourceHaarActual_lift
#print axioms permutedSourceHaarFamily
#print axioms rowShiftedSourceHaarInput
#print axioms rowShiftedSourceHaarInput_index
#print axioms rowShiftedSourceHaarInput_no_lift
#print axioms sourcePermutationCapsuleLift_not_uniform

end LeanFormal.IUT.XiFPaper.S1311PaperInd1PermutationLiftActual
