import tmp.sheaf.xif.paper.S1951KummerEvaluationSquareActual
import tmp.sheaf.xif.paper.S1958FullLogKummerUQActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTII.Frobenioid.SourceKappaOrbitUnitsActionSupply

/-!
# S1959: the paper coric vertices and the operation-level Kummer/evaluation arrows

Layer: O (original Theta-link / q-pilot), on the source-faithful S1895 input.

S1951/S1958 constructed the reduced Kummer-evaluation square on four *source*
F-prime-strips envStrip/gauStrip/lgpStrip/lgpLowerStrip.  Those are actual
source strips, but they are not the paper's four coric vertices
F_env/F_gau/F_LGP/F_lgp: the paper's vertices are F^⊩-prime-strips built
from theta/Gaussian monoids and global realified Frobenioids (IUT II,
Corollary 4.6, (iv), (v); Corollary 4.10, (ii); IUT III, Proposition 3.7,
(iii), (iv)).  This file does two things.

## 1. The strongest reduced construction available

It lifts the four actual source strips to the times-mu prime-strip layer
SourceFTimesMuPrimeStrip (the tree's reduced model of the F^⊢▶×μ layer),
and constructs, as full poly-isomorphisms of those times-mu prime-strips,

* the upper evaluation arrow env -> gau,
* the lower horizontal LGP -> lgp,
* the two vertical Kummer arrows env -> LGP and gau -> lgp (in the
  orientation of SourceFTimesMuPrimeStripPolyIsomorphismSquare),
* the commuting square, with both two-sided horizontal-existence fields.

The times-mu component of every arrow is the torsion-quotient transport
TimesMuQuotient.congr (Units.mapEquiv phi.isoMon v) induced by the actual
source strip equivalence phi; the F-component is the actual source link
I.fLinkAt.  This is a checked construction, not a fake inhabitant, but it is
still the reduced strip-equivalence-induced layer.

## 2. The exact first missing

The paper's four vertices and operation-level arrows are **not** constructed
here, and no placeholder is introduced for them.

The first missing is two-level.  At the type level, the tree has no
F^⊩-prime-strip carrier at all: FPrimeStrip is only the F^⊢ part, and the
only global realified Frobenioid attached to the S1895 input is C^⊩mod.  At
the construction level, the first object the paper constructs is the local
theta monoid assignment

  PsiFenv(daggerHT_Theta) = {Psi_{daggerF_Theta,v}}_{v in V}

of IUT II, Corollary 4.6, (iv), whose local construction is the
group-theoretic algorithm of IUT II, Proposition 4.1, (i)--(iv)
(Psi_env(Pi_v)).  The active LeanFormal/Iut tree contains no theta monoid and no Gaussian
monoid: HodgeTheater records only thetaPacket (a finite theta packet) and an
arbitrary primeStrip, and no construction of an F-prime-strip from a theta
or Gaussian monoid exists.  (The vendor/promachina snapshots contain only
label/degree shadows; they are not imported here.)  The Theta-bridge/gluing input of Corollary
4.6, (iv), is also only a reduced Hodge theater in the tree; if the paper's
full Theta-bridge is required as input, that gluing is the first missing.
Taking the tree's OriginalInput as the input, the first missing construction
specific to the four vertices is PsiFenv.  The next missing objects are the global realified
Frobenioids C^⊩env(daggerHT_Theta), C^⊩gau(daggerHT_Theta) (Corollary 4.6,
(v)), and the F^⊩-prime-strip packaging (C^⊩, Prime(C^⊩) = V, F^⊢, {rho_v})
of IUT I, Remark 5.2.1, (ii), and IUT II, Definition 4.9, (vii)--(viii).
The tree has only the F^⊢ carrier FPrimeStrip and the one global realified
Frobenioid paperGlobalRealifiedFrobenioid D (= C^⊩mod), not the four paper
vertices.

For the operation-level Kummer arrow of IUT II, Definition 4.9, (i), the
missing domain is the group-theoretic module O^×μ(G) reconstructed from the
local Galois group by the algorithm G -> (G acting on O^×(G)) of IUT II,
Example 1.8, (iii), (iv).  The existing KappaOrbitUnitsActionDatum interface
records exactly the required data, but the unconditional inhabitants in the
tree are the canonical/self completions with TimesMuKummer.Isomorphism.refl
or its conjugate; the tree contains no actual kappa^×μ : O^×μ(G) = O^×μ(A)
from source data.  Likewise
the evaluation isomorphism of Corollary 4.10, (ii), is not constructed:
S1951's evaluation unit layer is the strip-equivalence-induced unit map, not
the evaluation operation of Corollary 4.6, (iv), (v).

The four source strips used below are the prime strips of four *distinct*
Hodge theaters (proved below); the paper's four vertices are constructed from
one Theta±ellNF-Hodge theater and its theta/Gaussian monoids.  This is a
second, independent reason the reduced square is not the paper square.  No
Prop slot, empty type, arbitrary inhabitant, sorry or axiom is used; the
missing objects are recorded as the existing interfaces they are, not
replaced by a fake type.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S1959PaperCoricVerticesActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1958FullLogKummerUQActual

/-- The place type of the S1895 paper input. -/
abbrev PaperV : Type := S1951KummerEvaluationSquareActual.PaperV

/-! ## 1. The reduced times-mu vertices -/

/-- The canonical times-mu prime-strip on a source F-prime-strip. -/
noncomputable abbrev tmVertex (F : FPrimeStrip PaperV) :
    SourceFTimesMuPrimeStrip PaperV :=
  SourceFTimesMuPrimeStrip.canonical F

/-- The full poly-isomorphism of times-mu prime-strips induced by an actual
source strip equivalence.  Its times-mu component is the torsion-quotient
transport of the units, i.e. the reduced strip-equivalence-induced Kummer
map, not the operation-level kappa^×μ of IUT II, Definition 4.9, (i). -/
noncomputable def tmLinkOf {F F' : FPrimeStrip PaperV}
    (phi : FPrimeStripEquiv F F') :
    SourceFTimesMuPrimeStripFullPolyIsomorphism (tmVertex F) (tmVertex F') :=
  SourceFTimesMuPrimeStripFullPolyIsomorphism.ofEquivalence
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift phi)

/-- Composition of induced full poly-isomorphisms is induced by the composite
source strip equivalence. -/
theorem tmLinkOf_comp {F F' F'' : FPrimeStrip PaperV}
    (phi : FPrimeStripEquiv F F') (psi : FPrimeStripEquiv F' F'') :
    SourceFTimesMuPrimeStripFullPolyIsomorphism.comp (tmLinkOf phi) (tmLinkOf psi) =
      tmLinkOf (FPrimeStripEquiv.trans phi psi) := by
  rw [tmLinkOf, tmLinkOf, tmLinkOf]
  rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_ofEquivalence]
  apply Quotient.sound
  exact SourceFTimesMuPrimeStripEquivalence.NaturallyIsomorphic.canonicalLift_trans phi psi

/-- The F-component of an induced full poly-isomorphism is the actual source
strip equivalence. -/
theorem tmLinkOf_toF {F F' : FPrimeStrip PaperV}
    (phi : FPrimeStripEquiv F F') :
    SourceFTimesMuPrimeStripEquivalence.toF
      (SourceFTimesMuPrimeStripEquivalence.canonicalLift phi) = phi := rfl

/-- The times-mu component of an induced full poly-isomorphism is the
torsion-quotient transport of the unit map.  This is the exact reduced
content of every Kummer or evaluation arrow below. -/
theorem tmLinkOf_isoTimesMu {F F' : FPrimeStrip PaperV}
    (phi : FPrimeStripEquiv F F') (v : PaperV) :
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift phi).isoTimesMu v =
      TimesMuQuotient.congr (Units.mapEquiv (phi.isoMon v)) := rfl

/-! ## 2. The four actual source vertices and their links -/

namespace ReducedVertex

variable (D : S1895PaperInput)

/-- The times-mu lift of the actual source strip used for the paper's env
corner.  It is the reduced F^⊢▶×μ vertex, not the paper's F^⊩ vertex. -/
noncomputable abbrev env : SourceFTimesMuPrimeStrip PaperV :=
  tmVertex (envStrip D)

/-- The times-mu lift of the actual source strip used for the paper's gau
corner. -/
noncomputable abbrev gau : SourceFTimesMuPrimeStrip PaperV :=
  tmVertex (gauStrip D)

/-- The times-mu lift of the actual source strip used for the paper's LGP
corner. -/
noncomputable abbrev LGP : SourceFTimesMuPrimeStrip PaperV :=
  tmVertex (lgpStrip D)

/-- The times-mu lift of the actual source strip used for the paper's lgp
corner. -/
noncomputable abbrev lgp : SourceFTimesMuPrimeStrip PaperV :=
  tmVertex (lgpLowerStrip D)

/-- The upper evaluation full poly-isomorphism env -> gau, induced by the
actual source link fLinkAt 0 0 0 1. -/
noncomputable def upperEvaluation :
    SourceFTimesMuPrimeStripFullPolyIsomorphism (env D) (gau D) :=
  tmLinkOf (linkEnvToGau D)

/-- The lower horizontal full poly-isomorphism LGP -> lgp, induced by the
actual source link fLinkAt 1 0 1 1. -/
noncomputable def lowerHorizontal :
    SourceFTimesMuPrimeStripFullPolyIsomorphism (LGP D) (lgp D) :=
  tmLinkOf (linkLGPToLgpLower D)

/-- The left vertical Kummer full poly-isomorphism, in the orientation
env -> LGP of the full-poly square (the inverse of the actual source link
fLinkAt 1 0 0 0). -/
noncomputable def leftKummer :
    SourceFTimesMuPrimeStripFullPolyIsomorphism (env D) (LGP D) :=
  tmLinkOf (FPrimeStripEquiv.symm (linkLGPToEnv D))

/-- The right vertical Kummer full poly-isomorphism, in the orientation
gau -> lgp of the full-poly square (the inverse of the actual source link
fLinkAt 1 1 0 1). -/
noncomputable def rightKummer :
    SourceFTimesMuPrimeStripFullPolyIsomorphism (gau D) (lgp D) :=
  tmLinkOf (FPrimeStripEquiv.symm (linkLgpLowerToGau D))

/-- The F-prime-strip component of the upper evaluation arrow is exactly the
generic source link fLinkAt 0 0 0 1; it is not an evaluation operation. -/
theorem upperEvaluation_strip (D : S1895PaperInput) :
    SourceFTimesMuPrimeStripEquivalence.toF
      (SourceFTimesMuPrimeStripEquivalence.canonicalLift (linkEnvToGau D)) =
        (paperInput D).fLinkAt 0 0 0 1 := rfl

/-- The F-prime-strip component of the lower horizontal is exactly the generic
source link fLinkAt 1 0 1 1; it is not the paper's Corollary 4.10, (ii),
evaluation isomorphism. -/
theorem lowerHorizontal_strip (D : S1895PaperInput) :
    SourceFTimesMuPrimeStripEquivalence.toF
      (SourceFTimesMuPrimeStripEquivalence.canonicalLift (linkLGPToLgpLower D)) =
        (paperInput D).fLinkAt 1 0 1 1 := rfl

/-- The F-prime-strip component of the left Kummer arrow is the inverse of the
generic source link fLinkAt 1 0 0 0. -/
theorem leftKummer_strip (D : S1895PaperInput) :
    SourceFTimesMuPrimeStripEquivalence.toF
      (SourceFTimesMuPrimeStripEquivalence.canonicalLift
        (FPrimeStripEquiv.symm (linkLGPToEnv D))) =
        FPrimeStripEquiv.symm ((paperInput D).fLinkAt 1 0 0 0) := rfl

/-- The F-prime-strip component of the right Kummer arrow is the inverse of the
generic source link fLinkAt 1 1 0 1. -/
theorem rightKummer_strip (D : S1895PaperInput) :
    SourceFTimesMuPrimeStripEquivalence.toF
      (SourceFTimesMuPrimeStripEquivalence.canonicalLift
        (FPrimeStripEquiv.symm (linkLgpLowerToGau D))) =
        FPrimeStripEquiv.symm ((paperInput D).fLinkAt 1 1 0 1) := rfl

end ReducedVertex

/-! ## 3. The reduced full-poly Kummer-evaluation square -/

/-- The four strip-level fields of S1951's square are the four actual source
links, definitionally.  These lemmas let the square's commutation be read at
the level of the link composites. -/
@[simp] theorem kummerEvaluationSquare_upperHorizontal (D : S1895PaperInput) :
    (kummerEvaluationSquare D).upperHorizontal = upperEvaluation D := rfl

@[simp] theorem kummerEvaluationSquare_leftKummer (D : S1895PaperInput) :
    (kummerEvaluationSquare D).leftKummer = leftKummer D := rfl

@[simp] theorem kummerEvaluationSquare_rightKummer (D : S1895PaperInput) :
    (kummerEvaluationSquare D).rightKummer = rightKummer D := rfl

/-- The commutation of the reduced full-poly square.  It is exactly S1951's
commutes after unfolding the four strip representatives, transported along
canonicalLift. -/
theorem reducedSquare_commutes (D : S1895PaperInput) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
        (ReducedVertex.leftKummer D) (ReducedVertex.lowerHorizontal D) =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
        (ReducedVertex.upperEvaluation D) (ReducedVertex.rightKummer D) := by
  have hsq := (kummerEvaluationSquare D).commutes
  rw [kummerEvaluationSquare_upperHorizontal D,
    kummerEvaluationSquare_leftKummer D,
    kummerEvaluationSquare_rightKummer D,
    upperEvaluation_stripIso D, leftKummer_stripIso D,
    rightKummer_stripIso D, lowerHorizontal_stripIso D] at hsq
  change SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
      (tmLinkOf (FPrimeStripEquiv.symm (linkLGPToEnv D)))
      (tmLinkOf (linkLGPToLgpLower D)) =
    SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
      (tmLinkOf (linkEnvToGau D))
      (tmLinkOf (FPrimeStripEquiv.symm (linkLgpLowerToGau D)))
  rw [tmLinkOf_comp, tmLinkOf_comp]
  exact congrArg tmLinkOf hsq

/-- The reduced full-poly Kummer-evaluation square on the four times-mu lifts of
the actual source strips.  This is the strongest square-level object the
current source interface supports; it is not the paper's square on the four
coric vertices. -/
noncomputable def reducedSquare (D : S1895PaperInput) :
    SourceFTimesMuPrimeStripPolyIsomorphismSquare
      (ReducedVertex.env D) (ReducedVertex.gau D)
      (ReducedVertex.LGP D) (ReducedVertex.lgp D) where
  upperHorizontal := ReducedVertex.upperEvaluation D
  lowerHorizontal := ReducedVertex.lowerHorizontal D
  leftKummer := ReducedVertex.leftKummer D
  rightKummer := ReducedVertex.rightKummer D
  commutes := reducedSquare_commutes D
  upperToLower upper := by
    refine ⟨SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
      (SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
        (SourceFTimesMuPrimeStripFullPolyIsomorphism.symm
          (ReducedVertex.leftKummer D)) upper)
      (ReducedVertex.rightKummer D), ?_⟩
    rw [← SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc]
    rw [← SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc]
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_symm]
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.id_comp]
  lowerToUpper lower := by
    refine ⟨SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
      (SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
        (ReducedVertex.leftKummer D) lower)
      (SourceFTimesMuPrimeStripFullPolyIsomorphism.symm
        (ReducedVertex.rightKummer D)), ?_⟩
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_assoc]
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.symm_comp]
    rw [SourceFTimesMuPrimeStripFullPolyIsomorphism.comp_id]

/-- The two-path equality of the reduced full-poly square, in the
commuting-square form. -/
theorem reducedSquare_twoPath (D : S1895PaperInput) :
    SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
        (ReducedVertex.leftKummer D)
        (ReducedVertex.lowerHorizontal D) =
      SourceFTimesMuPrimeStripFullPolyIsomorphism.comp
        (ReducedVertex.upperEvaluation D)
        (ReducedVertex.rightKummer D) :=
  reducedSquare_commutes D

/-! ## 4. Why the reduced vertices are not the paper vertices -/

/-- The env source strip is the prime strip of the Hodge theater at (0,0). -/
theorem envStrip_eq_theaterAt_zero_zero (D : S1895PaperInput) :
    envStrip D = ((paperInput D).theaterAt 0 0).primeStrip := rfl

/-- The gau source strip is the prime strip of the Hodge theater at (0,1). -/
theorem gauStrip_eq_theaterAt_zero_one (D : S1895PaperInput) :
    gauStrip D = ((paperInput D).theaterAt 0 1).primeStrip := rfl

/-- The LGP source strip is the prime strip of the Hodge theater at (1,0). -/
theorem lgpStrip_eq_theaterAt_one_zero (D : S1895PaperInput) :
    lgpStrip D = ((paperInput D).theaterAt 1 0).primeStrip := rfl

/-- The lower lgp source strip is the prime strip of the Hodge theater at
(1,1). -/
theorem lgpLowerStrip_eq_theaterAt_one_one (D : S1895PaperInput) :
    lgpLowerStrip D = ((paperInput D).theaterAt 1 1).primeStrip := rfl

/-- The four source strips used by S1951 come from four pairwise distinct
Hodge theaters.  In the paper, the four coric vertices are constructed from
one Theta±ellNF-Hodge theater and its theta/Gaussian monoids (IUT II,
Corollary 4.6, (iv), (v); IUT III, Remark 3.10.2).  This theorem records the
structural mismatch at the source-strip level; it does not identify the
source strips with the paper vertices. -/
theorem fourSourceStrips_from_distinct_theaters (D : S1895PaperInput) :
    ((paperInput D).theaterAt 0 0 ≠ (paperInput D).theaterAt 0 1) ∧
    ((paperInput D).theaterAt 0 0 ≠ (paperInput D).theaterAt 1 0) ∧
    ((paperInput D).theaterAt 0 0 ≠ (paperInput D).theaterAt 1 1) ∧
    ((paperInput D).theaterAt 0 1 ≠ (paperInput D).theaterAt 1 0) ∧
    ((paperInput D).theaterAt 0 1 ≠ (paperInput D).theaterAt 1 1) ∧
    ((paperInput D).theaterAt 1 0 ≠ (paperInput D).theaterAt 1 1) := by
  have h : ∀ a b c d : Int, (paperInput D).theaterAt a b =
      (paperInput D).theaterAt c d → a = c ∧ b = d := by
    intro a b c d hab
    exact (paperInput D).theaterAt_eq_iff.mp hab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hh; obtain ⟨h1, h2⟩ := h 0 0 0 1 hh; omega
  · intro hh; obtain ⟨h1, h2⟩ := h 0 0 1 0 hh; omega
  · intro hh; obtain ⟨h1, h2⟩ := h 0 0 1 1 hh; omega
  · intro hh; obtain ⟨h1, h2⟩ := h 0 1 1 0 hh; omega
  · intro hh; obtain ⟨h1, h2⟩ := h 0 1 1 1 hh; omega
  · intro hh; obtain ⟨h1, h2⟩ := h 1 0 1 1 hh; omega

/-! ## 5. The operation-level Kummer and evaluation data

The reduced Kummer layer of the left arrow is the strip-equivalence-induced
unit map.  This is *not* the operation-level kappa^×μ of IUT II, Definition
4.9, (i), whose domain is the group-theoretic module O^×μ(G): the latter is
not defined in the tree.  The following theorems record the exact content of
what is constructed.
-/

/-- The left reduced Kummer arrow's per-place isomorphism is the actual
strip-equivalence-induced quotient-unit isomorphism. -/
theorem leftKummer_layer_equiv (D : S1895PaperInput) (v : PaperV) :
    ((leftKummer D).layer.kummer v).equiv =
      S1951KummerEvaluationSquareActual.General.quotientUnitsEquiv
        (Units.mapEquiv ((linkLGPToEnv D).isoMon v)) := rfl

/-- The upper reduced evaluation arrow's per-place unit layer is the actual
strip-equivalence-induced quotient-unit isomorphism. -/
theorem upperEvaluation_unitLayer (D : S1895PaperInput) (v : PaperV) :
    (upperEvaluation D).unitPortion.unitLayer v =
      S1951KummerEvaluationSquareActual.General.quotientUnitsEquiv
        (Units.mapEquiv ((linkEnvToGau D).isoMon v)) := rfl

/-- The full-poly left Kummer arrow carries the same torsion-quotient
transport on its times-mu component. -/
theorem tmLeftKummer_isoTimesMu (D : S1895PaperInput) (v : PaperV) :
    (SourceFTimesMuPrimeStripEquivalence.canonicalLift
      (FPrimeStripEquiv.symm (linkLGPToEnv D))).isoTimesMu v =
      TimesMuQuotient.congr
        (Units.mapEquiv ((FPrimeStripEquiv.symm (linkLGPToEnv D)).isoMon v)) :=
  tmLinkOf_isoTimesMu _ v

/-! ## 6. The exact first missing, as existing interfaces

No new missing type and no Prop slot is introduced.  The existing interface
which already names the operation-level Definition 4.9, (i), datum is
KappaOrbitUnitsActionDatum; it is *not* inhabited here for the paper
vertices, because its sourceUnits carrier and its kappa representative must
come from the group-theoretic algorithm G -> (G acting on O^×(G)), which is
absent.  The four paper vertices would have to be F^⊩-prime-strips, for which
the tree has no carrier at all (only FPrimeStrip and C^⊩mod); the first
missing definition in the paper's construction order is the theta monoid
assignment PsiFenv(daggerHT_Theta) of IUT II, Corollary 4.6, (iv).  These are
research findings, not Lean objects fabricated by this file.
-/

#check KappaOrbitUnitsActionDatum
#check S1927KummerEvaluationSquareActual
#check paperGlobalRealifiedFrobenioid

/-! ## 7. Axiom probes -/

#print axioms ReducedVertex.env
#print axioms ReducedVertex.upperEvaluation
#print axioms ReducedVertex.leftKummer
#print axioms reducedSquare_commutes
#print axioms reducedSquare
#print axioms reducedSquare_twoPath
#print axioms fourSourceStrips_from_distinct_theaters
#print axioms leftKummer_layer_equiv
#print axioms upperEvaluation_unitLayer

end LeanFormal.IUT.XiFPaper.S1959PaperCoricVerticesActual