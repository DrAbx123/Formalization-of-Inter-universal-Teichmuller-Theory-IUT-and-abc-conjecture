import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1359OrbifoldPiActual
import tmp.sheaf.xif.paper.S1319OrbicurveClauseActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36FreeProfinitePi
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtalePiOneKernelRealization

/-!
# S1490: the actual residual OrbicurveFundamentalGroupData for S1419

S1419 constructs the actual nonterminal hyperbolic orbicurve

  S1419Orbicurve l : HyperbolicOrbicurve (S1348K l)

with signature oncePuncturedElliptic.  Its exact residual is the certified
orbifold fundamental-group data

  Iut.OrbicurveFundamentalGroupData (S1419Orbicurve l)
     (Iut.AbsoluteGaloisProfinite (S1348K l)).

The tree does not contain the etale fundamental group of a curve, nor any
inhabitant of Iut.OrbicurveEtaleFundamentalGroup for any orbicurve.  This file
therefore does not fabricate that certificate.  It does two things.

## 1. The actual group-level exact sequence

The geometric graph group of the once-punctured elliptic curve is the free
profinite group on two generators (freeProfiniteGroupTwo, already constructed
in Example36FreeProfinitePi).  The arithmetic base is the actual absolute
Galois group G_K = AbsoluteGaloisProfinite (S1348K l).  From these actual
groups this file constructs the product model

  1 -> Pi_graph -> G_K x Pi_graph -> G_K -> 1

via the canonical profinite-kernel exact sequence.  The projection is the
actual first projection of the product, it is surjective, and its kernel is
multiplicatively equivalent to freeProfiniteGroupTwo, hence nontrivial and
nonabelian.  This is a group-level shape model only: it is never inserted into
the target data and is not claimed to be the arithmetic orbifold fundamental
group of the S1419 curve.  The actual action of G_K on the geometric graph
group is part of the missing arithmetic theorem, not supplied here.

## 2. The exact first missing structure

The first missing structure is the arithmetic finite-etale certificate
S1490ArithmeticPiFirstMissing l, consisting of an actual profinite group G, an
actual OrbicurveEtaleFundamentalGroup (S1419Orbicurve l) G, and an actual
surjective projection G -> G_K.  The second missing field is the geometric
certificate over the closed kernel of that projection.  The theorem
S1490Target_nonempty_iff_firstMissing proves that the target
OrbicurveFundamentalGroupData is inhabited exactly when these two certificates
are supplied.  Thus the exact first missing structure is isolated, and no
group-level model is passed off as the curve orbifold fundamental group.

## Exclusions

* The l-torsion exact sequence S1319LTorsionExactSequence is recorded but never
  used.  Its base group is definitionally the range of the l-torsion
  representation (a subgroup of a general linear group), not the absolute
  Galois group, so it is not a substitute for the orbifold fundamental group.
* The S1419 orbicurve is nonterminal and not a point fiber; the nonterminal
  certificate and the point-fiber negation are re-exported below.
* No terminal stack, point fiber, arbitrary carrier, new axiom or sorry is
  used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1490OrbicurveFundamentalGroupActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1359OrbifoldPiActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

/-! ## 1. The target and the actual graph group -/

/-- The actual absolute Galois group of the S1348 Gaussian field. -/
abbrev S1490Galois (l : PrimeGeFive) : ProfiniteGrp :=
  Iut.AbsoluteGaloisProfinite (S1348K l)

/-- The exact residual of S1419: certified orbifold fundamental-group data
for the actual nonterminal orbicurve over the actual absolute Galois group. -/
abbrev S1490Target (l : PrimeGeFive) : Type 1 :=
  Iut.OrbicurveFundamentalGroupData (S1419Orbicurve l) (S1490Galois l)

/-- The graph group of the once-punctured elliptic curve: the free profinite
group on two generators already constructed in the tree. -/
abbrev S1490GraphGroup : ProfiniteGrp := freeProfiniteGroupTwo

/-- The graph group is nontrivial. -/
theorem S1490GraphGroup_nontrivial : Nontrivial (S1490GraphGroup : Type) :=
  freeProfiniteGroupTwo_nontrivial

/-- The graph group is nonabelian. -/
theorem S1490GraphGroup_not_commutative :
    ¬ ∀ a b : (S1490GraphGroup : Type), a * b = b * a :=
  freeProfiniteGroupTwo_not_commutative

/-! ## 2. The group-level exact-sequence model -/

/-- The actual product model of the expected arithmetic extension.
This is a group-level model only; it is not the arithmetic orbifold
fundamental group of the S1419 curve and is never inserted into the target. -/
abbrev S1490ModelArithmeticGroup (l : PrimeGeFive) : ProfiniteGrp :=
  profiniteProduct (S1490Galois l) S1490GraphGroup

/-- The projection of the product model to the actual absolute Galois group. -/
abbrev S1490ModelProjection (l : PrimeGeFive) :
    S1490ModelArithmeticGroup l ⟶ S1490Galois l :=
  profiniteProductFst (S1490Galois l) S1490GraphGroup

/-- The model projection is surjective. -/
theorem S1490ModelProjection_surjective (l : PrimeGeFive) :
    Function.Surjective (S1490ModelProjection l) := by
  intro x
  exact profiniteProductFst_surjective (S1490Galois l) S1490GraphGroup x

/-- The kernel of the model projection is multiplicatively equivalent to the
actual graph group. -/
noncomputable def S1490ModelKernelMulEquiv (l : PrimeGeFive) :
    (Iut.profiniteKernelClosedSubgroup (S1490ModelProjection l)).toSubgroup ≃*
      (S1490GraphGroup : Type) :=
  prodFstKerMulEquiv (S1490Galois l) (S1490GraphGroup : Type)

/-- The canonical profinite exact sequence of the model projection. -/
noncomputable def S1490ModelSequence (l : PrimeGeFive) :
    Iut.ProfiniteFundamentalExactSequence
      (Iut.closedSubgroupProfiniteGrp
        (Iut.profiniteKernelClosedSubgroup (S1490ModelProjection l)))
      (S1490ModelArithmeticGroup l) (S1490Galois l) :=
  Iut.profiniteKernelExactSequence (S1490ModelProjection l)
    (S1490ModelProjection_surjective l)

private theorem nontrivial_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) [Nontrivial H] : Nontrivial G := by
  rw [nontrivial_iff_exists_ne (1 : G)]
  obtain ⟨h, hh⟩ := (nontrivial_iff_exists_ne (1 : H)).mp inferInstance
  exact ⟨e.symm h, fun h1 => hh (by simpa using congrArg e h1)⟩

/-- The closed kernel subgroup of the model has a nontrivial underlying type. -/
theorem S1490ModelKernelClosedSubgroup_nontrivial (l : PrimeGeFive) :
    Nontrivial (Iut.profiniteKernelClosedSubgroup
      (S1490ModelProjection l)).toSubgroup := by
  letI : Nontrivial (S1490GraphGroup : Type) := S1490GraphGroup_nontrivial
  exact nontrivial_of_mulEquiv (S1490ModelKernelMulEquiv l)

/-- The geometric term of the model exact sequence is nontrivial. -/
theorem S1490ModelKernel_nontrivial (l : PrimeGeFive) :
    Nontrivial (Iut.closedSubgroupProfiniteGrp
      (Iut.profiniteKernelClosedSubgroup (S1490ModelProjection l)) : Type) := by
  change Nontrivial (Iut.profiniteKernelClosedSubgroup
    (S1490ModelProjection l)).toSubgroup
  exact S1490ModelKernelClosedSubgroup_nontrivial l

/-! The model sequence has the expected projection and inclusion. -/

/-- The projection of the model exact sequence is the model projection. -/
theorem S1490ModelSequence_projection (l : PrimeGeFive) :
    (S1490ModelSequence l).projection = S1490ModelProjection l := rfl

/-- The inclusion of the model exact sequence is the canonical closed-kernel
inclusion. -/
theorem S1490ModelSequence_inclusion (l : PrimeGeFive) :
    (S1490ModelSequence l).inclusion =
      (Iut.closedSubgroupProfiniteInclusion
        (Iut.profiniteKernelClosedSubgroup
          (S1490ModelProjection l))).hom := rfl

/-- The model projection is surjective. -/
theorem S1490ModelSequence_projection_surjective (l : PrimeGeFive) :
    Function.Surjective (S1490ModelSequence l).projection :=
  (S1490ModelSequence l).projection_surjective

/-- The model inclusion is injective. -/
theorem S1490ModelSequence_inclusion_injective (l : PrimeGeFive) :
    Function.Injective (S1490ModelSequence l).inclusion :=
  (S1490ModelSequence l).inclusion_injective

/-- Exactness of the model sequence: the range of the inclusion is the kernel
of the projection. -/
theorem S1490ModelSequence_exact (l : PrimeGeFive) :
    (S1490ModelSequence l).inclusion.hom.range =
      (S1490ModelSequence l).projection.hom.ker :=
  (S1490ModelSequence l).exact

/-! ## 3. The exact first missing structure -/
/-- The exact first missing structure: an actual finite-etale certificate over
the S1419 orbicurve for an actual profinite group, together with an actual
surjective projection to the absolute Galois group.

The certificate field is exactly Iut.OrbicurveEtaleFundamentalGroup, whose
inhabitant is the tree's missing curve etale fundamental group.  This file
does not construct it. -/
structure S1490ArithmeticPiFirstMissing (l : PrimeGeFive) where
  /-- The arithmetic orbifold fundamental group. -/
  arithmeticGroup : ProfiniteGrp
  /-- The actual finite-etale Galois certificate over the S1419 orbicurve. -/
  arithmetic : Iut.OrbicurveEtaleFundamentalGroup (S1419Orbicurve l) arithmeticGroup
  /-- The projection to the actual absolute Galois group. -/
  projection : arithmeticGroup ⟶ S1490Galois l
  /-- The projection is surjective. -/
  projection_surjective : Function.Surjective projection

/-- The second missing field: the geometric certificate over the closed kernel
of the arithmetic projection. -/
abbrev S1490GeometricPiSecondMissing {l : PrimeGeFive}
    (C : S1490ArithmeticPiFirstMissing l) : Type 1 :=
  Iut.OrbicurveEtaleFundamentalGroup (S1419Orbicurve l)
    (Iut.closedSubgroupProfiniteGrp
      (Iut.profiniteKernelClosedSubgroup C.projection))

/-- Assemble the target from the exact first missing structure and the
geometric certificate over its kernel. -/
noncomputable def S1490TargetOfFirstMissing {l : PrimeGeFive}
    (C : S1490ArithmeticPiFirstMissing l)
    (geometric : S1490GeometricPiSecondMissing C) : S1490Target l where
  arithmeticGroup := C.arithmeticGroup
  arithmetic := C.arithmetic
  projection := C.projection
  projection_surjective := C.projection_surjective
  geometric := geometric

/-- Exactness of the reduction.  The target data is inhabited exactly when the
arithmetic first missing structure and the geometric kernel certificate are
supplied.  This is the precise remaining gap; no group-level substitute is
inserted for the missing finite-etale certificates. -/
theorem S1490Target_nonempty_iff_firstMissing (l : PrimeGeFive) :
    Nonempty (S1490Target l) ↔
      ∃ C : S1490ArithmeticPiFirstMissing l,
        Nonempty (S1490GeometricPiSecondMissing C) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨{ arithmeticGroup := D.arithmeticGroup
             arithmetic := D.arithmetic
             projection := D.projection
             projection_surjective := D.projection_surjective },
           ⟨D.geometric⟩⟩
  · rintro ⟨C, ⟨geometric⟩⟩
    exact ⟨S1490TargetOfFirstMissing C geometric⟩

/-! ## 3.1. The bare etale certificate -/

/-- The bare first missing structure: an actual profinite group together with
an actual finite-etale certificate over the S1419 orbicurve.  The group-level
projection to the absolute Galois group is not part of this hard etale input;
it is supplied separately. -/
abbrev S1490EtaleCertificateFirstMissing (l : PrimeGeFive) : Type 1 :=
  Σ G : ProfiniteGrp, Iut.OrbicurveEtaleFundamentalGroup (S1419Orbicurve l) G

/-- Promote a bare certificate and a surjective group-level projection to the
arithmetic first missing structure. -/
noncomputable def S1490ArithmeticPiFirstMissing.ofCertificate
    {l : PrimeGeFive} (C : S1490EtaleCertificateFirstMissing l)
    (projection : C.1 ⟶ S1490Galois l)
    (projection_surjective : Function.Surjective projection) :
    S1490ArithmeticPiFirstMissing l where
  arithmeticGroup := C.1
  arithmetic := C.2
  projection := projection
  projection_surjective := projection_surjective

/-- The bare etale certificate is necessary for the target. -/
theorem S1490EtaleCertificate_of_target {l : PrimeGeFive}
    (h : Nonempty (S1490Target l)) :
    Nonempty (S1490EtaleCertificateFirstMissing l) := by
  obtain ⟨D⟩ := h
  exact ⟨⟨D.arithmeticGroup, D.arithmetic⟩⟩

/-- **Exactness in bare-certificate form.**  The target is inhabited exactly
when a bare finite-etale certificate, a surjective group-level projection, and
the geometric certificate over its closed kernel are supplied.  This separates
the hard etale input from the group-level choices. -/
theorem S1490Target_nonempty_iff_certificate (l : PrimeGeFive) :
    Nonempty (S1490Target l) ↔
      ∃ C : S1490EtaleCertificateFirstMissing l,
        ∃ (projection : C.1 ⟶ S1490Galois l)
          (_ : Function.Surjective projection),
          Nonempty (Iut.OrbicurveEtaleFundamentalGroup (S1419Orbicurve l)
            (Iut.closedSubgroupProfiniteGrp
              (Iut.profiniteKernelClosedSubgroup projection))) := by
  rw [S1490Target_nonempty_iff_firstMissing]
  constructor
  · rintro ⟨C, hgeom⟩
    exact ⟨⟨C.arithmeticGroup, C.arithmetic⟩, C.projection,
      C.projection_surjective, hgeom⟩
  · rintro ⟨C, projection, hproj, hgeom⟩
    exact ⟨S1490ArithmeticPiFirstMissing.ofCertificate C projection hproj, hgeom⟩

/-- The first missing hard etale input, as a named proposition: an actual
profinite group with an actual finite-etale certificate over the S1419
orbicurve. -/
def S1490BareEtaleCertificateRequired (l : PrimeGeFive) : Prop :=
  Nonempty (S1490EtaleCertificateFirstMissing l)

/-- The bare etale certificate is required by the target. -/
theorem S1490BareEtaleCertificateRequired_of_target {l : PrimeGeFive}
    (h : Nonempty (S1490Target l)) : S1490BareEtaleCertificateRequired l :=
  S1490EtaleCertificate_of_target h

/-- The named exact remaining gap: the bare etale certificate, a surjective
group-level projection, and the geometric certificate over its closed kernel. -/
abbrev S1490ExactRemainingGap (l : PrimeGeFive) : Prop :=
  ∃ C : S1490EtaleCertificateFirstMissing l,
    ∃ (projection : C.1 ⟶ S1490Galois l)
      (_ : Function.Surjective projection),
      Nonempty (Iut.OrbicurveEtaleFundamentalGroup (S1419Orbicurve l)
        (Iut.closedSubgroupProfiniteGrp
          (Iut.profiniteKernelClosedSubgroup projection)))

/-- The target is inhabited exactly when the named exact remaining gap is. -/
theorem S1490Target_nonempty_iff_gap (l : PrimeGeFive) :
    Nonempty (S1490Target l) ↔ S1490ExactRemainingGap l :=
  S1490Target_nonempty_iff_certificate l

/-- The first missing structure is necessary for the target. -/
theorem S1490FirstMissing_of_target {l : PrimeGeFive}
    (h : Nonempty (S1490Target l)) :
    Nonempty (S1490ArithmeticPiFirstMissing l) := by
  obtain ⟨D⟩ := h
  exact ⟨{ arithmeticGroup := D.arithmeticGroup
           arithmetic := D.arithmetic
           projection := D.projection
           projection_surjective := D.projection_surjective }⟩

/-- The arithmetic group of any candidate is nontrivial as soon as the actual
absolute Galois group is nontrivial: surjectivity transfers a nontrivial
element backwards.  (The nontriviality of G_K itself is an arithmetic fact,
not constructed in this file.) -/
theorem S1490ArithmeticGroup_nontrivial_of_galois_nontrivial
    {l : PrimeGeFive} (C : S1490ArithmeticPiFirstMissing l)
    (hG : Nontrivial (S1490Galois l : Type)) :
    Nontrivial (C.arithmeticGroup : Type) := by
  rw [nontrivial_iff_exists_ne (1 : (C.arithmeticGroup : Type))]
  obtain ⟨g, hg⟩ := (nontrivial_iff_exists_ne (1 : (S1490Galois l : Type))).mp hG
  obtain ⟨x, hx⟩ := C.projection_surjective g
  exact ⟨x, fun h => hg (by simpa [h] using hx.symm)⟩

/-- The target is exactly the residual field of the S1419 first field. -/
theorem S1490FirstField_remainder_eq (l : PrimeGeFive) :
    S1359OrbifoldPiRemainder l (S1419FirstField l) = S1490Target l := rfl

/-- The exact sequence of any target is the canonical closed-kernel sequence
of its arithmetic projection; the geometric term is the actual kernel, not an
arbitrary second group. -/
theorem S1490Target_exactSequence_eq (l : PrimeGeFive) (D : S1490Target l) :
    Iut.OrbicurveFundamentalGroupData.exactSequence D =
      Iut.profiniteKernelExactSequence D.projection D.projection_surjective :=
  rfl

/-- The geometric group of any target is definitionally the closed kernel of
its arithmetic projection. -/
theorem S1490Target_geometricGroup_kernel (l : PrimeGeFive) (D : S1490Target l) :
    D.geometric.group =
      Iut.closedSubgroupProfiniteGrp
        (Iut.profiniteKernelClosedSubgroup D.projection) := rfl

/-! ## 4. Nonterminality and non-use of the l-torsion sequence -/

/-- The S1419 orbicurve satisfies the nonterminal condition. -/
theorem S1490Orbicurve_nonterminal (l : PrimeGeFive) :
    S1319NonterminalFiber (S1419Orbicurve l) :=
  S1419NonterminalFiber l

/-- The S1419 orbicurve is not a point fiber. -/
theorem S1490Orbicurve_not_pointFiber (l : PrimeGeFive) :
    ¬ IsPointFiber (S1419Orbicurve l).stack.fiber :=
  (S1359NonterminalFiber_iff_notPointFiber l (S1419Orbicurve l)).mp
    (S1419NonterminalFiber l)

/-- The base group of the target exact sequence is definitionally the actual
absolute Galois group. -/
theorem S1490Target_sourceBaseGroup (l : PrimeGeFive)
    (D : S1490Target l) :
    (S1348SourceExactSequenceOfProfinite
      (Iut.OrbicurveFundamentalGroupData.exactSequence D)).baseGroup =
      (S1490Galois l : Type) := rfl

/-- The base group of the l-torsion sequence is definitionally the range of
the l-torsion representation, not the absolute Galois group.  This is the
formal record that the l-torsion sequence is not used as a substitute. -/
theorem S1490LTorsion_baseGroup (l : PrimeGeFive) :
    (S1319LTorsionExactSequence l).baseGroup =
      (S1319LTorsionRepresentation l).range := rfl

/-- The cover group of the l-torsion sequence is definitionally the source
absolute Galois group; the target cover group is the arithmetic orbifold
group supplied by the first missing structure.  The two sequences are
different objects and no identification is asserted. -/
theorem S1490LTorsion_coverGroup (l : PrimeGeFive) :
    (S1319LTorsionExactSequence l).coverGroup =
      SourceAbsoluteGalois (S1280Arithmetic l) := rfl

/-! ## 5. Axiom footprint -/

#print axioms S1490GraphGroup_nontrivial
#print axioms S1490GraphGroup_not_commutative
#print axioms S1490ModelProjection_surjective
#print axioms S1490ModelKernel_nontrivial
#print axioms S1490ModelSequence_projection
#print axioms S1490ModelSequence_exact
#print axioms S1490Target_nonempty_iff_firstMissing
#print axioms S1490FirstMissing_of_target
#print axioms S1490EtaleCertificate_of_target
#print axioms S1490Target_nonempty_iff_certificate
#print axioms S1490BareEtaleCertificateRequired_of_target
#print axioms S1490Target_nonempty_iff_gap
#print axioms S1490ArithmeticGroup_nontrivial_of_galois_nontrivial
#print axioms S1490Orbicurve_nonterminal
#print axioms S1490Orbicurve_not_pointFiber
#print axioms S1490Target_sourceBaseGroup
#print axioms S1490LTorsion_baseGroup
#print axioms S1490LTorsion_coverGroup
#print axioms S1490FirstField_remainder_eq
#print axioms S1490Target_exactSequence_eq
#print axioms S1490Target_geometricGroup_kernel

end LeanFormal.IUT.XiFPaper.S1490OrbicurveFundamentalGroupActual

end