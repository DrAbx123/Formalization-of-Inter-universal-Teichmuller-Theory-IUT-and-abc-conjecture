/-!
# Indet03: mapping table — first-triangle (Ind1),(Ind2),(Ind3) -> mainline A35 / INDEX

Paper-faithfulness mapping (A35 structural gap).  Sources:
* IUT III, Theorem 3.11, corpus lines 653-679: the three indeterminacies admitted
  in the passage from the BPS to the multiradial representation;
* MHYY "Formalization of IUT (2026-04)" §4, corpus lines 472-501: first triangle
  = BPS -> multiradial representation, constructed up to (Ind1,2,3) / full
  poly-isomorphism with the 0-column;
* IUT III Fig. I.6 (multiradial representation components: log-shells, LGP-monoid
  splitting monoids, number fields).

Mapping to tree declarations (all EXISTING; this batch only adds the first-triangle
instantiation/statement layer Indet01/Indet02):
* (Ind1) -> IUT-III.Ind1 obligation (Audit.Ind1, pending) +
  MultiradialKernel.Core.ind1 (label action) + SourceFiniteMultiradial.core
  (ind1 := ProcessionChoice.ind1Act); quotient absorption:
  generatedQuotientMap_ind1 (proved); first-triangle: Indet01.firstTriangleInd1.
* (Ind2) -> IUT-III.Ind2 obligation (pending) + Core.ind2 + Ind2AlienCopySeparation
  (ind2ShiftedCopy, secondLinkDescent bijective, zero shift = diagonal);
  quotient absorption: generatedQuotientMap_ind2 (proved); first-triangle:
  Indet01.firstTriangleInd2.
* (Ind3) -> IUT-III.Ind3 obligation (pending) + Core.ind3 (one-sided) +
  Ind3UpperSemiConstruction.outputImageFamily/_upper (proved upper-semi law,
  sharp level criterion, strict one-sidedness); first-triangle:
  Indet01.firstTriangleInd3 + firstTriangleInd3_upperSemi.
* quotient/up-to -> MultiradialKernel.Core.GenerationEqualityRelation /
  GeneratedQuotient + ConcreteFiniteModelTransport.generatedQuotient/
  generatedEqualityRelation (level characterization); up-to statement layer:
  Indet02.bpsToMultiradial (+ _ind1/_ind2 invariance, _eq_iff_level) and
  Indet02.SourceMltRepUpTo.
* BPS/0-column full poly-isomorphism -> our certified C3 convention closure
  S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds
  (polyIso in-place vs procession reindex conventions agree on pure tensors) —
  this is the tree's formal counterpart of the arbitrary indeterminate
  isomorphism gluing the input BPS to the 0-column BPS at (0,0).
* route consumer: Indet02 up-to statement feeds the route's multiradial consumer
  (S3139MultiradialProcessionConsumerActual) and the C3 convention layers
  (S3139C3ConventionRegionConsumerActual/TransferActual).

HONESTY: this is a statement/definitions layer; the production Audit obligations
IUT-III.Ind1/Ind2/Ind3 stay PENDING for the actual paper analytic carriers.  The
finite-instance quotient/upper-semi laws are proved and reused; no fake closure,
no re-proof.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.Indet03A35MappingActual

/-- A35 mapping row: (paper object, tree declaration, status). -/
structure A35MappingRow where
  paperObject : String
  treeDeclaration : String
  status : String

/-- The first-triangle indeterminacy mapping table for mainline A35. -/
def firstTriangleA35Mapping : List A35MappingRow :=
  [ { paperObject := "(Ind1) procession label/prime-strip automorphisms (IUT III 655-660)",
      treeDeclaration := "MultiradialKernel.Core.ind1 + SourceFiniteMultiradial.core (ind1 := ProcessionChoice.ind1Act); quotient: generatedQuotientMap_ind1; first-triangle: Indet01FirstTriangleIndActual.firstTriangleInd1",
      status := "finite instance PROVED (quotient absorption); paper analytic carriers PENDING (Audit.Ind1)" },
    { paperObject := "(Ind2) non-(Ind1) Z^x/O^x mu indeterminacies (IUT III 661-667)",
      treeDeclaration := "Core.ind2 + Ind2AlienCopySeparation (ind2ShiftedCopy, secondLinkDescent, zero shift = diagonal); quotient: generatedQuotientMap_ind2; first-triangle: Indet01.firstTriangleInd2",
      status := "finite instance PROVED (quotient absorption, alien-copy separation); source carriers PENDING (Audit.Ind2)" },
    { paperObject := "(Ind3) upper semi-compatibility of log-Kummer correspondences (IUT III 668-672)",
      treeDeclaration := "Core.ind3 (one-sided) + Ind3UpperSemiConstruction.outputImageFamily + outputImageFamily_upper + constructedOutputUpperSemi; first-triangle: Indet01.firstTriangleInd3/firstTriangleInd3_upperSemi",
      status := "finite instance PROVED (upper-semi law, sharp level criterion, strict one-sidedness); analytic log-Kummer carriers PENDING (Audit.Ind3)" },
    { paperObject := "BPS -> multiradial representation up to the three indeterminacies (MHYY §4 472-501; IUT III 653-679)",
      treeDeclaration := "Indet02BPSMultiradialUpToActual.bpsToMultiradial + _ind1/_ind2 + _eq_iff_level + SourceMltRepUpTo.repClass_eq_iff_level",
      status := "STATEMENT LAYER PROVED (finite instance); up-to relation = same vertical level" },
    { paperObject := "full poly-isomorphism / 0-column gluing of the input BPS (arbitrary indeterminate isomorphism)",
      treeDeclaration := "certified C3 closure: S3139C3ConventionClosureActual.sourceInd1ConventionIdentification_holds; consumer layers S3139C3ConventionRegionConsumerActual/TransferActual",
      status := "PURE-TENSOR LEVEL PROVED (first real residual closure); no volume/measure invariance claimed" } ]

end LeanFormal.IUT.XiFPaper.Indet03A35MappingActual
