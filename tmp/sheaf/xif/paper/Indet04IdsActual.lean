/-!
# Indet04: first-triangle indeterminacy ids (data only; registry frozen 14041, no registry edits)

Ids for lattice (INDEX) and mainline (A35 mapping).

* INDEX.FT.Indet.structure -> Indet01FirstTriangleIndActual:
  firstTriangleInd1/2/3, firstTriangleInd1_level, firstTriangleInd2_level,
  firstTriangleInd3_level, firstTriangleInd3_upperSemi, FirstTriangleIndeterminacy,
  firstTriangleIndeterminacy, firstTriangleIndCitations.
* INDEX.FT.Indet.up-to -> Indet02BPSMultiradialUpToActual:
  bpsToMultiradial, bpsToMultiradial_ind1, bpsToMultiradial_ind2,
  bpsToMultiradial_eq_iff_level, Ind3Dominates, Ind3Dominates.level_le,
  firstTriangleInd3_possibleImage_upper, SourceMltRepUpTo (+repClass,
  repClass_congr, repClass_eq_iff_level), firstTrianglePolyIsoAnchors.
* INDEX.FT.Indet.A35-mapping -> Indet03A35MappingActual.firstTriangleA35Mapping
  (A35MappingRow: paper object -> tree declaration -> status; IUT III 653-679,
  MHYY §4 472-501).
* INDEX.FT.Indet.step0 -> Indet00Step0Actual.indetStep0Record.
REUSED production obligations (statuses PRESERVED, not closed):
  LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind1.lean:5 (Audit.ind1),
  Ind2.lean:5 (Audit.ind2), Ind3.lean:5 (Audit.ind3) -- all pending.
REUSED proved assets: Ind1QuotientTransport (quotient absorption, level invariant,
descended volume), Ind2AlienCopySeparation (alien copy second link), 
Ind3UpperSemiConstruction (upper-semi family + laws), MultiradialOutputKernel
(Core/GeneratedQuotient/kernel steps), UpperSemi (correspondence kernel),
SourceFiniteMultiradial (core/profile), ConcreteFiniteModelTransport (level
characterization of the generated relation).
HONESTY: statement/definitions layer only; no fake proof; analytic log-Kummer /
D-prime-strip source carriers remain pending (Audit obligations).  The full
poly-isomorphism/0-column side is the certified C3 closure (pure-tensor level).
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.Indet04IdsActual

/-- First-triangle indeterminacy ids: (index id, declarations, file). -/
def indetIds : List (String × String × String) :=
  [ ("INDEX.FT.Indet.structure",
      "firstTriangleInd1, firstTriangleInd2, firstTriangleInd3, firstTriangleInd1_level, firstTriangleInd2_level, firstTriangleInd3_level, firstTriangleInd3_upperSemi, FirstTriangleIndeterminacy, firstTriangleIndeterminacy",
      "Indet01FirstTriangleIndActual.lean"),
    ("INDEX.FT.Indet.up-to",
      "bpsToMultiradial, bpsToMultiradial_ind1, bpsToMultiradial_ind2, bpsToMultiradial_eq_iff_level, Ind3Dominates, firstTriangleInd3_possibleImage_upper, SourceMltRepUpTo, repClass_congr, repClass_eq_iff_level, firstTrianglePolyIsoAnchors",
      "Indet02BPSMultiradialUpToActual.lean"),
    ("INDEX.FT.Indet.A35-mapping", "firstTriangleA35Mapping",
      "Indet03A35MappingActual.lean"),
    ("INDEX.FT.Indet.step0", "indetStep0Record", "Indet00Step0Actual.lean") ]

end LeanFormal.IUT.XiFPaper.Indet04IdsActual
