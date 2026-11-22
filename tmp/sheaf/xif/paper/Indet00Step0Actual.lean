/-!
# Indet00: STEP 0 deep-search record for the first-triangle indeterminacy batch (policy §7.10)

Queries: Ind1|Ind2|Ind3|indeterminacy|multiradial representation|BPS|0-column|conjugate|SourceLogShellActionCompatibility|Sigma
Hits: LeanFormal 319 / Iut 106 / cft-port 10 / tmp/sheaf/xif/paper 1079 /
archive 3 / gap-exploration 19 / vendor 417 / corpus 219.
Sections read: coord/PRIOR-ART-INDEX.md A/F/G; corpus IUT III lines 645-700;
MHYY Formalization of IUT (2026-04) §4 (lines 472-501).
Reuse decisions (no re-proof; production files already green):
* LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind1.lean (Audit.ind1, pending),
  Ind2.lean (Audit.ind2, pending), Ind3.lean (Audit.ind3, pending) -- obligations
  referenced, status preserved (not closed by this batch).
* Ind1QuotientTransport.lean: generatedQuotientMap_ind1/_ind2 (proved; quotient
  absorbs Ind1/Ind2), quotientClass_eq_iff_level_eq, normalizedLogVolumeOnQuotient
  (+unique/injective), ConstructedOutputQuotientCompatibility,
  sourceOutputQuotientCompatibility, constructedOutputQuotientCompatibility_nonempty.
* Ind2AlienCopySeparation.lean: ind2ShiftedCopy + secondLinkDescent bijective/volume
  preserving + zero shift = diagonal (proved).
* Ind3UpperSemiConstruction.lean: outputImageFamily (+_upper, _le_iff,
  _not_le_of_lt, _value), constructedOutputUpperSemi (+==possibleImageUpperSemi iff
  level zero) (proved).
* MultiradialOutputKernel.lean: MultiradialKernel.Core (ind1/ind2/ind3 + laws),
  Ind1Step/Ind2Step/Ind3Step, GeneratedEqualityRelation, GeneratedQuotient,
  generatedQuotientMap (proved kernel).
* UpperSemi.lean: UpperSemiCorrespondence structure (singleton/comp/upper_of_comp).
* SourceFiniteMultiradial.lean: core l (finite instance), profile l (logVolume,
  possibleImage, ind1/ind2 invariance, ind3 upper, possibleImage_ind3).
* ConcreteFiniteModelTransport.lean: GeneratedEqualityRelation (concrete),
  generatedRelation_level_eq/_of_level_eq, generatedSetoid/generatedQuotient/
  generatedQuotientMap.
* MHYY §4 472-501 = first-triangle BPS->multiradial up-to statement; the tree's
  formal full-poly-isomorphism counterpart is the certified C3 convention closure.
New precedents appended to coord/PRIOR-ART-INDEX.md (section I, 2026-11-10 stepxi Indet).
Pins: registry frozen 14041; no intermediate reopen.
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.Indet00Step0Actual

/-- STEP 0 record: (query, hits, reuse/adapt decision). -/
def indetStep0Record : List (String × String × String) :=
  [ ("Ind1|Ind2|Ind3|indeterminacy|multiradial representation|BPS|0-column|conjugate|SourceLogShellActionCompatibility|Sigma",
      "LeanFormal 319 / Iut 106 / cft-port 10 / paper 1079 / archive 3 / gap 19 / vendor 417 / corpus 219",
      "reuse: MultiradialOutputKernel.Core; Ind1QuotientTransport; Ind2AlienCopySeparation; Ind3UpperSemiConstruction; UpperSemi; SourceFiniteMultiradial; ConcreteFiniteModelTransport"),
    ("IUT III corpus 653-679", "Ind1/Ind2/Ind3 exact definitions", "adapt as statement layer Indet01/Indet02"),
    ("MHYY 2026-04 §4 472-501", "BPS -> multiradial rep up to full poly-isomorphism with 0-column", "adapt; formal counterpart = certified C3 closure (reuse)"),
    ("Audit IUT-III.Ind1/Ind2/Ind3", "pending obligations (Ind1.lean:5/Ind2.lean:5/Ind3.lean:5)", "preserve status; no fake closure") ]

end LeanFormal.IUT.XiFPaper.Indet00Step0Actual
