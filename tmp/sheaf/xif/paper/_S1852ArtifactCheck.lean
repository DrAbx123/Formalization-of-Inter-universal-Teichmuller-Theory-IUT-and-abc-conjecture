import tmp.sheaf.xif.paper.S1852CoherentCoverActual

open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual

/-- Independent re-check from the compiled artifact: the coherent cover is
inhabited. -/
example : Nonempty CoherentCover := S1852CoherentNonempty

/-- Independent re-check of the main statement from the compiled artifact. -/
example (A : CoherentCover) :
    S1756End (CoherentCover.cover A) =
      CategoryTheory.CategoryStruct.id (S1733Model (CoherentCover.cover A)) :=
  S1852FirstMissingOnCoherent A

/-- Independent re-check: the doubled cover is excluded. -/
example (C : CoherentCover) (hC : CoherentCover.cover C = S1850DoubledCover) : False :=
  S1852DoubledCover_not_coherent C hC

#print axioms S1852FirstMissingOnCoherent
#print axioms S1852Doubled_not_coneEssSurj
#print axioms S1852Doubled_not_strong
#print axioms S1852FirstMissing_iff_S1756