import tmp.sheaf.xif.paper.S1910FiberPurityActual
import tmp.sheaf.xif.paper.S1912EqualRankTraceRetractionActual
import tmp.sheaf.xif.paper.S1877RPrimeGaloisActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S1934RPrimeField6Lead

open LeanFormal.IUT.XiFPaper.S1848RPrimeReflectActual
open LeanFormal.IUT.XiFPaper.S1910FiberPurityActual
open LeanFormal.IUT.XiFPaper.S1912EqualRankTraceRetractionActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual
open LeanFormal.IUT.XiFPaper.S1877RPrimeGaloisActual

theorem S1934_FReflectsIsoMaps : S1848FReflectsIsoMaps :=
  S1910FReflectsIsoMaps S1912_EqualRankInclusion

theorem S1934_BCReflectsIsos : S1835BCReflectsIsos :=
  S1848BCReflectsIsos_iff.mpr S1934_FReflectsIsoMaps

theorem S1934_GaloisCategoryRPrime : GaloisCategory S1877Target :=
  S1877GaloisCategory S1934_BCReflectsIsos

#print axioms S1934_FReflectsIsoMaps
#print axioms S1934_BCReflectsIsos
#print axioms S1934_GaloisCategoryRPrime

end LeanFormal.IUT.XiFPaper.S1934RPrimeField6Lead
