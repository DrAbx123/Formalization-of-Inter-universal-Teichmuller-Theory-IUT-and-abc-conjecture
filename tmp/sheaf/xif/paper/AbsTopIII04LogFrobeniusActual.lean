import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: Def 3.1(iv)|log-Frobenius|SourceLogShellCodomainClosure|SourceLogShellCarrier -> hits LeanFormal/IUT/IUTII/Kummer/SourceLogShellCodomainClosure.lean:60-146, SourceLogShellCarrier.lean:176/182, SourceLocalLogShellDatum.lean:32 -> REUSE (dictionary + elementary landing; no re-proof).

# [AbsTopIII] 04: Def 3.1 (iv) log-Frobenius - concrete dictionary (C)

Corpus: papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt
lines 3424-3470 (Def 3.1(iv)): the log-Frobenius functor log_{TF,TF} sending
(k, Pi_k-action) to (k^~, Pi_k-action), isomorphic to the identity functor; and
the functors lambda^x, lambda^{x,pf}.  Concrete tree dictionary: the actual
log-shell landing/normalization facts (SourceLogShellCarrier:176/182) and the
p* = logShellScale identification (SourceLocalLogShellDatum:32); the COD0MAIN
closure file records the log(O^{x,p}) subset 1+p^m shape
(SourceLogShellCodomainClosure:60-146).  Functor construction itself is NOT
formalized here (no claim).
-/

namespace LeanFormal.IUT.XiFPaper.AbsTopIII04LogFrobeniusActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT

/-- The source factor p* equals the actual log-shell scale (log-Frobenius
dictionary, Def 3.1(iv); reuse SourceLocalLogShellDatum:32). -/
theorem absTopIII_logFrobenius_scale {p : Nat} (hp : p.Prime) :
    sourceLogShellStar p = logShellScale p :=
  sourceLogShellStar_eq_logShellScale hp

/-- The log map of invariant units lands in the concrete log-shell
(the elementary O^{x,p} -> log-shell landing underlying Def 3.1(iv); reuse
SourceLogShellCarrier:182). -/
theorem absTopIII_logFrobenius_unit_landing (D : SourceLogShellDatum)
    {u : D.Units} (hu : u ∈ D.invariants) :
    (D.logMap u).toAdd ∈ D.logShell :=
  invariant_unitLog_mem_logShell D hu

/-- Def 3.1(iv) dictionary rows: (item, corpus, tree anchor, status). -/
def def31IVRows : List (String × String × String × String) :=
  [ ("log_{TF,TF} : CMLF_TF -> CMLF_TF", "corpus 3424-3436",
      "none (functor construction not formalized)", "NOT formalized (no claim)")
  , ("log_{TF,T} for T in {TLG,TCG,TM}", "corpus 3441-3446",
      "none (functor construction not formalized)", "NOT formalized (no claim)")
  , ("lambda^x, lambda^{x,pf}", "corpus 3447-3470",
      "none (functor construction not formalized)", "NOT formalized (no claim)")
  , ("p* = logShellScale (concrete)", "Def 3.1(i)/(iv) p*",
      "SourceLocalLogShellDatum:32 sourceLogShellStar_eq_logShellScale", "REUSED")
  , ("O^{x,p} landing in log-shell (concrete)", "Def 3.1(iv) elementary content",
      "SourceLogShellCarrier:182 invariant_unitLog_mem_logShell;
        SourceLogShellCodomainClosure:60-146", "REUSED (elementary)") ]

/-- The Def 3.1(iv) dictionary has five rows. -/
theorem def31IVRows_length : def31IVRows.length = 5 := rfl

#check absTopIII_logFrobenius_scale
#check absTopIII_logFrobenius_unit_landing
#check def31IVRows
#check def31IVRows_length

end LeanFormal.IUT.XiFPaper.AbsTopIII04LogFrobeniusActual