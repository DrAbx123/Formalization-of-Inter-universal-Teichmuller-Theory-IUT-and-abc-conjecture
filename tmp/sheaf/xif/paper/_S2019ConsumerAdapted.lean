import tmp.sheaf.xif.paper.S2019RebasedRootStackActual

/-! Consumer check for the S2019 olean: the rebased root stack datum and its
results are importable, and their axiom footprint is the allowed one. -/

open LeanFormal.IUT.XiFPaper.S2019RebasedRootStackActual
open LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual
open LeanFormal.IUT.XiFPaper.S2001LiftCommutesActual
open LeanFormal.IUT.XiFPaper.S1994KSideCovers
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT

universe u

#check @S2019IsoCommaDescent
#check @S2019FullIsStack
#check @S2019RootIsStack_iff_fullDescentAll
#check @S2019RootFullDescentAll_iff_effDescent
#check @S2019FirstMissing
#check @S2019CorrectedRootStackDatum
#check @S2019CorrectedRootStackMissing_iff
#check @S2019CorrectedRootStackMissing_implies_S1994
#check @S2019RebasedRootStackRoute
#check @S2019RebasedRootStackRoute_uniq

example {K : Type u} [Field K] {l : PrimeGeFive} (D : S2019CorrectedRootStackDatum K l) :
    S1997RootStackificationMissing K l := ⟨D.toRecorded⟩

example {K : Type u} [Field K] {l : PrimeGeFive} :
    S2019FirstMissing (K := K) (l := l) ↔ S1997RootEffectiveDescent K l.value :=
  S2019FirstMissing_iff_effDescent

#print axioms S2019CorrectedRootStackMissing_iff
#print axioms S2019CorrectedRootStackMissing_implies_S1994
#print axioms S2019RebasedRootStackRoute_iff
