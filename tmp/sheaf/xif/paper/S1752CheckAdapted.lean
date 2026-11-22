import tmp.sheaf.xif.paper.S1752ActionFundamentalActual
import tmp.sheaf.xif.paper.S1751FiniteIndexOpenActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1752ActionFundamentalActual
open LeanFormal.IUT.XiFPaper.S1751FiniteIndexOpenActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

namespace S1752CheckAdapted

-- The exact missing conditions and their equivalent forms.
#check S1752ActionForgetMissing
#check S1752ActionForgetMissing_iff_everyFiniteIndexOpen
#check S1752ActionForgetMissing_iff_S1751Target
#check S1752ActionForgetMissing_false_iff_S1751Refutation

-- The conditional literal target and its exact characterization.
#check S1752ActionForget_isFundamentalGroup
#check S1752ActionForget_isFundamentalGroup_iff_missing
#check S1737ActionForget_isFundamentalGroup
#check S1752ActionForget_isFundamentalGroup_of_everyFiniteIndexOpen
#check S1752ActionForget_isFundamentalGroup_of_S1751Target
#check S1752ActionForget_isFundamentalGroup_of_continuousMulEquiv

-- The comparison with Aut.
#check S1752ActionForgetToAutContinuous
#check S1752ActionForgetToAutContinuous_smul
#check S1752ActionForgetMissing_iff_exists_continuousMulEquiv

-- Packaging.
#check S1752ActionGaloisCategoryCertificate.of
#check S1752ActionGaloisCategoryData.of
#check S1752ActionAutCertificate
#check S1752ActionEtaleFundamentalGroup
#check S1752ActionEtaleFundamentalGroup_certified
#check S1752ActionEtaleFundamentalGroup_of_everyFiniteIndexOpen
#check S1752ActionEtaleFundamentalGroup_of_S1751Target
#check S1752ActionEtaleFundamentalGroup_of_continuousMulEquiv

-- Refutation shape from S1751's non-open subgroup input.
#check S1752ActionForgetMissing_false_of_S1751NonOpenSubgroupMissing
#check S1752ActionForget_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing
#check S1752S1720_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing

-- Unconditional separably closed and finite cases.
#check S1752ActionForgetMissing_of_isSepClosed
#check S1752ActionEtaleFundamentalGroup_of_isSepClosed
#check S1752ActionForgetMissing_of_finite
#check S1752ActionEtaleFundamentalGroup_of_finite

-- Sanity examples: the structures are inhabited unconditionally / conditionally.
example (F : Type) [Field F] : GaloisCategory (S1752ActionCategory F) :=
  inferInstance

example (F : Type) [Field F] : S1752ActionGaloisCategoryData F :=
  S1752ActionGaloisCategoryData.of F

example (F : Type) [Field F] :
    PreGaloisCategory.FiberFunctor (S1752ActionForget F) :=
  inferInstance

example (F : Type) [Field F] (h : S1752ActionForgetMissing F) :
    PreGaloisCategory.IsFundamentalGroup (S1752ActionForget F) (S1752G F) :=
  S1752ActionForget_isFundamentalGroup F h

example (F : Type) [Field F] [IsSepClosed F] :
    PreGaloisCategory.IsFundamentalGroup (S1752ActionForget F) (S1752G F) :=
  S1752ActionForget_isFundamentalGroup_of_isSepClosed F

example (F : Type) [Field F] (h : S1752ActionForgetMissing F) :
    Iut.EtaleFundamentalGroup :=
  S1752ActionEtaleFundamentalGroup F h

example (F : Type) [Field F] [IsSepClosed F] :
    Iut.EtaleFundamentalGroup :=
  S1752ActionEtaleFundamentalGroup_of_isSepClosed F

-- Axiom audit of every load-bearing declaration.
#print axioms S1752ActionGaloisCategoryCertificate.of
#print axioms S1752ActionGaloisCategoryData.of
#print axioms S1752ActionAutCertificate
#print axioms S1752ActionForgetMissing_iff_everyFiniteIndexOpen
#print axioms S1752ActionForgetMissing_iff_S1751Target
#print axioms S1752ActionForgetMissing_false_of_S1751NonOpenSubgroupMissing
#print axioms S1752ActionForget_isFundamentalGroup
#print axioms S1752ActionForget_isFundamentalGroup_iff_missing
#print axioms S1752ActionForget_isFundamentalGroup_of_everyFiniteIndexOpen
#print axioms S1752ActionForget_isFundamentalGroup_of_S1751Target
#print axioms S1752ActionForget_isFundamentalGroup_of_continuousMulEquiv
#print axioms S1737ActionForget_isFundamentalGroup
#print axioms S1752ActionForgetToAutContinuous
#print axioms S1752ActionForgetToAutContinuous_smul
#print axioms S1752ActionForgetMissing_iff_exists_continuousMulEquiv
#print axioms S1752ActionEtaleFundamentalGroup
#print axioms S1752ActionEtaleFundamentalGroup_certified
#print axioms S1752ActionEtaleFundamentalGroup_of_everyFiniteIndexOpen
#print axioms S1752ActionEtaleFundamentalGroup_of_S1751Target
#print axioms S1752ActionEtaleFundamentalGroup_of_continuousMulEquiv
#print axioms S1752ActionForget_not_isFundamentalGroup_of_not_missing
#print axioms S1752ActionForget_not_isFundamentalGroup_of_nonOpen
#print axioms S1752ActionForget_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing
#print axioms S1752S1720_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing
#print axioms S1752AllFiniteActionsContinuous_of_subsingleton
#print axioms S1752AbsoluteGalois_subsingleton_of_isSepClosed
#print axioms S1752ActionForgetMissing_of_isSepClosed
#print axioms S1752ActionForget_isFundamentalGroup_of_isSepClosed
#print axioms S1752ActionEtaleFundamentalGroup_of_isSepClosed
#print axioms S1752ActionForgetMissing_of_finite
#print axioms S1752ActionForget_isFundamentalGroup_of_finite
#print axioms S1752ActionEtaleFundamentalGroup_of_finite

end S1752CheckAdapted
