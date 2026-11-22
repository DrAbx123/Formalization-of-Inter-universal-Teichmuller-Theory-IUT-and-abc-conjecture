import tmp.sheaf.xif.paper.Mzk1IVThm110Actual
import tmp.sheaf.xif.paper.Mzk1P6ActualProducersActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.Mzk1P6ActualProducersActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual

namespace LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual

/-- The explicit actual source dictionary consumed by the Thm 110 display. -/
structure P6DisplaySourceData where
  l : PrimeGeFive
  l_ge_seven : 7 ≤ l.value
  dmod : Nat
  dmod_ge_one : 1 ≤ dmod
  dFpd : Real
  fFpd : Real
  dFpd_ge_one : 1 ≤ dFpd
  fFpd_ge_one : 1 ≤ fFpd
  eStar : Real
  etaPrm : Real
  logQ : Real
  logQ_pos : 0 < logQ
  eta_nonneg : 0 ≤ eStar * (l.value : Real) + etaPrm

/-- The actual `ActualThm110Data` assembled from the explicit dictionary. -/
def P6DisplaySourceData.toActualData (D : P6DisplaySourceData) : ActualThm110Data where
  l := D.l
  l_ge_seven := D.l_ge_seven
  dmod := D.dmod
  dmod_ge_one := D.dmod_ge_one
  dFpd := D.dFpd
  fFpd := D.fFpd
  dFpd_ge_one := D.dFpd_ge_one
  fFpd_ge_one := D.fFpd_ge_one
  eStar := D.eStar
  etaPrm := D.etaPrm
  logQ := D.logQ
  logQ_pos := D.logQ_pos
  eta_nonneg := D.eta_nonneg

/-- The actual Thm 110 display terms. -/
def P6DisplaySourceData.toTerms (D : P6DisplaySourceData) : Thm110DisplayTerms :=
  D.toActualData.toTerms

@[simp] theorem P6DisplaySourceData.toTerms_l (D : P6DisplaySourceData) :
    D.toTerms.l = (D.l.value : Real) := rfl

@[simp] theorem P6DisplaySourceData.toTerms_dmod (D : P6DisplaySourceData) :
    D.toTerms.dmod = (D.dmod : Real) := rfl

@[simp] theorem P6DisplaySourceData.toTerms_logQ (D : P6DisplaySourceData) :
    D.toTerms.logQ = D.logQ := rfl

@[simp] theorem P6DisplaySourceData.toTerms_eStar (D : P6DisplaySourceData) :
    D.toTerms.eStar = D.eStar := rfl

@[simp] theorem P6DisplaySourceData.toTerms_etaPrm (D : P6DisplaySourceData) :
    D.toTerms.etaPrm = D.etaPrm := rfl

/-- Actual display chain: the explicit source dictionary plus the Cor 3.12
input yields the Thm 1.10 final display. -/
theorem p6_display_chain
    (D : P6DisplaySourceData)
    (hCor312 : thm110Lhs D.toTerms ≤ thm110Mid D.toTerms + thm110Cor312Gap D.toTerms) :
    thm110Lhs D.toTerms ≤ thm110Rhs D.toTerms :=
  thm110_display_of_hCor312 D.toActualData hCor312

#print axioms p6_display_chain

end LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
end