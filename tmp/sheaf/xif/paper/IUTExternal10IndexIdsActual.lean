import LeanFormal.IUT.Audit.Status

/-! # IUTExternal10: INDEX ids for IUT external objects (Lead DIRECTIVE; frozen 14041)

Source: coord/IUT-EXTERNAL-OBJECTS-INVENTORY.md (mainline, 2026-11-11);
MHYY Formalization of IUT (2026-04) Stage 4 corpus lines 121-124 + bibliography
627-690.  ids INDEX.IUTEXTERNAL.<ref> with planned alias INDEX.EXT.<ref>.<nn>.
Classes: A definable/elementary, B paper-proved formalization target, C convention/
data, D genuinely deep named input.  No registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.IUTExternal10IndexIdsActual

/-- IUT external references: (ref, paper, IUT use, existing assets, class, owner). -/
def IUTExternalIds : List (String × String × String × String × String × String) :=
  [ ("INDEX.IUTEXTERNAL.pGC", "Local Pro-p Anabelian Geometry of Curves (1997)", "IUT I/II pro-p anabelian reconstruction", "LeanFormal/IUT/IUTI,IUTII partial; pro-p groups", "B (some A)", "stage4"),
    ("INDEX.IUTEXTERNAL.GeoAn", "Geometry of Anabelioids (2004)", "IUT I anabelioid/fundamental groupoid machinery", "IUTI partial; IUTIII SourceCarrier abstractions", "B", "stage4"),
    ("INDEX.IUTEXTERNAL.AbsAnb", "Absolute Anabelian Geometry of Hyperbolic Curves (2004)", "IUT I absolute anabelian reconstruction; III", "ABCBridge Geometry hyperbolic-curve place data", "B", "stage4"),
    ("INDEX.IUTEXTERNAL.NCBel", "Noncritical Belyi Maps (2004)", "GenEll Thm 2.1 (ii)=>(i); IUT IV section2", "stage4 Mzk1 Thm2.5/Cor3.2 statement; GeometricCore = only deep residual", "B + D residual", "stage4 statement / mainline wiring"),
    ("INDEX.IUTEXTERNAL.AbSc", "Galois Sections in Absolute Anabelian Geometry (2005)", "IUT II/III Galois-section rigidity", "IUTII partial", "B", "stage4"),
    ("INDEX.IUTEXTERNAL.SemiAn", "Semi-graphs of Anabelioids (2010)", "IUT I/II combinatorial anabelian", "IUTIII graphs/edge data", "B", "stage4"),
    ("INDEX.IUTEXTERNAL.QuCnf", "Conformal/quasiconformal categorical representation (2010)", "IUT I/II geometricity of anabelioids", "none dedicated", "B", "stage4"),
    ("INDEX.IUTEXTERNAL.CbGC", "Combinatorial Grothendieck Conjecture (2007)", "IUT I/II combinatorial reconstruction", "IUTIII combinatorial pieces", "B", "stage4"),
    ("INDEX.IUTEXTERNAL.Config", "Configuration Spaces I,II", "IUT I/II configuration-space anabelian geometry", "none dedicated", "B", "stage4"),
    ("INDEX.IUTEXTERNAL.FrdI-II", "Frobenioids I/II (2004)", "IUT I Frobenioid formalism", "IUTIV ArithmeticDivisorDegree function layer only; no Frobenioid formalization", "B (large)", "stage4"),
    ("INDEX.IUTEXTERNAL.EtTh", "The Etale Theta Function and its Frobenioid-theoretic Manifestations (2009)", "IUT I/II/III theta function; theta-pilot", "Theta-side SourceDefinition31Data/S3131/S3132; canonical rooted Q_C/H_C", "B (D in theta section)", "stepxi"),
    ("INDEX.IUTEXTERNAL.GenEll", "Arithmetic Elliptic Curves in General Position (2010)", "IUT IV section2 (Thm 1.10 + GenEll => ABC)", "GenEll00-13 P0 set; (i)=>(ii) proved; (ii)=>(i) paper-input", "B", "mainline/abc/stage4"),
    ("INDEX.IUTEXTERNAL.NodNon", "Combinatorial Anabelian Geometry of Nodally Nondegenerate Curves (2010)", "IUT I combinatorial anabelian", "none dedicated", "B", "stage4"),
    ("INDEX.IUTEXTERNAL.AbsTopI-III", "Topics in Absolute Anabelian Geometry I-III (2013-2015)", "IUT III absolute anabelian/log-shell; IV", "AbsTopIII 01-09 citable (concrete p-adic side); 05 DEEP named", "B + D", "hull/stage4"),
    ("INDEX.IUTEXTERNAL.ExpEst", "Explicit Estimates (IUTchIV Stage 5; Fesenko-Hoshi-Minamide-Porowski)", "IUT IV numerical/quantitative bounds", "IUTIV Estimates/* (Section1/Section2/StepV*, ElementaryEstimates e1-e6)", "B", "abc/stage4") ]

theorem IUTExternalIds_length : IUTExternalIds.length = 15 := rfl

/-- Planned per-file alias ids INDEX.EXT.<ref>.<nn>. -/
def IUTExternalFileAliases : List (String × String) :=
  [ ("INDEX.EXT.pGC.01", "IUTExternalPGC01StatementActual (planned; stage4)"),
    ("INDEX.EXT.GeoAn.01", "IUTExternalGeoAn01BasicActual (planned; stage4)"),
    ("INDEX.EXT.AbsAnb.01", "IUTExternalAbsAnb01StatementActual (planned; stage4)"),
    ("INDEX.EXT.NCBel.01", "Mzk1 statement hook into GenEll05 Theorem21ReductionInputs.mzk1NoncriticalBelyi (stage4/mainline)"),
    ("INDEX.EXT.AbSc.01", "IUTExternalAbSc01StatementActual (planned; stage4)"),
    ("INDEX.EXT.SemiAn.01", "IUTExternalSemiAn01BasicActual (planned; stage4)"),
    ("INDEX.EXT.QuCnf.01", "IUTExternalQuCnf01StatementActual (planned; stage4)"),
    ("INDEX.EXT.CbGC.01", "IUTExternalCbGC01StatementActual (planned; stage4)"),
    ("INDEX.EXT.Config.01", "IUTExternalConfig01BasicActual (planned; stage4)"),
    ("INDEX.EXT.FrdI-II.01", "IUTExternalFrdI01BasicActual (planned; stage4)"),
    ("INDEX.EXT.EtTh.01", "IUTExternalEtTh01StatementActual (planned; stepxi)"),
    ("INDEX.EXT.GenEll.01", "GenEll05b wiring map current (mainline)"),
    ("INDEX.EXT.NodNon.01", "IUTExternalNodNon01StatementActual (planned; stage4)"),
    ("INDEX.EXT.AbsTopI-III.01", "AbsTopIII07/08/09 integration + 05 deep named (hull)"),
    ("INDEX.EXT.ExpEst.01", "IUTExternalExpEst01StatementActual (planned; abc/stage4)") ]

theorem IUTExternalFileAliases_length : IUTExternalFileAliases.length = 15 := rfl

end LeanFormal.IUT.XiFPaper.IUTExternal10IndexIdsActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: IUT external objects ids. -/
def IUTExternalIdsRecord : Obligation :=
  { id := "INDEX.IUTEXTERNAL.ids"
    source := "coord/IUT-EXTERNAL-OBJECTS-INVENTORY.md; MHYY Formalization of IUT (2026-04) Stage 4 corpus 121-124; bibliography 627-690"
    status := VerificationStatus.interface
    note := "IUT EXTERNAL OBJECTS ids (15 refs): pGC, GeoAn, AbsAnb, NCBel, AbSc, SemiAn, QuCnf, CbGC, Config, FrdI-II, EtTh, GenEll, NodNon, AbsTopI-III, ExpEst, with paper/IUT-use/existing-assets/class A-D/owner. Plain ids INDEX.IUTEXTERNAL.* + planned alias INDEX.EXT.<ref>.<nn> per mainline; owners per inventory (stage4 most, stepxi EtTh, hull AbsTopIII, abc ExpEst/GenEll section1, mainline GenEll wiring/NCBel wiring). Deep inputs named, never faked. No registry edits (frozen 14041)."
    dependsOn := ["IUTExternal10IndexIdsActual", "IUTExternal11CitationRowsActual", "IUTExternal12AssetsMapActual"] }

end LeanFormal.IUT.Audit
