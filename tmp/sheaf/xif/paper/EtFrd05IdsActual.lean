/-!
# EtFrd05: EtTh / Frobenioid ids (data only; registry frozen 14041, no registry edits)

* INDEX.ETTH.statement -> EtTh01StatementActual: EtaleThetaKummerClass,
  MonoThetaEnvironment, EtaleThetaObject, EtThPaperComponents.
* INDEX.ETTH.deep-inputs -> EtTh02DeepInputsActual: EtThDeepInput, etThDeepInputs
  (10 named class-B inputs, proved := false), etThDeepInputs_all_unproved,
  etThDeepInputs_length.
* INDEX.ETTH.tree-reuse -> EtTh03TreeReuseActual.etThTreeReuse.
* INDEX.ETTH.route-wiring -> EtTh04RouteWiringActual.etThRouteWiring.
* INDEX.FRD.statement -> Frd01StatementActual: DivisorialMonoidData,
  ModelFrobenioidData, FrobeniusActionData, FrobenioidObjectLayer, FrdPaperComponents.
* INDEX.FRD.reuse -> Frd02ReuseAuditActual.frdReuseAudit.
* INDEX.ETTH.FRD.step0 -> EtFrd00Step0Actual.etFrdStep0Record.
Chosen EtTh file names reported to mainline for the external-object inventory:
EtTh01StatementActual / EtTh02DeepInputsActual / EtTh03TreeReuseActual /
EtTh04RouteWiringActual (and Frobenioid: Frd01StatementActual / Frd02ReuseAuditActual).
Reused tree assets: EtaleThetaQuotient (A), ConcreteSourceEtaleThetaBridge:44 (A),
ConcreteSourceFrobenioidBridge (A), Iut.Foundations.SourceModelFrobenioid* (A),
Example36* Frobenius assets (A/B), theta packet SourceDefinition31Data, S3131/S3132
canonical rooted, GenEll10 H6 (interface-level), Indet01-03 A35, C3 closure.
Honest: deep [EtTh] theta results are class-B D-inputs (proved := false); [FrdI]/[FrdII]
category-theoreticity theorems class B; nothing closed unconditionally.
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.EtFrd05IdsActual

/-- EtTh / Frobenioid ids: (index id, declarations, file). -/
def etFrdIds : List (String × String × String) :=
  [ ("INDEX.ETTH.statement", "EtaleThetaKummerClass, MonoThetaEnvironment, EtaleThetaObject, EtThPaperComponents", "EtTh01StatementActual.lean"),
    ("INDEX.ETTH.deep-inputs", "EtThDeepInput, etThDeepInputs, etThDeepInputs_all_unproved, etThDeepInputs_length", "EtTh02DeepInputsActual.lean"),
    ("INDEX.ETTH.tree-reuse", "etThTreeReuse", "EtTh03TreeReuseActual.lean"),
    ("INDEX.ETTH.route-wiring", "etThRouteWiring", "EtTh04RouteWiringActual.lean"),
    ("INDEX.FRD.statement", "DivisorialMonoidData, ModelFrobenioidData, FrobeniusActionData, FrobenioidObjectLayer, FrdPaperComponents", "Frd01StatementActual.lean"),
    ("INDEX.FRD.reuse", "frdReuseAudit", "Frd02ReuseAuditActual.lean"),
    ("INDEX.ETTH.FRD.step0", "etFrdStep0Record", "EtFrd00Step0Actual.lean") ]

end LeanFormal.IUT.XiFPaper.EtFrd05IdsActual
