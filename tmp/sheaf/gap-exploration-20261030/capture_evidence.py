"""Capture the bounded exploratory review; never runs Lean or mutates source code."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone

sys.stdout.reconfigure(encoding="utf-8")
ROOT = Path("D:/lean")
OUT = ROOT / "tmp/sheaf/gap-exploration-20261030"
REPORT = ROOT / "coord/reports/gap-exploration-20261030.md"
NODE = ROOT / "dag/nodes/gap-exploration-20261030.json"


def dump(path, obj):
    path.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def append_once(path, marker, body):
    prior = path.read_text(encoding="utf-8-sig")
    if marker not in prior:
        with path.open("a", encoding="utf-8", newline="") as stream:
            stream.write("\n\n" + body.rstrip() + "\n")


report = REPORT.read_text(encoding="utf-8")
report = report.replace("/D:/lean/", "D:/lean/")
REPORT.write_text(report, encoding="utf-8", newline="\n")

node = {
    "schema": "iut-sheaf-node/v1",
    "id": "gap-exploration-20261030",
    "kind": "statement",
    "root_role": None,
    "owner": "root-current-chat-single-thread",
    "statement": (
        "For one qualifying original initial Theta datum T, identify the same-source q, "
        "specified K-place/root, IQ tensor packet, Kummer/Ind images, hull and normalized "
        "readout needed by xi-f; establish a source-faithful route without extra conclusion "
        "hypotheses. This node records exploratory obligations, not a proved theorem."
    ),
    "source": "IUT I Example 3.2(iv), p.71; IUT III Corollary 3.12, pp.173-174, xi-d--xi-f pp.183-184; current versioned local sources",
    "lean": {
        "file": None,
        "declaration": None,
        "type": None,
        "status": "not_formalized_exploratory_review_only",
    },
    "statement_dependencies": ["xif-source-construction"],
    "proof_dependencies": [],
    "edge_evidence": [{
        "from": "gap-exploration-20261030",
        "to": "xif-source-construction",
        "kind": "statement",
        "basis": "The exploratory statement concerns the existing xi-f source-construction consumer; no proof dependence or completion is asserted.",
        "status": "observed_source",
    }],
    "dependencies_complete": False,
    "natural_language_proof": None,
    "mathlib_search": {
        "status": "bounded_local_primary_source_search",
        "records": ["tmp/sheaf/gap-exploration-20261030/search-results.json"],
        "limits": "Searches identify reusable leaves and inspected candidates, not absence across all mathematics.",
    },
    "stage1": "open",
    "proof_status": "open",
    "semantic_status": "partial_alignment_with_specific_mismatches",
    "locked": False,
    "candidate_connections": [
        "S438/S605/S618 -> source-selected K-place q/root",
        "SourceLogShellActualTensorSpan + FinitePadicTensorLogShellRealization -> source packet realization",
        "NormalizedHaarTransport + degree transport -> source normalized readout",
        "S1116 + S1124 + S865/S284 + FinitePadicHaarScaling -> E character-norm formula",
    ],
    "gaps": [
        "Same-source F/K place and Tate q comparison, plus root descent in the specified K completion",
        "Actual capsule/tuple indices and source IQ realization, not Unit/Real models or arbitrary functions",
        "Kummer maps and full source action/evaluation compatibility, not inhabited Prop-only records",
        "Source hull/image-family control with correct measure, positive finite mass, reference, weights and determinant",
        "Correct norm/degree formulas; no forced default=spectral coefficient identity",
        "Same-C q-mark/output/readout bridge to xi-f",
        "Actual arithmetic epsilon-comparison input for the final conditional ABC bridge",
    ],
    "evidence": [
        "coord/reports/gap-exploration-20261030.md",
        "tmp/sheaf/gap-exploration-20261030/evidence.json",
    ],
    "statement_compiles": "not_run",
    "proof_body_checked": "not_run",
    "kernel_closed": "not_run",
    "target_accepted": False,
    "independent_review": "not_run_single_thread",
    "comparator": "not_run",
    "project_build": "not_run",
    "next_action": "Reuse S438/S605/S618 to instantiate the q comparison diagram at the source-selected K-place; isolate remaining Tate/torsion root-descent obligations.",
}
dump(NODE, node)

marker = "2026-10-30 — gap-exploration-20261030"
append_once(
    ROOT / "AUDIT_LEDGER.md", marker,
    """## 2026-10-30 — gap-exploration-20261030：单线程源对象与复用探索

任务/消费者：按用户要求单线程探索当前 gap、备选路线、原文目标对象对齐；沿 Q-BRIDGE/xif-source-construction，未重新审查全仓或 L0.3。报告：[完整报告](coord/reports/gap-exploration-20261030.md)；证据：[冻结清单](tmp/sheaf/gap-exploration-20261030/evidence.json)。

更正（保留原记录及有效数学）：
- S342 的无根结论仅适用于 qVFamily 所在 F 侧所选完备化。原文 I p.71 指定 K 侧完备化中的 2l 次根，不能泛化成“所有原文完备化都无根”。S438 已给 K 侧参数与 order_K=e*order_F；S605/S618 已列指定地方/参数比较。S467 的任意 e,m 反例未使用完整源条件；根下降仍 open。
- S1148 的多因子张量供体盘点不完整：SourceLogShellActualTensorSpan、FinitePadicTensorFieldDecomposition、FinitePadicTensorLogShellRealization/Transport 已存在。有限张量 hull 历史批次 exit 0；IQ span 单模块 Built 的另一批次整体 exit 1，不能混报。它们仍需源 capsule/index/Kummer/像族实例化。
- S1115 所说 E 层 DVR/单位因子未建已被 S1116/S1124 当前证明体更新；S1139 仍以最终 FactorNormPow 为输入。可复用 S865/S284 与通用 p-Haar 缩放走非循环路线，尚未本轮实现或编译。
- S1122/S1146 的任意或固定 Gaussian Theta 与独立 q 混配反例不反驳原文同一数据比较；复用 S1129 已有更正。

当前文本发现：S1145 的 GlobalKummerTensorPacketIso 只存 Prop，record 非空不证明字段；S1148 的 transport 只需函数非空，可由常零满足。S1142 的 Ind1 当前为同一等价的来回 image，集合返回 base。生产 norm 公式遗漏零分支；10-18 历史版部分修复但全 x 公式与 nu_add_ge_min 仍有零/相消反例。以上为明确对象/接口问题，不是对所有可行路线的否定。

测度边界：真有限维子空间嵌入的 ambient Haar 与原空间 pushforward 一般不同；具体扩张次数及形式化未在本轮验证。NormalizedHaarTransport 的实际同构/相对读数路线和 S1086 已有 pushforward 分支值得复用，但源读数身份仍须证明。

状态：statement_compiles=not_run；proof_body_checked=not_run；kernel_closed=not_run；target_accepted=false。未运行 Lean/Project/comparator/axiom probe/独立审查。只写报告、证据、新探索节点与本次追加记录，未改 Lean 或活动 xif 节点。

下一步：复用 S438/S605/S618，在原文 section 指定 K-place 实例化 q 比较图，避免强证独立任意地方选择相等；明确 Tate/torsion 到指定完备化根的剩余箭头。"""
)

append_once(
    ROOT / "coord/STATE.md", marker,
    """## 2026-10-30 — gap-exploration-20261030：探索报告完成，数学链仍 open

- 用户限定本 chat 单线程；root 已完成 [gap/备选路线/源对象报告](reports/gap-exploration-20261030.md)。报告状态不能解释为 IUT/xi-f 证明完成。
- 新证据：F 侧 S342 不排除原文 K 侧根；S438/S605/S618 已有 K-side 参数链。实际有限 Qp tensor/field-product/log-shell hull/normalized Haar transport 供体已经存在，应复用；完整源索引、Kummer/Ind 与读数接入仍未闭合。
- 当前接口检查：S1145 Prop-only record、S1148 任意函数 gate、S1142 Ind1 来回 image 均不能支持完整原文对象对齐。通用 norm 候选含零值反例；E DVR/unit-factor 已有证明体，最终 character formula 尚待非循环推导。
- 独立节点 dag/nodes/gap-exploration-20261030.json；证据 tmp/sheaf/gap-exploration-20261030/evidence.json。既有活动 xif 节点与 Lean 未改。
- statement_compiles/proof_body_checked/kernel_closed 均 not_run；target_accepted=false；无 Project/comparator/独立审查。历史构建证据在报告内限定范围。
- 可执行下一步：在源指定 K-place 上复用 S438 的 q map/order 公式并核对 S605 的地方/参数/uniformization 比较，登记准确根下降义务。"""
)

append_once(
    ROOT / "coord/queue.md", marker,
    """## 2026-10-30 — gap-exploration-20261030：Q-BRIDGE 探索增补

- [report complete; proof open] 单线程探索报告见 [gap-exploration-20261030](reports/gap-exploration-20261030.md)。不自动唤醒任何历史任务，不将本 chat 单线程要求传播成项目限制。
- 继续 Q-BRIDGE 前先消费报告的复用表：S438/S605/S618、ActualTensorSpan、FinitePadicTensorLogShellRealization/Transport、NormalizedHaarTransport、S1116/S1124/S865。不要再次把这些整个登记成“无实现”。
- [next candidate; unclaimed] 一个源指定 K-place 的 q 比较图包：固定 T,b、源 section、comap、completionMap、q/Tate/order/norm 兼容性；避免强证两个独立 arbitrary choices 相等。根下降未得到时保持准确具名 gap。
- 停止错误接口扩增：Prop record 非空、常零 transport、默认/normalized 系数硬相等、真子空间 ambient=pushforward，均不计源闭合。S1122 数值反例范围沿用 S1129 更正。
- 本次仅文档/证据；Lean/Project/comparator/公理检查未运行，target_accepted=false。"""
)

append_once(
    OUT / "TASK.md", "交付记录：2026-10-30",
    """## 交付记录：2026-10-30

- 完整报告：coord/reports/gap-exploration-20261030.md；独立探索节点：dag/nodes/gap-exploration-20261030.json。
- 主要结果：确认真实张量/hull/Haar 和 K-side 运输供体；限缩 F-side 无根与任意 Theta 反例；识别 Prop-only gate、测度/范数混用；给出六条带具体供体及停止条件的路线。
- 编译与验收：statement_compiles=not_run，proof_body_checked=not_run，kernel_closed=not_run，target_accepted=false；独立审查/comparator/Project 均未运行。
- 未改既有 Lean 文件、活动 xif 节点和构建调度；STATE/queue/AUDIT 仅追加。供体未因报告而获本版本内核认证。
- 一个下一步：源 section 指定 K-place 上的 q 比较图，复用 S438/S605/S618，明确 torsion 到根下降的剩余义务。
- 机械检查输出：verification.json；检索记录：search-results.json；源文件 SHA256 与副本：evidence.json / snapshots。
"""
)

queries = [
    {
        "id": "k_side_existing_and_consumers",
        "args": ["rg", "-n", "--glob", "*.lean",
                 "KSideTwoLRootData|qVFamilyK\\b|KLocalRamificationDivisible|kernel_field_identification",
                 "tmp/sheaf/xif/paper", "LeanFormal/IUT/IUTI/InitialTheta"],
    },
    {
        "id": "tensor_hull_existing",
        "args": ["rg", "-n", "--glob", "*.lean",
                 "exists_realized_tensorLogShell_hull|exists_finiteNormedFieldProduct_piTensor|sourceLogShellActualIntegralTensors_span_eq_top|tensorLogShellHull_decomposition_change",
                 "LeanFormal/IUT/Foundations/LocalFields", "LeanFormal/IUT/IUTII/Kummer"],
    },
    {
        "id": "measure_existing",
        "args": ["rg", "-n", "--glob", "*.lean",
                 "relative_log_mass_image_eq|measure_prime_smul_finiteDimensional|s1086PerB_pushforward|s1124UnitFactorOne_actual|rootHaarFactor_normPow_actual",
                 "LeanFormal/IUT/Foundations/LocalFields", "tmp/sheaf/xif/paper"],
    },
    {
        "id": "norm_candidates_production_and_history",
        "args": ["rg", "-n", "--glob", "*.lean",
                 "canonicalAbsValue|generalNormalizedNormFormula|spectralNorm_eq_formula|nu_add_ge_min",
                 "LeanFormal/IUT/Foundations/AlgebraicGeometry/GeneralNormalizedNormBySpectralUniqueness.lean",
                 "tmp/n8-20261018/general/GeneralNormalizedNormBySpectralUniqueness.lean"],
    },
    {
        "id": "mathlib_norm_primitives",
        "args": ["rg", "-n",
                 "spectralNorm_unique_field_norm_ext|spectralNorm_zero|def log|lemma log_zero",
                 ".lake/packages/mathlib/Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean",
                 ".lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/WithZero.lean"],
    },
    {
        "id": "latest_interface_shapes",
        "args": ["rg", "-n", "Prop|Nonempty|paperInd1Image|ind3Transfer|toPaper",
                 "tmp/sheaf/xif/paper/Theorem311KummerPacketIsoGapActual.lean",
                 "tmp/sheaf/xif/paper/S1142IndPaperCarrierActual.lean",
                 "tmp/sheaf/xif/paper/S1144QvPaperQPilotObjectActual.lean",
                 "tmp/sheaf/xif/paper/S1145GlobalKummerTensorPacketIsoActual.lean",
                 "tmp/sheaf/xif/paper/S1148MultiradialCarrierAuditActual.lean"],
    },
    {
        "id": "historical_tensor_build_evidence",
        "args": ["rg", "-n",
                 "SourceLogShellActualTensorSpan|FinitePadicTensorLogShellRealization|Build completed|error:|cmd exit",
                 "tmp/source-local-log-20261017/build-finite-tensor-log-realization-3.log",
                 "tmp/single-agent-iq-carrier-20261017/build-tensor-2.log"],
    },
    {
        "id": "abc_boundary",
        "args": ["rg", "-n",
                 "structure Cor312ToABCBridgeInterface|epsilonComparison|theorem cor312ToABCBridge_abcConjecture|nonempty_iff_abcConjecture",
                 "LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean"],
    },
]
search_results = []
for query in queries:
    result = subprocess.run(query["args"], cwd=ROOT, capture_output=True,
                            encoding="utf-8", errors="replace")
    search_results.append({
        **query, "recorded_at_utc": now(), "exit_code": result.returncode,
        "stdout": result.stdout, "stderr": result.stderr,
        "interpretation_limit": "Matches are leads, followed by source reading; no-match would not prove global absence.",
    })
dump(OUT / "search-results.json", search_results)

links = re.findall(r"\]\((?:<)?(D:/lean/[^)>]+)(?:>)?\)", report)
link_records = []
source_paths = set()
own_outputs = {
    REPORT, NODE, OUT / "evidence.json", OUT / "verification.json",
    OUT / "TASK.md", OUT / "search-results.json",
}
for raw in links:
    match = re.search(r":(\d+)$", raw)
    lineno = int(match.group(1)) if match else None
    filename = re.sub(r":\d+$", "", raw)
    path = Path(filename)
    item = {"path": str(path), "line": lineno, "exists": path.exists()}
    if path.exists() and lineno is not None:
        count = len(path.read_text(encoding="utf-8-sig").splitlines())
        item["line_in_bounds"] = 1 <= lineno <= count
    link_records.append(item)
    if path not in own_outputs:
        source_paths.add(path)

for rel in [
    "AGENTS.md", "SHEAF.md", "GOAL.md", "SETUP.md", "coord/TASK_TEMPLATE.md",
    "coord/targets-review.md", "coord/STATE.md", "coord/queue.md", "AUDIT_LEDGER.md",
    "dag/README.md",
]:
    source_paths.add(ROOT / rel)

entries = []
for path in sorted(source_paths, key=lambda p: str(p).lower()):
    if not path.exists():
        entries.append({"path": str(path), "exists": False})
        continue
    rel = path.relative_to(ROOT)
    frozen = OUT / "snapshots" / rel
    frozen.parent.mkdir(parents=True, exist_ok=True)
    content = path.read_bytes()
    frozen.write_bytes(content)
    entries.append({
        "path": path.as_posix(),
        "relative_path": rel.as_posix(),
        "sha256": hashlib.sha256(content).hexdigest(),
        "bytes": len(content),
        "mtime_utc": datetime.fromtimestamp(path.stat().st_mtime, timezone.utc).isoformat(),
        "snapshot": frozen.relative_to(ROOT).as_posix(),
        "scope": "Evidence text, not current Lean/kernel certification",
    })

head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                      encoding="utf-8", check=True).stdout.strip()
dump(OUT / "evidence.json", {
    "schema": "iut-exploration-evidence/v1",
    "task": "gap-exploration-20261030",
    "captured_at_utc": now(),
    "workspace": ROOT.as_posix(),
    "head": head,
    "version_rule": "Uncommitted files are identified by actual SHA256 and frozen copies; HEAD alone is insufficient.",
    "method": "single-agent source reading, bounded rg searches, PDF text/visual verification, historical log inspection",
    "scope": "Q-BRIDGE / xi-f; no whole-project proof audit",
    "not_run": ["Lean", "Project build", "comparator", "axiom probe", "independent review"],
    "report": {"path": REPORT.as_posix(), "sha256": sha(REPORT)},
    "node": {"path": NODE.as_posix(), "sha256": sha(NODE)},
    "search_log": (OUT / "search-results.json").relative_to(ROOT).as_posix(),
    "source_files": entries,
    "pdf_pages": [
        {"paper": "I", "printed_pages": [71], "visuals": ["source-pages/I-p71.png"]},
        {"paper": "III", "printed_pages": [173, 174, 183, 184],
         "visuals": ["source-pages/III-p173.png", "source-pages/III-p174.png",
                     "source-pages/III-p183.png", "source-pages/III-p184.png"]},
    ],
    "network_note": "Official PDF links were consulted; a repeat fetch timed out. The report cites the captured local primary PDFs and records their hashes.",
})

for item in link_records:
    item["exists"] = Path(item["path"]).exists()
missing = [x for x in link_records
           if not x["exists"] and Path(x["path"]) != OUT / "verification.json"]
bad_lines = [x for x in link_records if x.get("line_in_bounds") is False]
unstable = [x["relative_path"] for x in entries
            if "sha256" in x and sha(ROOT / x["relative_path"]) != x["sha256"]]
snapshot_errors = [x["relative_path"] for x in entries
                   if "sha256" in x and sha(ROOT / x["snapshot"]) != x["sha256"]]
references = node["statement_dependencies"] + node["proof_dependencies"]
node_refs = {ref: (ROOT / "dag/nodes" / (ref + ".json")).exists() for ref in references}
ancestor = json.loads((ROOT / "dag/nodes/xif-source-construction.json").read_text(encoding="utf-8-sig"))
direct_back_edge = node["id"] in ancestor["statement_dependencies"] + ancestor["proof_dependencies"]
json_checks = {}
for path in [NODE, OUT / "evidence.json", OUT / "search-results.json"]:
    json.loads(path.read_text(encoding="utf-8"))
    json_checks[path.relative_to(ROOT).as_posix()] = "parsed"
verification = {
    "verified_at_utc": now(), "kind": "documentation_and_snapshot_only",
    "report_links_count": len(link_records),
    "unique_sources_captured": len(entries),
    "missing_links": missing, "out_of_bounds_lines": bad_lines,
    "source_changed_during_capture": unstable, "snapshot_hash_errors": snapshot_errors,
    "json_checks": json_checks, "new_node_references_exist": node_refs,
    "new_direct_back_edge": direct_back_edge,
    "dag_check_scope": "Only this new node and its immediate existing consumer reference; no full historical DAG validation claimed.",
    "search_exit_codes": {x["id"]: x["exit_code"] for x in search_results},
    "no_lean_commands": True,
    "pass": not (missing or bad_lines or unstable or snapshot_errors or direct_back_edge)
            and all(node_refs.values()) and all(x["exit_code"] == 0 for x in search_results),
}
dump(OUT / "verification.json", verification)
print(json.dumps({
    "report": REPORT.as_posix(),
    "unique_sources_captured": len(entries),
    "report_links_count": len(link_records),
    "verification": verification,
}, ensure_ascii=False, indent=2))
