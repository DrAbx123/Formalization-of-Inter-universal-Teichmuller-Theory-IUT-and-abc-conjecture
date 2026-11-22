from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess

BASE = Path('D:/lean')
TASK = 'supplement-gap-priorities-20261030'
OUT = BASE / 'tmp/sheaf' / TASK
REPORT = BASE / 'coord/reports' / (TASK + '.md')
NODE = BASE / 'dag/nodes' / (TASK + '.json')

def sha(data):
    return hashlib.sha256(data).hexdigest()

def dump(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

text = REPORT.read_text(encoding='utf-8-sig')
links = re.findall(r'\]\((D:/[^\n)]+)\)', text)
generated = {OUT / 'evidence.json', OUT / 'verification.json'}
sources = set()
for link in links:
    path = Path(re.sub(r':\d+$', '', link))
    if path not in generated:
        sources.add(path)
for rel in [
    'papers/motizuki_corpus/raw/Formalization of IUT (2026-04).pdf',
    'papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt',
    'papers/motizuki_corpus/raw/Essential Logical Structure of Inter-universal Teichmuller Theory.pdf',
    'papers/motizuki_corpus/text/Essential Logical Structure of Inter-universal Teichmuller Theory.txt',
    'LeanFormal/IUT/IUTIII/Corollary312/Routes.lean',
    'LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceSHETransportLaws.lean',
    'tmp/sheaf/n8/closure/C9-ROUTE-CONSISTENCY-REVIEW-20261023.md',
    'tmp/sheaf/n8/closure/C9-STAGE1-SUPPLEMENT-ROUTE-20261023.md',
    'tmp/sheaf/supplement-gap-priorities-20261030/TASK.md',
]:
    sources.add(BASE / rel)
records = []
for path in sorted(sources):
    data = path.read_bytes()
    snapshot = OUT / 'snapshots' / path.relative_to(BASE)
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    snapshot.write_bytes(data)
    records.append({'path': path.as_posix(), 'sha256': sha(data), 'bytes': len(data),
                    'snapshot': snapshot.as_posix()})
old = json.loads((BASE / 'tmp/sheaf/gap-exploration-20261030/evidence.json').read_text(encoding='utf-8-sig'))
previous = BASE / 'coord/reports/gap-exploration-20261030.md'
previous_unchanged = sha(previous.read_bytes()) == old['report']['sha256']
node = json.loads(NODE.read_text(encoding='utf-8-sig'))
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=BASE, text=True).strip()
manifest = {
    'schema': 'iut-exploration-evidence/v1', 'task': TASK,
    'captured_at_utc': datetime.now(timezone.utc).isoformat(), 'head': head,
    'version_rule': 'Source bytes and hashes control; the dirty workspace is not identified by HEAD alone.',
    'scope': 'Single-agent priority review, no new mathematical proof; previous report preserved.',
    'report': {'path': REPORT.as_posix(), 'sha256': sha(REPORT.read_bytes())},
    'node': {'path': NODE.as_posix(), 'sha256': sha(NODE.read_bytes())},
    'source_files': records, 'previous_report_unchanged': previous_unchanged,
    'pdf_visual_checks': ['Formalization 2026 p.10', 'EssLgc 2024 p.155'],
    'other_rendered_pages_not_claimed_visually_checked': ['Formalization 2026 p.11', 'EssLgc 2024 pp.150,153'],
    'statement_compiles': 'not_run', 'proof_body_checked': 'not_run',
    'kernel_closed': 'not_run', 'target_accepted': False,
    'not_run': ['Lean', 'Project build', 'comparator', 'axiom probe', 'independent review'],
}
dump(OUT / 'evidence.json', manifest)
dump(OUT / 'verification.json', {'status': 'checking'})
errors = []
for link in links:
    match = re.match(r'^(.*?):(\d+)$', link)
    path = Path(match.group(1) if match else link)
    if not path.is_file():
        errors.append('Missing link: ' + link)
    elif match and int(match.group(2)) > len(path.read_text(encoding='utf-8-sig').splitlines()):
        errors.append('Line outside file: ' + link)
for record in records:
    for key in ['path', 'snapshot']:
        if sha(Path(record[key]).read_bytes()) != record['sha256']:
            errors.append('Hash mismatch: ' + record[key])
for dep in node['statement_dependencies'] + node['proof_dependencies']:
    dep_path = BASE / 'dag/nodes' / (dep + '.json')
    if not dep_path.is_file():
        errors.append('Missing immediate dependency: ' + dep)
    else:
        dep_node = json.loads(dep_path.read_text(encoding='utf-8-sig'))
        if TASK in dep_node.get('statement_dependencies', []) + dep_node.get('proof_dependencies', []):
            errors.append('Immediate dependency backedge: ' + dep)
if not previous_unchanged:
    errors.append('Previous report changed from its frozen manifest')
for record in json.loads((OUT / 'append-record.json').read_text(encoding='utf-8')):
    data = Path(record['path']).read_bytes()
    if sha(data[:record['previous_bytes']]) != record['previous_sha256']:
        errors.append('Historical prefix changed: ' + record['path'])
verification = {
    'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'pass': not errors,
    'local_links_checked': len(links), 'source_snapshots_checked': len(records),
    'errors': errors, 'dag_scope': 'This new node and immediate dependencies only; no full DAG review',
    'previous_report_unchanged': previous_unchanged,
    'mathematical_or_Lean_verification': 'not_run', 'target_accepted': False,
}
dump(OUT / 'verification.json', verification)
print(json.dumps(verification, ensure_ascii=False))
if errors:
    raise SystemExit(1)
