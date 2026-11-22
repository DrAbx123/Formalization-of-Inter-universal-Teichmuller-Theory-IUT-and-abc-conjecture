import os, re, subprocess, sys, time
from pathlib import Path
ROOT = Path(r"D:\lean")
START = ROOT / "tmp" / "sheaf" / "xif"
LOG = ROOT / "tmp" / "xif_memo_build.log"
RES = ROOT / "tmp" / "xif_memo_results.log"
BLOCKED = ROOT / "tmp" / "xif_memo_blocked.txt"
FAILED = ROOT / "tmp" / "xif_memo_failed.txt"
OKF = ROOT / "tmp" / "xif_memo_ok.txt"
def log(s):
    line=f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {s}"
    print(line, flush=True)
    with open(LOG,'a',encoding='utf-8') as f: f.write(line+'\n')
def module_of(p): return str(p.relative_to(ROOT).with_suffix('')).replace(chr(92),'.').replace('/','.')
def path_of_module(m): return ROOT / (m.replace('.', os.sep) + '.lean')
def olean_of(m): return ROOT/'.lake'/'build'/'lib'/'lean'/(m.replace('.', os.sep)+'.olean')
# index all tmp modules
mods={}
for p in (ROOT/'tmp').rglob('*.lean'):
    mods[module_of(p)]=p
imports={}
for m,p in mods.items():
    try: text=p.read_text(encoding='utf-8',errors='replace')
    except Exception: text=''
    deps=[]
    for line in text.splitlines():
        mm=re.match(r'^\s*import\s+([A-Za-z0-9_\.]+)\s*$', line)
        if mm:
            dep=mm.group(1)
            if dep in mods: deps.append(dep)
    imports[m]=deps
starts=sorted(set(module_of(p) for p in START.rglob('*.lean')))
log(f"start files={len(starts)} tmp_modules={len(mods)}")
# topological dependencies-first
order=[]; state={}
def dfs(m, stack):
    st=state.get(m,0)
    if st==1: raise RuntimeError('cycle: '+' -> '.join(stack+[m]))
    if st==2: return
    state[m]=1
    for d in imports.get(m,[]): dfs(d, stack+[m])
    state[m]=2; order.append(m)
for m in starts: dfs(m, [])
log(f"topological order={len(order)}")
# freshness
def fresh(m):
    p=mods[m]; o=olean_of(m)
    return o.exists() and o.stat().st_mtime >= p.stat().st_mtime
# dependency readiness
def missing_deps(m):
    return [d for d in imports.get(m,[]) if not fresh(d)]
# pending = non-fresh modules in topo order
pending=[m for m in order if not fresh(m)]
log(f"pending={len(pending)} skipped_fresh={len(order)-len(pending)}")
# initial memo check without Lean
initial_blocked={m:missing_deps(m) for m in pending if missing_deps(m)}
initial_ready=[m for m in pending if not missing_deps(m)]
log(f"memo_initial_ready={len(initial_ready)} memo_initial_blocked={len(initial_blocked)}")
# state
failed=[]; ok=[]; blocked={}
remaining=set(pending)
def ready_now():
    r=[]; b=[]
    for m in order:
        if m not in remaining: continue
        md=missing_deps(m)
        if md: b.append((m,md))
        else: r.append(m)
    return r,b
pass_no=0
res=open(RES,'a',encoding='utf-8')
while True:
    ready, blocked_list = ready_now()
    blocked={m:md for m,md in blocked_list}
    if not ready:
        log(f"STOP no ready modules remaining; blocked={len(blocked)}")
        break
    pass_no += 1
    log(f"PASS {pass_no} ready={len(ready)} blocked_without_lean={len(blocked)}")
    progressed=0
    for i,m in enumerate(ready,1):
        p=mods[m]; o=olean_of(m); o.parent.mkdir(parents=True,exist_ok=True)
        cmd=['lake','env','lean','-j1','-R',str(ROOT),'-o',str(o),str(p)]
        try:
            cp=subprocess.run(cmd,cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=600)
            code=cp.returncode; out=cp.stdout.decode('utf-8','replace')
        except subprocess.TimeoutExpired:
            code=-999; out='TIMEOUT'
        except Exception as e:
            code=-998; out=f'EXC {e}'
        res.write(f"PASS={pass_no} EXIT={code} FILE={p.relative_to(ROOT)}\n"); res.flush()
        if out: res.write('\n'.join(out.splitlines()[-100:])+'\n'); res.flush()
        remaining.discard(m)
        if code==0:
            ok.append(m); progressed+=1
        else:
            failed.append(m)
        if i%10==0 or i==len(ready): log(f"PASS {pass_no} progress {i}/{len(ready)} ok={len(ok)} fail={len(failed)}")
    log(f"PASS {pass_no} done ok={len(ok)} fail={len(failed)} progressed={progressed}")
    if progressed==0:
        log("STOP no progress")
        break
    if pass_no>=6:
        log("STOP pass limit")
        break
res.close()
# final readiness snapshot
ready, blocked_list = ready_now()
blocked={m:md for m,md in blocked_list}
with open(BLOCKED,'w',encoding='utf-8') as f:
    for m,md in sorted(blocked.items()):
        f.write(str(mods[m].relative_to(ROOT))+' | missing: '+', '.join(md)+'\n')
with open(FAILED,'w',encoding='utf-8') as f:
    for m in failed: f.write(str(mods[m].relative_to(ROOT))+'\n')
with open(OKF,'w',encoding='utf-8') as f:
    for m in ok: f.write(str(mods[m].relative_to(ROOT))+'\n')
log(f"DONE ok={len(ok)} failed={len(failed)} blocked={len(blocked)} remaining={len(remaining)}")
