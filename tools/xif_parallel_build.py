import os, re, subprocess, sys, time, concurrent.futures
from pathlib import Path
ROOT = Path(r"D:\lean")
START = ROOT / "tmp" / "sheaf" / "xif"
LOG = ROOT / "tmp" / "xif_parallel_build.log"
RES = ROOT / "tmp" / "xif_parallel_results.log"
BLOCKED = ROOT / "tmp" / "xif_parallel_blocked.txt"
FAILED = ROOT / "tmp" / "xif_parallel_failed.txt"
OKF = ROOT / "tmp" / "xif_parallel_ok.txt"
WORKERS = 4
def log(s):
    line=f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {s}"
    print(line, flush=True)
    with open(LOG,'a',encoding='utf-8') as f: f.write(line+'\n')
def module_of(p): return str(p.relative_to(ROOT).with_suffix('')).replace(chr(92),'.').replace('/','.')
def olean_of(m): return ROOT/'.lake'/'build'/'lib'/'lean'/(m.replace('.', os.sep)+'.olean')
mods={}
for p in (ROOT/'tmp').rglob('*.lean'): mods[module_of(p)]=p
imports={}
for m,p in mods.items():
    try: text=p.read_text(encoding='utf-8',errors='replace')
    except Exception: text=''
    deps=[]
    for line in text.splitlines():
        mm=re.match(r'^\s*import\s+([A-Za-z0-9_\.]+)\s*$', line)
        if mm and mm.group(1) in mods: deps.append(mm.group(1))
    imports[m]=deps
if '--files' in sys.argv:
    _i = sys.argv.index('--files')
    _sel = sys.argv[_i+1:]
    starts = []
    for _x in _sel:
        _p = Path(_x)
        if _p.is_absolute(): _p = _p.relative_to(ROOT)
        starts.append(str(_p.with_suffix('')).replace(chr(92),'.').replace('/','.'))
    starts = sorted(set(starts))
else:
    starts=sorted(set(module_of(p) for p in START.rglob('*.lean')))
order=[]; state={}
def dfs(m, stack):
    st=state.get(m,0)
    if st==1: raise RuntimeError('cycle: '+' -> '.join(stack+[m]))
    if st==2: return
    state[m]=1
    for d in imports.get(m,[]): dfs(d, stack+[m])
    state[m]=2; order.append(m)
for m in starts: dfs(m, [])
def fresh(m):
    p=mods[m]; o=olean_of(m)
    return o.exists() and o.stat().st_mtime >= p.stat().st_mtime
def missing_deps(m): return [d for d in imports.get(m,[]) if not fresh(d)]
log(f"start files={len(starts)} order={len(order)} workers={WORKERS}")
pending=[m for m in order if not fresh(m)]
log(f"pending={len(pending)} skipped_fresh={len(order)-len(pending)}")
remaining=set(pending); failed=[]; ok=[]; blocked={}
res=open(RES,'a',encoding='utf-8')
def compile_one(m):
    p=mods[m]; o=olean_of(m); o.parent.mkdir(parents=True,exist_ok=True)
    cmd=['lake','env','lean','-j1','-R',str(ROOT),'-o',str(o),str(p)]
    try:
        cp=subprocess.run(cmd,cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=600)
        return m,cp.returncode,cp.stdout.decode('utf-8','replace')
    except subprocess.TimeoutExpired: return m,-999,'TIMEOUT'
    except Exception as e: return m,-998,f'EXC {e}'
pass_no=0
while True:
    ready=[]; blocked={}
    for m in order:
        if m not in remaining: continue
        md=missing_deps(m)
        if md: blocked[m]=md
        else: ready.append(m)
    if not ready:
        log(f"STOP no ready; blocked={len(blocked)} remaining={len(remaining)}")
        break
    pass_no+=1
    log(f"PASS {pass_no} ready={len(ready)} blocked={len(blocked)}")
    with concurrent.futures.ThreadPoolExecutor(max_workers=WORKERS) as ex:
        futs={ex.submit(compile_one,m):m for m in ready}
        done=0
        for fut in concurrent.futures.as_completed(futs):
            m,code,out=fut.result(); done+=1
            res.write(f"PASS={pass_no} EXIT={code} FILE={mods[m].relative_to(ROOT)}\n"); res.flush()
            if out: res.write('\n'.join(out.splitlines()[-60:])+'\n'); res.flush()
            remaining.discard(m)
            if code==0: ok.append(m)
            else: failed.append(m)
            if done%10==0 or done==len(ready): log(f"PASS {pass_no} progress {done}/{len(ready)} ok={len(ok)} fail={len(failed)}")
    log(f"PASS {pass_no} done ok={len(ok)} fail={len(failed)}")
    if len(remaining)==0: break
    if pass_no>=6: break
res.close()
ready=[]; blocked={}
for m in order:
    if m in remaining:
        md=missing_deps(m)
        if md: blocked[m]=md
        else: ready.append(m)
with open(BLOCKED,'w',encoding='utf-8') as f:
    for m,md in sorted(blocked.items()): f.write(str(mods[m].relative_to(ROOT))+' | missing: '+', '.join(md)+'\n')
with open(FAILED,'w',encoding='utf-8') as f:
    for m in failed: f.write(str(mods[m].relative_to(ROOT))+'\n')
with open(OKF,'w',encoding='utf-8') as f:
    for m in ok: f.write(str(mods[m].relative_to(ROOT))+'\n')
log(f"DONE ok={len(ok)} failed={len(failed)} blocked={len(blocked)} remaining={len(remaining)}")
