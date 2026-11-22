import os, re, subprocess, sys, time
from pathlib import Path
ROOT = Path(r"D:\lean")
START = ROOT / "tmp" / "sheaf" / "xif"
LOG = ROOT / "tmp" / "xif_topo_build.log"
RES = ROOT / "tmp" / "xif_topo_results.log"
FAILED = ROOT / "tmp" / "xif_topo_failed.txt"
def log(s):
    line=f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {s}"
    print(line, flush=True)
    with open(LOG,'a',encoding='utf-8') as f: f.write(line+'\n')
def module_of(p):
    rel=p.relative_to(ROOT)
    return str(rel.with_suffix('')).replace('\\','.').replace('/','.')
def path_of_module(m):
    return ROOT / (m.replace('.', os.sep) + '.lean')
# index all tmp lean modules
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
            if dep in mods:
                deps.append(dep)
    imports[m]=deps
starts=[module_of(p) for p in START.rglob('*.lean')]
starts=sorted(set(starts))
log(f"start files={len(starts)} tmp_modules={len(mods)}")
# DFS topological, dependencies first
order=[]; state={}
def dfs(m, stack):
    st=state.get(m,0)
    if st==1:
        raise RuntimeError('cycle: '+' -> '.join(stack+[m]))
    if st==2: return
    state[m]=1
    for d in imports.get(m,[]):
        dfs(d, stack+[m])
    state[m]=2
    order.append(m)
try:
    for m in starts: dfs(m, [])
except Exception as e:
    log('TOPO ERROR '+str(e)); sys.exit(2)
# filter to reachable set (starts + deps)
reach=set(order)
order=[m for m in order if m in reach]
log(f"topological order={len(order)} (includes tmp deps)")
with open(ROOT/'tmp'/'xif_topo_queue.txt','w',encoding='utf-8') as f:
    for m in order: f.write(str(mods[m].relative_to(ROOT))+'\n')
# compile
def fresh(m):
    p=mods[m]; olean=ROOT/'.lake'/'build'/'lib'/'lean'/(str(p.relative_to(ROOT).with_suffix('.olean')))
    return olean.exists() and olean.stat().st_mtime >= p.stat().st_mtime, olean
pending=[]
for m in order:
    ok,olean=fresh(m)
    if not ok: pending.append(m)
log(f"pending compile={len(pending)} skipped_fresh={len(order)-len(pending)}")
maxpass=4
res=open(RES,'a',encoding='utf-8')
for pass_no in range(1,maxpass+1):
    if not pending: break
    log(f"PASS {pass_no} pending={len(pending)}")
    nxt=[]; success=0
    for i,m in enumerate(pending,1):
        p=mods[m]
        olean=ROOT/'.lake'/'build'/'lib'/'lean'/(str(p.relative_to(ROOT).with_suffix('.olean')))
        olean.parent.mkdir(parents=True,exist_ok=True)
        cmd=['lake','env','lean','-j1','-R',str(ROOT),'-o',str(olean),str(p)]
        try:
            cp=subprocess.run(cmd,cwd=str(ROOT),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=600)
            code=cp.returncode; out=cp.stdout.decode('utf-8','replace')
        except subprocess.TimeoutExpired:
            code=-999; out='TIMEOUT'
        except Exception as e:
            code=-998; out=f'EXC {e}'
        res.write(f"PASS={pass_no} EXIT={code} FILE={p.relative_to(ROOT)}\n"); res.flush()
        if out:
            res.write('\n'.join(out.splitlines()[-80:])+'\n'); res.flush()
        if code==0:
            success+=1
        else:
            nxt.append(m)
        if i%10==0 or i==len(pending): log(f"PASS {pass_no} progress {i}/{len(pending)} ok={success} fail={len(nxt)}")
    log(f"PASS {pass_no} done success={success} fail={len(nxt)}")
    pending=nxt
    if success==0: break
res.close()
with open(FAILED,'w',encoding='utf-8') as f:
    for m in pending: f.write(str(mods[m].relative_to(ROOT))+'\n')
log(f"BUILD DONE remaining_failed={len(pending)}")
