import json
SLgens=[]
for line in open('/tmp/local_matrices.jsonl'):
    d=json.loads(line); M=matrix(GF(5),d['M']); det=M.det()
    if det==0: continue
    D=diagonal_matrix(GF(5),[1,det^(-1)])
    N=M*D
    assert N.det()==1, (N,N.det())
    SLgens.append(N)
print('SLgens',len(SLgens), flush=True)
Hs=SL(2,5).subgroup(SLgens)
print('SL subgroup order',Hs.order(), flush=True)
