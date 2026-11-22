import json
ms=[]
for line in open('/tmp/local_matrices.jsonl'):
    d=json.loads(line)
    ms.append(matrix(GF(5),d['M']))
print('num',len(ms), flush=True)
H=GL(2,5).subgroup(ms)
print('order',H.order(), flush=True)
print('is GL2', H == GL(2,5), flush=True)
# determinant 1 subgroup generated
SLgens=[]
for l in open('/tmp/local_matrices.jsonl'):
    d=json.loads(l); M=matrix(GF(5),d['M'])
    if M.det()!=0:
        # take M / det to get det 1
        SLgens.append(M * M.det()^(-1))
Hs=SL(2,5).subgroup(SLgens)
print('SL order',Hs.order(), flush=True)
