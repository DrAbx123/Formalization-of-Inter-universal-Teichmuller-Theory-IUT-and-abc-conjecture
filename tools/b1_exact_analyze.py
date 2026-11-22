import csv,math,statistics as st
rows=list(csv.DictReader(open('coord/b1_exact_snf_500.csv')))
print('n',len(rows))
vals=[int(r['min_abs']) for r in rows]
print('zero',sum(1 for v in vals if v==0),'one',sum(1 for v in vals if v==1),'gt1',sum(1 for v in vals if v>1))
print('minmax',min(vals),max(vals))
# compare r_f
ratio=[]
for r in rows:
    v=int(r['min_abs']); rf=int(r['r_f'])
    if v>0: ratio.append(v/rf)
print('min/rf min/max/median',min(ratio),max(ratio),st.median(ratio))
print('exact==r_f',sum(1 for r in rows if int(r['min_abs'])==int(r['r_f'])))
print('exact divides r_f',sum(1 for r in rows if int(r['min_abs'])>0 and int(r['r_f'])%int(r['min_abs'])==0))
# Cobs for min>0
def cobs(r):
    v=int(r['min_abs']); N=int(r['N'])
    return math.log(v)/math.log(N) if v>0 and N>1 else None
cs=[(int(r['N']),cobs(r),int(r['min_abs']),r['label']) for r in rows if cobs(r) is not None]
print('Cobs min/max/median/mean',min(c for _,c,_,_ in cs),max(c for _,c,_,_ in cs),st.median(c for _,c,_,_ in cs),st.mean(c for _,c,_,_ in cs))
for lo in [0,100,200,300,400]:
    hi=lo+100
    z=[(c,m,l) for N,c,m,l in cs if lo<=N<hi]
    if z:
        print('BIN',lo,hi,'n',len(z),'max',max(c for c,_,_ in z),'median',st.median(c for c,_,_ in z),'mean',st.mean(c for c,_,_ in z),'maxmin',max(m for _,m,_ in z))
# slope log min vs log N for min>0 all, and excluding min1
zs=[(math.log(int(r['N'])),math.log(int(r['min_abs'])),int(r['min_abs'])) for r in rows if int(r['min_abs'])>0]
def slope(z):
    xs=[a for a,b,_ in z]; ys=[b for a,b,_ in z]; mx=st.mean(xs); my=st.mean(ys)
    return sum((x-mx)*(y-my) for x,y in zip(xs,ys))/sum((x-mx)**2 for x in xs)
print('slope all',slope(zs))
print('slope >1',slope([z for z in zs if z[2]>1]))
print('slope >r_f?',slope([z for z in zs if z[2]>1]))
# Qp compare
both=[r for r in rows if r['qp_found']=='True' and r['qp_value']!='' and int(r['min_abs'])>0]
print('both',len(both),'exact<q',sum(1 for r in both if int(r['min_abs'])<int(r['qp_value'])),'eq',sum(1 for r in both if int(r['min_abs'])==int(r['qp_value'])),'gt',sum(1 for r in both if int(r['min_abs'])>int(r['qp_value'])))
