import csv,math,statistics as st
rows=list(csv.DictReader(open('coord/b1_exact_snf_1000.csv')))
print('n',len(rows))
vals=[int(r['min_abs']) for r in rows]
print('zero',sum(1 for v in vals if v==0),'one',sum(1 for v in vals if v==1),'gt1',sum(1 for v in vals if v>1))
zs=[(math.log(int(r['N'])),math.log(int(r['min_abs'])),int(r['min_abs'])) for r in rows if int(r['min_abs'])>0]
xs=[a for a,b,c in zs]; ys=[b for a,b,c in zs]; mx=st.mean(xs); my=st.mean(ys)
print('slope all',sum((x-mx)*(y-my) for x,y in zip(xs,ys))/sum((x-mx)**2 for x in xs))
for lo in range(0,1000,100):
    allz=[r for r in rows if lo<=int(r['N'])<lo+100]
    z=[(math.log(int(r['min_abs']))/math.log(int(r['N'])),int(r['min_abs'])) for r in allz if int(r['min_abs'])>0]
    print('BIN',lo,lo+100,'rows',len(allz),'zero',sum(1 for r in allz if int(r['min_abs'])==0),'pos',len(z),'max',round(max(c for c,m in z),4) if z else None,'median',round(st.median(c for c,m in z),4) if z else None,'mean',round(st.mean(c for c,m in z),4) if z else None,'maxmin',max(m for c,m in z) if z else None)
# zero distribution by N
for lo in range(0,1000,100):
    allz=[r for r in rows if lo<=int(r['N'])<lo+100]
    if allz: print('ZERO',lo,sum(1 for r in allz if int(r['min_abs'])==0),'/',len(allz))
# compare 500 exact file
old=list(csv.DictReader(open('coord/b1_exact_snf_500.csv')))
print('old',len(old),'new<=500',sum(1 for r in rows if int(r['N'])<=500))
# Cobs among positive all
allc=[(int(r['N']),math.log(int(r['min_abs']))/math.log(int(r['N']))) for r in rows if int(r['min_abs'])>0]
print('C max/median',max(c for _,c in allc),st.median(c for _,c in allc))
