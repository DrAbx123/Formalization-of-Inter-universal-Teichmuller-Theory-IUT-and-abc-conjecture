import csv,math,statistics as st
rows=list(csv.DictReader(open('coord/b1_exact_snf_1000.csv')))
pos=[r for r in rows if int(r['min_abs'])>0]
def slope(rs):
    zs=[(math.log(int(r['N'])),math.log(int(r['min_abs']))) for r in rs]
    xs=[a for a,b in zs]; ys=[b for a,b in zs]; mx=st.mean(xs); my=st.mean(ys)
    return sum((x-mx)*(y-my) for x,y in zip(xs,ys))/sum((x-mx)**2 for x in xs)
print('pos',len(pos),'slope positive',slope(pos),'slope all rows',slope([r for r in rows if int(r['min_abs'])>0]))
print('Cobs positive max median mean',max(math.log(int(r['min_abs']))/math.log(int(r['N'])) for r in pos),st.median(math.log(int(r['min_abs']))/math.log(int(r['N'])) for r in pos),st.mean(math.log(int(r['min_abs']))/math.log(int(r['N'])) for r in pos))
print('eq rf',sum(1 for r in rows if int(r['min_abs'])==int(r['r_f'])),'div',sum(1 for r in rows if int(r['min_abs'])>0 and int(r['r_f'])%int(r['min_abs'])==0),'gt',sum(1 for r in rows if int(r['min_abs'])>int(r['r_f'])))
rat=[int(r['min_abs'])/int(r['r_f']) for r in pos]
print('ratio median min max',st.median(rat),min(rat),max(rat))
print('min max',min(int(r['min_abs']) for r in rows),max(int(r['min_abs']) for r in rows))
# bins with 200 ranges for extension concise
for lo in range(0,1000,100):
 a=[r for r in rows if lo<=int(r['N'])<lo+100]; z=[r for r in a if int(r['min_abs'])>0]
 print('B',lo,len(a),sum(1 for r in a if int(r['min_abs'])==0),len(z), (max(math.log(int(r['min_abs']))/math.log(int(r['N'])) for r in z) if z else None),(st.median(math.log(int(r['min_abs']))/math.log(int(r['N'])) for r in z) if z else None))
