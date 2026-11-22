import shutil, os, sys
root=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))  # not used
resources=r'D:\Users\Administrator\AppData\Local\Programs\DeepSeek Harness\resources'
src=os.path.join(resources,'app.asar')
out=os.path.join(resources,'app.asar.16g')
b=bytearray(open(src,'rb').read())
old1=b'node: process.execPath'
new1=b'node: process.env.DSHN'
old2=b'join(app.getAppPath(), "dsh")'
new2=b'process.env.DSH_DESKTOP_HOST_'
print('len',len(old1),len(new1),len(old2),len(new2))
print('count1',b.count(old1),'count2',b.count(old2))
assert len(old1)==len(new1) and len(old2)==len(new2)
assert b.count(old1)==1 and b.count(old2)==1
i=b.find(old1); b[i:i+len(old1)]=new1
i=b.find(old2); b[i:i+len(old2)]=new2
open(out,'wb').write(b)
print('wrote',out,len(b))
