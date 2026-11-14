import sys,re,collections
s=open(sys.argv[1]).read()
# minimal sexp parser
def parse(s):
    i=0;n=len(s);stack=[[]]
    while i<n:
        c=s[i]
        if c.isspace(): i+=1
        elif c=='(':
            stack.append([]); i+=1
        elif c==')':
            x=stack.pop(); stack[-1].append(x); i+=1
        elif c=='"':
            j=i+1
            while s[j]!='"':
                if s[j]=='\\': j+=1
                j+=1
            stack[-1].append('"'+s[i+1:j]+'"'); i=j+1
        else:
            j=i
            while j<n and not s[j].isspace() and s[j] not in '()': j+=1
            stack[-1].append(s[i:j]); i=j
    return stack[0]
def show(x):
    if isinstance(x,list): return '('+' '.join(show(y) for y in x)+')'
    return x
errs=parse(s)[0]
bykind=collections.defaultdict(list)
for e in errs:
    bykind[e[1]].append(e)
for k,es in sorted(bykind.items(), key=lambda kv:-len(kv[1])):
    fns=collections.Counter(e[0] for e in es)
    print(f"\n### {k}: {len(es)}  in {len(fns)} fns")
    print("   fns:", ' '.join(f"{f}:{c}" for f,c in fns.most_common(40)))
    seen=set();shown=0
    heads=collections.Counter()
    for e in es:
        x=e[2] if len(e)>2 else ''
        h=x[0] if isinstance(x,list) and x else x
        heads[h if not isinstance(h,list) else 'LIST']+=1
    print("   heads:",dict(heads.most_common(15)))
    for e in es:
        if e[0].startswith('"GRAM/T') : continue
        x=show(e[2]) if len(e)>2 else ''
        key=(e[0])
        if key in seen: continue
        seen.add(key); shown+=1
        print("   ",e[0],x[:230])
        if shown>=int(sys.argv[2]): break
