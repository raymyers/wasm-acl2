import sys,collections
exec(open('errs.py').read().split("errs=parse")[0])
for v in ["1.0","3.0"]:
    forms=parse(open(f"wasm-{v}.il.sexp").read())
    flat=[]
    for f in forms:
        flat += f[1:] if f[0]=='rec' else [f]
    def isparam(x): return isinstance(x,list) and len(x)>=2 and isinstance(x[1],str) and x[1].startswith('"') and x[0] in('exp','typ','def','gram')
    defs=[f for f in flat if f[0]=='def']
    builtins=[f[1] for f in defs if not any(isinstance(x,list) and x[0]=='clause' for x in f)]
    ho=[f[1] for f in defs if any(isparam(x) and x[0]=='def' for x in f[2:])]
    tp=[f[1] for f in defs if any(isparam(x) and x[0]=='typ' and len(x)==2 for x in f[2:])]
    rels=[f for f in flat if f[0]=='rel']
    rc={f[1]:sum(1 for x in f if isinstance(x,list) and x[0]=='rule') for f in rels}
    grams=[f[1] for f in flat if f[0]=='gram']
    print(v,"defs",len(defs),"builtins",len(builtins),"ho-defs",len(ho),ho[:12],"typaram-defs",len(tp))
    print("  rels",len(rels),"rules",sum(rc.values()),"empty rels",[k for k,c in rc.items() if c==0])
    print("  step rules",{k:c for k,c in rc.items() if k.strip('"').startswith('Step')}, "Instr_ok",rc.get('"Instr_ok"'))
    print("  grams",len(grams),"B",sum(g.startswith('"B') for g in grams),"T",sum(g.startswith('"T') for g in grams),"other",[g for g in grams if g[1] not in 'BT'][:10])
    # variants with atom-free case and >1 case
    bad=[]
    def walk(x,name):
        if isinstance(x,list):
            if x and x[0]=='variant':
                cs=[c for c in x[1:] if isinstance(c,list) and c[0]=='case']
                if len(cs)>1 and any(set(c[1].strip('"'))<=set('%') for c in cs): bad.append(name)
            for y in x: walk(y,name)
    for f in flat:
        if f[0]=='typ': walk(f,f[1])
    print("  multi-case variants with an atom-free case:",bad)
    print("  rec groups:",sorted(((len(f)-1,f[1][0]) for f in forms if f[0]=='rec'),reverse=True)[:6])
    if v=="3.0": print("  builtins:",' '.join(b.strip('"') for b in builtins))
