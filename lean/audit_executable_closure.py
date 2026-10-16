#!/usr/bin/env python3
"""Own generated-C dependency inventory, including closure/static initializers.
This over-approximates lexical symbol references. Imported runtime functions are
listed explicitly; it is not a proof of physical costs or the C toolchain.
"""
from pathlib import Path
import re,json
ROOT=Path(__file__).resolve().parent
IR=ROOT/'.lake/build/ir'; LOGS=ROOT/'build_logs/final'
sources={}; bodies={}; kinds={}
def body_end(src,pos):
    depth=1; quote=None
    while pos<len(src):
        c=src[pos]
        if quote:
            if c=='\\':pos+=2;continue
            if c==quote:quote=None
        elif c in ['"',"'"]:quote=c
        elif src.startswith('//',pos):
            end=src.find('\n',pos);pos=len(src) if end<0 else end;continue
        elif src.startswith('/*',pos):
            end=src.find('*/',pos+2)
            if end<0:raise ValueError('Unterminated generated C comment')
            pos=end+2;continue
        elif c=='{':depth+=1
        elif c=='}':
            depth-=1
            if depth==0:return pos+1
        pos+=1
    raise ValueError('Unbalanced generated C function')
modules=json.loads((LOGS/'audit_modules.json').read_text())
for path in sorted(IR/(m['module'].replace('.','/')+'.c') for m in modules):
    if not path.is_file():raise SystemExit('Missing generated C: '+str(path))
    src=path.read_text()
    for m in re.finditer(r'(?m)^(?:LEAN_EXPORT |static )?(?:lean_object\*|lean_object \*|uint\d+_t|size_t|double|float|void|int)\s+((?:_init_)?(?:l|lp)_[A-Za-z0-9_]+)\([^;\n]*\)\s*\{',src):
        pos=body_end(src,m.end())
        sym=m.group(1);sources[sym]=str(path.relative_to(ROOT));bodies[sym]=src[m.end():pos-1];kinds[sym]='function'
    for m in re.finditer(r'(?m)^static (?:const )?[^\n=;]+?\s+((?:l|lp)_[A-Za-z0-9_]+)\s*=\s*([^;\n]*);',src):
        sym=m.group(1);sources[sym]=str(path.relative_to(ROOT));bodies[sym]=m.group(2);kinds[sym]='static_data'
profiles={
'unbounded':['l_Cover_A06_runCover','l_Cover_A06_verifyRawCertificate','l_Cover_A06_firstSuccessfulStage'],
'capped':['l_Cover_A06_runCoverCapped'],
'compiler':['l_Cover_CompilerTasks_compileTask'],
}
reports=[]
for profile,required in profiles.items():
    missing=[s for s in required if s not in bodies]
    if missing:raise SystemExit('Missing extracted roots: '+repr(missing))
    seen=set();unknown=set();todo=list(required)
    while todo:
        s=todo.pop()
        if s in seen:continue
        seen.add(s)
        body=bodies.get(s)
        if body is None:unknown.add(s);continue
        for ref in set(re.findall(r'\b(?:l|lp)_[A-Za-z0-9_]+',body)):
            if ref not in seen:todo.append(ref)
            init='_init_'+ref
            if init in bodies and init not in seen:todo.append(init)
    forbidden=[s for s in seen if any(t in s for t in ['Classical_choice','Real_sqrt','Real_decidable','Gen_Rates_orbitDist']) or s=='l_Cover_PolyExpr_eval']
    if profile in ['capped','compiler']:
        forbidden += [s for s in seen if re.fullmatch(r'l_Cover_FiniteDesign_(?:componentDecidableEq|componentRelationDecidable|toBaseline)(?:___.*)?',s) or re.fullmatch(r'l_Cover_ConcreteCompiler_(?:modelOrdering|dimension|constraints|objective)(?:___.*)?',s)]
    if profile in ['capped','compiler']:
        forbidden += [s for s in seen if re.fullmatch(r'l_Cover_FinTask_(?:result|steps)(?:___.*)?',s)]
    if profile=='capped':
        forbidden += [s for s in seen if 'Nat_find' in s or re.fullmatch(r'l_Cover_(?:chooseLeafTask|visitTask|checkTreeTask|A06_stage|A06_firstSuccessfulStage|FiniteEnumeration_permutationLETask)(?:___.*)?',s)]
    flags=[s for s in unknown if any(t in s.lower() for t in ['classical','choose','realsqrt','realeq','propdecidable'])]
    report={'profile':profile,'roots':required,'reachable_extracted_count':len(seen-unknown),'forbidden_reachable_symbols':sorted(set(forbidden)), 'flagged_runtime_names':flags,'unresolved_runtime_symbols':sorted(unknown),'reachable_symbols':sorted(seen),'owned_symbol_sources':{s:sources[s] for s in sorted(seen-unknown)}}
    report['native_runtime_functions_referenced']=sorted({r for name in seen-unknown for r in re.findall(r'\b(lean_[A-Za-z0-9_]+)\s*\(',bodies[name])})
    reports.append(report)
    print(profile+': '+str(len(seen-unknown))+' own extracted symbols, '+str(len(unknown))+' pinned runtime symbols; forbidden='+repr(forbidden),flush=True)
LOGS.mkdir(parents=True,exist_ok=True)
(LOGS/'executable_closure.json').write_text(json.dumps({'scope':'Generated own C lexical symbol closure, including closure references and static initializers; runtime imports explicitly listed, not a whole compiler/runtime verification. Proof-erased semantic specifications are excluded from execution. This does not prove OS or single-step allocation bounds.','extracted_function_count':sum(v=='function' for v in kinds.values()),'extracted_static_data_count':sum(v=='static_data' for v in kinds.values()),'profiles':reports},indent=2)+'\n')
if any(r['forbidden_reachable_symbols'] for r in reports):raise SystemExit('Forbidden extracted dependency requires disposition')
