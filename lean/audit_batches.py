#!/usr/bin/env python3
"""Per-module audit under the unchanged 4GiB Lean cap; no shared writes."""
import json,os,pathlib,re,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parent
TC=pathlib.Path(os.environ['LEAN_TOOLCHAIN'])
PKGS=pathlib.Path(os.environ['LEAN_PACKAGES'])
LOGS=ROOT/'build_logs/final';DIR=ROOT/'lean/audit_batches';DIR.mkdir(parents=True,exist_ok=True)
BUILD=ROOT/'.lake/build/lib/lean'
env=os.environ.copy();env['PATH']=str(TC/'bin')+':'+env.get('PATH','');env['LEAN_PATH']=':'.join([str(BUILD)]+[str(p/'.lake/build/lib/lean') for p in sorted(PKGS.iterdir()) if p.is_dir()])
mods=json.loads((LOGS/'audit_modules.json').read_text())
items=[];extras=[];records=[]; expressions={}; all_axioms=set()

def run(label,p):
 cmd=[str(TC/'bin/lean'),'-M','4096',str(p.relative_to(ROOT))]
 t=time.time();r=subprocess.run(cmd,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=LOGS/(label+'.log');log.write_text(r.stdout)
 records.append({'batch':label,'command':cmd,'exit_code':r.returncode,'elapsed_seconds':time.time()-t,'log':str(log.relative_to(ROOT))})
 (LOGS/'audit_batch_manifest.json').write_text(json.dumps(records,indent=2)+'\n')
 if r.returncode:print(r.stdout);raise SystemExit(r.returncode)
 return r.stdout
for k,mod in enumerate(mods):
 name=mod['module'];source=ROOT/mod['source']
 stripped=re.sub(r'/\-.*?\-/','',source.read_text(),flags=re.S);stripped=re.sub(r'--[^\n]*','',stripped)
 if all(not l.strip() or l.startswith('import ') or l.startswith('public import ') for l in stripped.splitlines()):
  records.append({'module':name,'status':'import-only source: no owned kernel declarations'});continue
 inv=DIR/f'Inventory{k:03}.lean'
 inv.write_text('import '+name+'\nimport Lean.Elab.Command\n\nopen Lean Elab Command in\nrun_cmd do\n  let rec nameExpr : Name → String\n    | .anonymous => "Lean.Name.anonymous"\n    | .str p s => "(Lean.Name.str " ++ nameExpr p ++ " " ++ reprStr s ++ ")"\n    | .num p n => "(Lean.Name.num " ++ nameExpr p ++ " " ++ reprStr n ++ ")"\n  let env ← getEnv\n  let names := env.header.moduleNames\n  let target := names.map (· == `'+name+')\n  let owners := env.const2ModIdx\n  for (n,idx) in owners do\n    if target[idx.toNat]! then\n      match env.find? n with\n      | some ci =>\n        let kind := if ci.isTheorem then "theorem" else "constant"\n        liftIO (IO.println s!"OWNED_DECL '+name+' {kind} {n}")\n        liftIO (IO.println s!"OWNED_EXPR {n} {nameExpr n}")\n      | none => liftIO (IO.println s!"OWNED_CODEGEN '+name+' {n}")\n')
 out=run(f'inventory_{k:03}',inv)
 found=sorted(set(re.findall(r'OWNED_DECL (\S+) (\S+) (\S+)',out)))
 foundextra=sorted(set(re.findall(r'OWNED_CODEGEN (\S+) (\S+)',out)))
 items+=found;extras+=foundextra
 expressions.update(dict(re.findall(r'OWNED_EXPR (\S+) (.+)',out)))
 audit=DIR/f'Axioms{k:03}.lean'
 audit.write_text('import '+name+'\nimport Lean.Elab.Command\nopen Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n  let names := env.header.moduleNames\n  let target := names.map (· == `'+name+')\n  for (n, idx) in env.const2ModIdx do\n    if target[idx.toNat]! then\n      if (env.find? n).isSome then\n        elabCommand (← `(#print axioms $(mkIdent n)))\n')
 ao=run(f'axioms_{k:03}',audit)
 printed=set(re.findall(r"^'(.*)' (?:depends on axioms|does not depend on any axioms)",ao,re.M))
 expected={n for m,t,n in found}
 if printed != expected:raise SystemExit(f'Audit coverage mismatch {name}: missing={expected-printed}, extra={printed-expected}')
 axi=set()
 for group in re.findall(r'depends on axioms: \[(.*?)\]',ao,re.S):axi.update(x.strip() for x in group.split(',') if x.strip())
 all_axioms.update(axi)
 bad=axi-{'propext','Classical.choice','Quot.sound'}
 if bad:raise SystemExit(f'Nonstandard axioms {name}: {bad}')
 print(f'AUDITED {name}: {len(found)} kernel constants, {len(foundextra)} codegen-only names',flush=True)
 (LOGS/'all_owned_constants.json').write_text(json.dumps([{'module':m,'kind':t,'name':n} for m,t,n in sorted(set(items))],indent=2)+'\n')
 (LOGS/'codegen_only_constants.json').write_text(json.dumps([{'module':m,'name':n,'audit':'generated-C ownership/extraction; invisible to kernel #print'} for m,n in sorted(set(extras))],indent=2)+'\n')
items=sorted(set(items));extras=sorted(set(extras))
# Exact complete audit index; its directives are executed above in memory-bounded batches.
(ROOT/'lean/AxiomAudit.lean').write_text('/- Every directive below is replayed in lean/audit_batches/Axioms*.lean.\nThe batches avoid exceeding the unchanged Lean 4GiB cap. -/\n'+ '\n'.join('import '+m['module'] for m in mods)+'\n\n'+'import Lean.Elab.Command\nopen Lean Elab Command in\nrun_cmd do\n'+'\n'.join('  -- '+n+'\n  elabCommand (← `(#print axioms $(mkIdent '+expressions[n]+')))' for m,t,n in items)+'\n')
(LOGS/'axiom_summary.json').write_text(json.dumps({'kernel_constants':len(items),'theorems':sum(t=='theorem' for m,t,n in items),'codegen_only_names':len(extras),'nonstandard':[],'used_axioms':sorted(all_axioms),'allowed':['propext','Classical.choice','Quot.sound'],'ownership':'actual const2ModIdx with per-module imports, private/generated included','replay':'each #print directive in master lean/AxiomAudit.lean executed in memory-bounded own-module batches','lean_memory_cap_mib':4096},indent=2)+'\n')
print(f'AXIOM AUDIT PASS: {len(items)} kernel constants, {len(extras)} codegen-only names inventoried; all module ownership checked.')
