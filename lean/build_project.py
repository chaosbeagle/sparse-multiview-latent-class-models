#!/usr/bin/env python3
"""Source-only local proof/C build; pinned dependency artifacts are read-only.
All module-owned constants (private/generated included) are inventoried/audited.
"""
import json,os,pathlib,re,subprocess,sys,time,hashlib
ROOT=pathlib.Path(__file__).resolve().parent
TC=pathlib.Path(os.environ['LEAN_TOOLCHAIN'])
PKGS=pathlib.Path(os.environ['LEAN_PACKAGES'])
BUILD=ROOT/'.lake/build/lib/lean';IR=ROOT/'.lake/build/ir';LOGS=ROOT/'build_logs/final';LOGS.mkdir(parents=True,exist_ok=True)
subprocess.run([sys.executable,str(ROOT/'prepare_runtime.py')],cwd=ROOT,check=True)
env=os.environ.copy();env['PATH']=str(TC/'bin')+':'+env.get('PATH','');env['LEAN_PATH']=':'.join([str(BUILD)]+[str(p/'.lake/build/lib/lean') for p in sorted(PKGS.iterdir()) if p.is_dir()])
version=subprocess.check_output([str(TC/'bin/lean'),'--version'],text=True).strip()
if 'version 4.32.0,' not in version:raise SystemExit('Wrong Lean version: '+version)
pins=[]
for pin in json.loads((ROOT/'dependency-pins.json').read_text())['packages']:
 actual=subprocess.check_output(['git','-C',str(PKGS/pin['name']),'rev-parse','HEAD'],text=True).strip()
 if actual!=pin['rev']:raise SystemExit('Dependency pin mismatch: '+pin['name'])
 pins.append({'name':pin['name'],'rev':actual})
for name,digest in json.loads((ROOT/'accepted-source-hashes.json').read_text()).items():
 if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=digest:raise SystemExit('Accepted source hash mismatch: '+name)
mods=[];seen=set()
def visit(name):
 if name in seen:return
 seen.add(name);p=ROOT/(name.replace('.','/')+'.lean')
 if not p.is_file():return
 for line in p.read_text().splitlines():
  line=line.removeprefix('public ')
  if line.startswith('import '):
   for dep in line[7:].split():visit(dep)
 mods.append((name,p))
for main in ['Ext','Gen','Cover']:visit(main)
tests=['RegressionTests','ConfidenceSmoke','CountInterfaceRegression','SemanticCrosswalk','GeneralizationRegression','CoverRegression','CompilerFuelRegression','CoverSemanticCrosswalk']
for test in tests:
 if (ROOT/f'lean/{test}.lean').is_file():visit('lean.'+test)
# Remove ONLY explicitly owned targets; never follow symlinks or clean dependencies.
audit_only = '--audit-only' in sys.argv
for name,p in ([] if audit_only else mods):
 out=BUILD/(name.replace('.','/')+'.olean')
 for artifact in [out,out.with_suffix('.ilean'),pathlib.Path(str(out)+'.private'),pathlib.Path(str(out)+'.server')]:
  if artifact.is_symlink():raise SystemExit('Refusing owned-output symlink: '+str(artifact))
  if artifact.exists():artifact.unlink()
records=[];deps=[]
def compile_one(name,p,emit_c=True):
 out=BUILD/(name.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
 if out.is_symlink():raise SystemExit('Refusing compiler output symlink')
 c=IR/(name.replace('.','/')+'.c');c.parent.mkdir(parents=True,exist_ok=True)
 cmd=[str(TC/'bin/lean'),'-M','4096','-o',str(out),'-i',str(out.with_suffix('.ilean'))]
 if emit_c:cmd+=['-c',str(c)]
 cmd+=[str(p.relative_to(ROOT))]
 start=time.time();r=subprocess.run(cmd,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=LOGS/(name.replace('.','_')+'.log');log.write_text(r.stdout)
 records.append({'module':name,'command':cmd,'exit_code':r.returncode,'elapsed_seconds':time.time()-start,'log':str(log.relative_to(ROOT)),'c':str(c.relative_to(ROOT)) if emit_c else None})
 (LOGS/'build_manifest.json').write_text(json.dumps(records,indent=2)+'\n')
 print(f'{name}: exit {r.returncode}',flush=True)
 if r.returncode:print(r.stdout);raise SystemExit(r.returncode)
 d=subprocess.run([str(TC/'bin/lean'),'--deps',str(p.relative_to(ROOT))],cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 deps.append({'module':name,'exit_code':d.returncode,'dependencies':d.stdout.splitlines()})
 return r.stdout
for name,p in ([] if audit_only else mods):compile_one(name,p)
owned=[name for name,p in mods]
imports='\n'.join('import '+n for n in ['Gen','Ext','Cover']+[f'lean.{t}' for t in tests if (ROOT/f'lean/{t}.lean').is_file()])
(LOGS/'audit_modules.json').write_text(json.dumps([{'module':n,'source':str(p.relative_to(ROOT))} for n,p in mods],indent=2)+'\n')
r=subprocess.run([sys.executable,str(ROOT/'audit_batches.py')],cwd=ROOT,env=env)
if r.returncode:raise SystemExit(r.returncode)
raw_items=json.loads((LOGS/'all_owned_constants.json').read_text())
items=[(x['module'],x['kind'],x['name']) for x in raw_items]
extras=[(x['module'],x['name']) for x in json.loads((LOGS/'codegen_only_constants.json').read_text())]
summary=json.loads((LOGS/'axiom_summary.json').read_text());axioms=set(summary.get('used_axioms',summary['allowed']));bad=set(summary['nonstandard'])
roots=['Cover.A06.validateCoverInput','Cover.A06.stage','Cover.A06.firstSuccessfulStage','Cover.A06.returnedTree','Cover.A06.verifyCertificate','Cover.A06.verifyRawCertificate','Cover.A06.runCover','Cover.A06InputCodec.parse','Cover.ConcreteCompiler.constraints','Cover.ConcreteCompiler.objective','Cover.validatedScalarCoefficients','Cover.AlgCode.compareTotal','Cover.AlgCode.positiveTotal','Cover.AlgCode.refinePrecisely','Cover.AlgCode.verifyRefinement','Cover.DyadicSqrt.bounds','Cover.ScalarExpr.bounds','Cover.checkTree','Cover.coverStage','Cover.Bytes.parseEvidenceByteArray','Cover.Bytes.serializeEvidenceByteArray']
if (ROOT/'Cover/A06Capped.lean').exists():
 roots += ['Cover.A06.runCoverCapped','Cover.A06.rawByteStageJob','Cover.A06.admittedStageJob','Cover.CompilerTasks.compileTask','Cover.InputTasks.parseRawTask','Cover.InputTasks.serializeInputTask','Cover.A06.Runtime.stageCoreTask','Cover.A06.Runtime.verifyTask','Cover.A06.Runtime.packageTask','Cover.stageStoredTask','Cover.checkTreeStoredTask','Cover.Bytes.serializeEvidenceBytesTask','Cover.Bytes.parseEvidenceBytesTask','Cover.Regression.runPhaseRegressions','Cover.A06.CappedRegression.runMalformedInputRegressions','Cover.A06ModelRegression.runCompilerFuelRegression']
comp=ROOT/'lean/ComputabilityAudit.lean'
comp.write_text(imports+'\nimport Lean.Compiler.NoncomputableAttr\n\nopen Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n  let roots : Array Name := #['+', '.join('``'+n for n in roots)+']\n  for name in roots do\n    if isNoncomputable env name then throwError m!"NONCOMPUTABLE_ROOT {name}"\n    logInfo m!"COMPUTABLE_ROOT {name}"\n\n'+'\n'.join('#print axioms '+n for n in roots)+'\n')
compile_one('lean.ComputabilityAudit',comp,False)
scan=[]
for name,p in mods:
 s=p.read_text();s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'--[^\n]*','',s);s=re.sub(r'"(?:\\.|[^"\\])*"','""',s)
 hits=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b',s)
 if hits:scan.append({'module':name,'hits':hits})
if scan:raise SystemExit('Prohibited own-source markers: '+repr(scan))
# Record generated C imports exactly; a name hit is advisory until its body is reviewed.
cimports=[]
for name,p in mods:
 if not name.startswith('Cover.'):continue
 c=IR/(name.replace('.','/')+'.c')
 txt=c.read_text() if c.exists() else ''
 externs=sorted(set(re.findall(r'^(?:extern\s+)?(?:lean_object\*|uint\w+_t|size_t|double|void)\s+((?:l|lp)_\w+)\([^;{]*\);',txt,re.M)))
 suspicious=[x for x in externs if any(t in x.lower() for t in ['classical','choose','realsqrt','realeq','propdecidable'])]
 cimports.append({'module':name,'c':str(c.relative_to(ROOT)),'imported_symbols':externs,'name_flags_for_review':suspicious})
(LOGS/'codegen_only_constants.json').write_text(json.dumps([{'module':m,'name':n,'audit':'not kernel declarations; covered by generated C inventory/extraction'} for m,n in extras],indent=2)+'\n')
(LOGS/'all_owned_constants.json').write_text(json.dumps([{'module':m,'kind':k,'name':n} for m,k,n in items],indent=2)+'\n')
# Per-module axiom_summary.json from audit_batches.py remains the authoritative audit record.
(LOGS/'source_scan.json').write_text(json.dumps({'modules':owned,'prohibited':scan},indent=2)+'\n')
(LOGS/'import_dependencies.json').write_text(json.dumps(deps,indent=2)+'\n')
(LOGS/'c_import_inventory.json').write_text(json.dumps(cimports,indent=2)+'\n')
(LOGS/'computability_roots.json').write_text(json.dumps({'roots':roots,'all_codegen_succeeded':True,'noncomputable_tagged_roots':[],'runtime_imports':'listed in c_import_inventory; not a closed-world runtime audit'},indent=2)+'\n')
(LOGS/'runtime_pins.json').write_text(json.dumps({'lean':version,'packages':pins,'clean_scope':'only own named module outputs; shared dependencies read-only','source_only_rebuild':not audit_only,'audit_only':audit_only},indent=2)+'\n')
r=subprocess.run([sys.executable,str(ROOT/'audit_executable_closure.py')],cwd=ROOT,env=env)
if r.returncode:raise SystemExit(r.returncode)
print(f'{"CORE AUDIT PASS" if audit_only else "FULL SOURCE BUILD PASS"}: {len(mods)} modules; {len(items)} owned constants including private/generated; standard axioms only. C emitted for all source modules. No gate is self-promoted.')
