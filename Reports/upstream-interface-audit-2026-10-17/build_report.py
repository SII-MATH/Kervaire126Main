"""Read-only report generator. Does not rewrite interfaces or proof registries."""
from pathlib import Path
from collections import Counter, deque
from datetime import datetime, timezone, timedelta
import gzip
import hashlib
import html
import json
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parent
SLUGS = ['spectral-sequence', 'adams-synthetic', 'literature', 'computation', 'proof-tools']
MODS = ['SpectralSequence', 'AdamsSynthetic', 'Literature', 'Computation', 'ProofTools']
TARGET = 'KIP126.Main.h6_sq_permanent'

def read(p):
    return json.loads((ROOT / p).read_text())

def dump(p, data):
    (OUT / p).write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n')

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def bfs(graph, root):
    parent = {root: None}
    q = deque([root])
    while q:
        n = q.popleft()
        for v in graph.get(n, {}).get('dependencies', []):
            if v not in parent:
                parent[v] = n
                q.append(v)
    return parent

def path(parent, n):
    result = []
    while n is not None:
        result.append(n)
        n = parent[n]
    return result[::-1]

def norm(s):
    return s.replace('KIP126.Def.', 'KIP126.')

# A retained successful full-body observer is the only available Main kernel graph.
# Its date and incompatible source state are deliberately not relabeled as current.
historical_path = Path('/tmp/Main-Actual-Dependency-Graph-Production-After.json')
historical_bytes = historical_path.read_bytes() if historical_path.exists() else gzip.decompress((OUT/'historical-main-kernel-graph.json.gz').read_bytes())
historical = json.loads(historical_bytes)
old_graph = {r['name']: r for r in historical['nodes']}
old_parent = bfs(old_graph, TARGET)
old_reach = set(old_parent)
old_user_parent = {}
for n in old_parent:
    if n in old_graph:
        old_user_parent.setdefault(old_graph[n]['user_name'], n)

capture_path = OUT/'upstream-kernel-capture.json'
capture_bytes = capture_path.read_bytes() if capture_path.exists() else gzip.decompress((OUT/'upstream-kernel-capture.json.gz').read_bytes())
capture = json.loads(capture_bytes)
now = {r['name']: r for r in capture}
# Independent graph check: propagate direct holes backward through type/body edges.
reverse = {}
for r in capture:
    for dep in set(r['dependencies']): reverse.setdefault(dep, []).append(r['name'])
hole_reach = {r['name'] for r in capture if r['direct_sorry']}
q = deque(hole_reach)
while q:
    for consumer in reverse.get(q.popleft(), []):
        if consumer not in hole_reach:
            hole_reach.add(consumer)
            q.append(consumer)
allapi = {}
apis = {}
caps = {}
manifests = {}
for slug, mod in zip(SLUGS, MODS):
    apis[mod] = read(f'metadata/{slug}-api.json')
    caps[mod] = {c['id']: c for c in read(f'metadata/{slug}-contracts.json')['capabilities']}
    manifests[mod] = read(f'metadata/{slug}-sources.json')
    for r in apis[mod]['declarations'] + apis[mod]['generated_declarations']:
        allapi[r['name']] = r

materials = {
 'ss': dict(title='谱页、滤过、收敛和 ESS', refs=[
  ['AimPaper §§2、4–5', '../../AimPaper/main.tex'],
  ['Ravenel, Complex cobordism and stable homotopy groups of spheres', 'https://doi.org/10.1090/chel/347'],
  ['固定 mathlib 源码', '../../.lake/packages/mathlib/Mathlib/Algebra/Homology/SpectralSequence/Basic.lean']],
  check='检查页号、Z/B 商、共同 Z∞ 代表及 E∞ 非零；收敛必须指向指定滤过，ESS 的微分解释须保留 bounded/projective 等完整前提。抽象结构的声明只规定数据，并不构造真实 Adams 谱序列。'),
 'background': dict(title='固定范畴、ν、Adams 塔与来源识别', refs=[
  ['Pstrągowski, Synthetic spectra and the cellular motivic category', 'https://arxiv.org/abs/1803.01804'],
  ['BHS, On the boundaries… §9 / Appendix A', 'https://arxiv.org/abs/1910.14116'],
  ['source-identification 契约', '../../metadata/adams-synthetic-contracts.json']],
  check='必须构造同一个普通源球、HF₂ 单位、塔、ν 与恢复比较；范畴存在性、sourceRecognition、Milnor d²=0 和 E₂ 标准类标定仍须真实证明。文献中的完成对象不能直接当作当前普通对象。'),
 'synthetic': dict(title='λ 商、乘法、移位与合成/经典比较', refs=[
  ['AimPaper §§3–5', '../../AimPaper/main.tex'],
  ['BHS §9, Theorem 9.19 / Appendix A', 'https://arxiv.org/abs/1910.14116'],
  ['Pstrągowski 原文', 'https://arxiv.org/abs/1803.01804']],
  check='核对同一 λ 幂余纤维、双移位同构、实际乘法、检测标签和权重约定；有限 λ 商与未截断对象须区分，E∞ 同构不自动给同伦群同构。'),
 'bx': dict(title='BJM–Burklund–Xu 归纳判据', refs=[
  ['Burklund–Xu §7.2, Theorem 7.15 / Proposition 7.19', 'https://arxiv.org/html/2302.11869v3#S7.SS2'],
  ['AimPaper Theorem 7.3 / Remark θ₅ choice，约 main.tex:2117–2141', '../../AimPaper/main.tex']],
  check='先固定同一个 θ₅，并证明所需阶二条件；ηθ₅² 与 ληθ₅² 版本之间还有 λ-torsion/次数比较。原始选定类判据不能直接替代 Main 的任意选择不变性，也不能把当前主定理本身作为上游证据。'),
 'classical': dict(title='经典 θ₅、Hopf 类及 realization', refs=[
  ['Xu, The Strong Kervaire invariant problem in dimension 62', 'https://arxiv.org/abs/1410.6199'],
  ['Isaksen–Wang–Xu, Stable homotopy groups of spheres: from dimension 0 to 90', 'https://doi.org/10.1007/s10240-023-00139-1'],
  ['AimPaper 引文与原始条件', '../../AimPaper/main.bib']],
  check='区分普通 π₆₂ 与其 2-primary 部分；检测一个 mod-2 标签不等于消除了奇挠不定性。选定 θ₅ 的阶二及 realization-kernel 为独立责任，不能由全部 E∞ 层为零直接推出。'),
 'tmf': dict(title='tmf、消失线与经典范围', refs=[
  ['Bruner–Rognes, The Adams spectral sequence for topological modular forms', 'https://doi.org/10.1090/surv/253'],
  ['AimPaper main.bib：BR21 / Adams58 / Adams60', '../../AimPaper/main.bib'],
  ['同一 tmf 源、单位及比较的契约', '../../metadata/literature-contracts.json']],
  check='tmf 范畴对象、代数单位及 κ̄⁴w 标签须与原计算一致；tmf 收敛的封装已补不代表这些输入已构造。经典消失线与 d₂(hᵢ) 须核对范围和源/目标次数。'),
 'may': dict(title='May TC3、三角与符号', refs=[
  ['May, The additivity of traces in triangulated categories', 'https://doi.org/10.1006/aima.2001.1995'],
  ['AimPaper main.bib：May01', '../../AimPaper/main.bib'],
  ['Literature.May 实现', '../../KIP126/Literature/May.lean']],
  check='必须是指定移位/张量/余纤维的实际三角与 push-pull 方块；符号由交换约束决定，去掉负号需要实际像上的指数二条件。仅有三角公理不能伪造首项标签。'),
 'moss': dict(title='Moss、Toda 与高阶不定性', refs=[
  ['Moss, Secondary compositions and the Adams spectral sequence', 'https://doi.org/10.1007/BF01129978'],
  ['AimPaper main.bib：Moss', '../../AimPaper/main.bib'],
  ['Literature Moss / Toda 契约', '../../metadata/literature-contracts.json']],
  check='保留定义系、相邻乘积为零、弱收敛和 no-crossing 假设，以及全部 Massey/Toda 不定性。一个被检测标签不能代替指定同伦代表或保证其阶二。'),
 'computation': dict(title='计算表、机器证明及标准类比较', refs=[
  ['AimPaper Appendix：122≤t−s≤127, s≤25；§7 各 Fact', '../../AimPaper/main.tex'],
  ['Lin–Wang–Xu, Machine Proofs…', 'https://arxiv.org/abs/2412.10876'],
  ['Zenodo 数据（仓库书目记录）', 'https://doi.org/10.5281/zenodo.14272279'],
  ['SSeqCpp 原程序', 'https://github.com/WayneLin92/SSeqCpp'],
  ['仓库逐分支审查', '../../Sources/Reviews/SS-all-results-2026-10-16/final-review.txt']],
  check='E₂ 线性代数、微分、乘积与永久存活是不同证据层。必须验证归档数据→同一实际球页的比较、hᵢ 标定及每项推导的前提；level 9000 只能解释为到页 1000，不能自行推出永久存活。机器日志的递归代表同步、搜索正确性及有限→经典推广仍有审查责任。'),
 'tools': dict(title='stretching、广义 Leibniz / Mahowald 与公共操作', refs=[
  ['AimPaper §6，Theorems 6.1 / 6.12、stretching 推论', '../../AimPaper/main.tex'],
  ['ProofTools 逐声明迁移与原始缺口', '../../metadata/proof-tools-sources.json'],
  ['零层 ν-MH2 专项核对', '../../Sources/Reviews/MH2-cw49-2026-10-16/conclusions.txt']],
  check='工具的真实前提包括页/长度界、共同有限商、源/目标可见性、完整目标不定性及 no-crossing。一般 GL/MH2 各有直接 sorry；历史 Main 已改接零层 ν 余纤维特例，但表格生成曾使用一般工具，逻辑上未引用一般工具不消除外部计算认证责任。'),
}

def family(r):
    mod, name, src = r['responsibility_owner'], r['name'].lower(), r['source'].lower()
    if mod == 'SpectralSequence': return 'ss'
    if mod == 'Computation': return 'computation'
    if mod == 'ProofTools': return 'tools'
    if mod == 'AdamsSynthetic':
        return 'background' if any(x in src for x in ['background', '/source', '/system', '/tower', '/filtration', '/standard.lean']) else 'synthetic'
    if any(x in name + src for x in ['bx', 'burklund', 'finiteliftcriterion', 'bxTheta'.lower()]): return 'bx'
    if any(x in name + src for x in ['tmf', 'br21', 'spherevanishing', 'sphere_vanishing', 'classicalrange', 'hopf_differential']): return 'tmf'
    if '/may' in src or 'may_' in name or 'maystructure' in name or 'tc3' in name: return 'may'
    if any(x in name + src for x in ['moss', 'toda', 'secondary']): return 'moss'
    if any(x in name + src for x in ['einfinity', 'bhs', 'lift', 'applicability', 'triangles', 'rigidity', 'weights_', 'inversion_', 'selected_filtration', 'nucofiber', 'quotient', 'lambda_']): return 'synthetic'
    return 'classical'

def frontier(graph, root):
    q, seen, result = [root], set(), set()
    while q:
        n = q.pop()
        if n in seen: continue
        seen.add(n)
        row = graph.get(n)
        if not row: continue
        if not norm(row['module']).startswith('KIP126.Main'):
            result.add(n)
        else:
            q.extend(row['dependencies'])
    return result

boundary = frontier(old_graph, TARGET)
rows, generated, drift = [], [], []
for mod in MODS:
    for cat, dest in [('declarations', rows), ('generated_declarations', generated)]:
        for r0 in apis[mod][cat]:
            r = {k:v for k,v in r0.items() if k not in ['type_consumers','type_dependencies','capability_evidence','universes']}
            n = r['name']
            live = now.get(n)
            if live is None: raise RuntimeError('Missing current upstream export: '+n)
            r['responsibility_owner'] = mod
            r['axioms'] = sorted(live['axioms'])
            r['direct_sorry'] = live['direct_sorry']
            r['strict_clean'] = 'sorryAx' not in live['axioms']
            r['status'] = 'direct' if r['direct_sorry'] else 'clean' if r['strict_clean'] else 'transitive'
            r['line'] = live['line']
            r['full_type'] = live['full_type'] or r0['full_type']
            r['fingerprint_matches_lock'] = live['type_fingerprint'] == r0['type_fingerprint']
            if not r['fingerprint_matches_lock']: drift.append(n)
            r['historical_used'] = n in old_reach
            r['historical_frontier'] = n in boundary
            r['family'] = family(r)
            r['historical_path'] = path(old_parent, n) if r['historical_used'] else []
            r['old_type_same'] = old_graph.get(n, {}).get('type_fingerprint') == live['type_fingerprint'] if n in old_graph else None
            source_record = next((f for f in manifests[mod].get('files', []) if f['path'] == r['source']), {})
            r['origins'] = source_record.get('origins', [])
            r['source_sha256'] = sha(ROOT / r['source'])
            r['capabilities'] = [dict(id=c, purpose=caps[mod][c]['mathematical_purpose']) for c in r0.get('capability_evidence', []) if c in caps[mod]]
            r['graph_has_pending'] = n in hole_reach
            r['pending_examples'] = []
            if r['status'] == 'transitive':
                queue, visited = deque([n]), {n}
                while queue and len(r['pending_examples']) < 5:
                    dep = queue.popleft()
                    node = now.get(dep)
                    if not node: continue
                    if node['direct_sorry']:
                        r['pending_examples'].append(node['source_name'])
                    else:
                        for v in node['dependencies']:
                            if v in hole_reach and v not in visited:
                                visited.add(v)
                                queue.append(v)
            dest.append(r)

def stats(rs):
    return dict(total=len(rs), local_clean=sum(not r['direct_sorry'] for r in rs),
                strict_clean=sum(r['strict_clean'] for r in rs), direct=sum(r['direct_sorry'] for r in rs),
                transitive=sum(r['status']=='transitive' for r in rs))

summary = {}
for grp in ['used', 'unused', 'all']:
    select = lambda r: grp == 'all' or r['historical_used'] == (grp == 'used')
    pool = [r for r in rows if select(r)]
    summary[grp] = dict(total=stats(pool), modules={m:stats([r for r in pool if r['responsibility_owner']==m]) for m in MODS},
        theorems=stats([r for r in pool if r.get('source_kind') in ['theorem','lemma','alias']]),
        fixed=stats([r for r in pool if r.get('directly_callable')]),
        generated=stats([r for r in generated if select(r)]))

obligations = read('metadata/proof-obligations.json')
pending = [r for r in capture if r['direct_sorry']]
registry = {r['name']: r for r in obligations['obligations']}
unregistered = [r['name'] for r in pending if r['name'] not in registry]
missing = [n for n in registry if n not in now or not now[n]['direct_sorry']]
private_pending = [dict(name=r['name'], source_name=r['source_name'], module=r['module'], line=r['line'],
    historical_used=r['name'] in old_reach or r['source_name'] in old_user_parent,
    source=r['module'].replace('.','/')+'.lean') for r in pending if r['name'] not in {x['name'] for x in rows}]
history_holes = [r for n,r in old_graph.items() if n in old_reach and (r['body_has_sorry'] or r['type_has_sorry'])]
snap = read(OUT.relative_to(ROOT) / 'snapshot-inputs.json')
changed = [p for p,h in snap['files'].items() if not (ROOT/p).exists() or sha(ROOT/p)!=h]
final_snap = read(OUT.relative_to(ROOT) / 'snapshot-before-final-build.json')
final_changed = [p for p,h in final_snap['files'].items() if not (ROOT/p).exists() or sha(ROOT/p)!=h]
valid = dict(upstream_capture=True, type_lock_drift=drift, unregistered=unregistered,
             registry_missing=missing, source_changed_during_audit=changed,
             source_changed_since_final_build_snapshot=final_changed,
             upstream_changed_during_audit=[p for p in changed if not p.startswith('KIP126/Main/')],
             final_build_log_time=datetime.fromtimestamp((Path('/tmp/k126-report-final-build.log') if Path('/tmp/k126-report-final-build.log').exists() else OUT/'build.log').stat().st_mtime, timezone(timedelta(hours=8))).isoformat(timespec='seconds'),
             graph_axioms_disagreement=[r['name'] for r in rows+generated if r['graph_has_pending']==r['strict_clean']],
             project_axioms=[r['name'] for r in capture if r['is_axiom']],
             synthetic_sorry=[r['name'] for r in capture if r['synthetic_sorry']],
             inventory='passed', full_build='failed twice; final failures: High125.Detector, High125.Filtration, WeakRepresentative, Theta.RealizationKernel', main_capture='failed: missing High125.Filtration.olean')
data = dict(created=datetime.now(timezone(timedelta(hours=8))).isoformat(timespec='seconds'),
    head=snap['head'], target=TARGET, summary=summary, rows=rows, generated=generated,
    pending=dict(total=len(pending), by_module=dict(Counter(r['module'].split('.')[1] for r in pending)),
                 private=private_pending, historical_total=len(history_holes)),
    historical=dict(date='2026-10-16 13:10 UTC / 21:10 北京时间',
        source=str(historical_path), sha256=hashlib.sha256(historical_bytes).hexdigest(), reachable_project=len(set(old_graph)&old_reach),
        interpretation='历史内核图用于分组；每行证明状态由当前上游重新捕获。当前 Main 未通过编译，分组不能当作当前有效证明依赖闭包。'),
    validation=valid, materials=materials)
dump('audit-data.json', data)
dump('validation.json', valid)
for source, target in [('/tmp/k126-report-final-build.log','build.log'),('/tmp/k126-report-inventory.log','inventory.log'),
        ('/tmp/k126-report-upstream-capture.log','upstream-capture.log'),('/tmp/k126-report-capture.log','main-capture.log')]:
    if Path(source).exists(): shutil.copyfile(source, OUT/target)
for content, target in [(historical_bytes,'historical-main-kernel-graph.json.gz'),
        (capture_bytes,'upstream-kernel-capture.json.gz')]:
    with gzip.open(OUT/target,'wb') as f: f.write(content)

def table(grp):
    result = '<div class="scroll"><table><thead><tr><th>模块</th><th>接口</th><th>自身无 sorry</th><th>依赖也无 sorryAx</th><th>直接占位</th><th>仅传递待补</th></tr></thead><tbody>'
    for mod, s in list(summary[grp]['modules'].items()) + [('合计',summary[grp]['total'])]:
        result += '<tr>'+''.join('<td>'+html.escape(str(x))+'</td>' for x in [mod,s['total'],s['local_clean'],s['strict_clean'],s['direct'],s['transitive']])+'</tr>'
    return result+'</tbody></table></div>'

used, unused = summary['used']['total'], summary['unused']['total']
PAGE = r'''<!doctype html>
<html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>h₆² 主定理 · 上游接口与来源审计</title>
<style>
:root{--bg:#f5f4ef;--ink:#16272a;--muted:#58696b;--line:#d9ded8;--green:#127263;--orange:#ad5d16;--red:#9c3437;--paper:#fffefa}
*{box-sizing:border-box}html{scroll-behavior:smooth}body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.75 system-ui,-apple-system,"Noto Sans CJK SC","Microsoft YaHei",sans-serif}a{color:var(--green);text-underline-offset:3px}header{padding:60px max(5vw,24px) 42px;background:#183a3c;color:#f9f6e9}header .eyebrow{font-size:12px;letter-spacing:.16em;color:#b4d3c6}h1{font-size:clamp(30px,4.5vw,58px);line-height:1.22;font-weight:650;max-width:1050px;margin:18px 0}header p{max-width:900px;color:#d1dfd4}header code{color:#d1e8d8}nav{position:sticky;top:0;z-index:5;display:flex;gap:22px;padding:12px max(5vw,24px);background:rgba(255,254,250,.96);border-bottom:1px solid var(--line);overflow:auto;white-space:nowrap}nav a{text-decoration:none;color:var(--ink);font-size:13px}main{max-width:1360px;margin:0 auto;padding:30px 4vw 70px}section{margin:34px 0 60px;scroll-margin-top:72px}h2{font-size:27px;letter-spacing:-.03em;margin:0 0 12px}h3{font-size:18px;margin:20px 0 10px}.kicker{font-size:12px;letter-spacing:.15em;color:var(--green);font-weight:700}.note,.danger{padding:20px 24px;border-left:4px solid var(--orange);background:#fff4df;margin:20px 0}.danger{border-color:var(--red);background:#f9e9e5}.small,small{font-size:12px;color:var(--muted)}.metrics{display:grid;grid-template-columns:repeat(4,1fr);gap:15px;margin:24px 0}.metric{padding:20px;background:var(--paper);border:1px solid var(--line);border-radius:7px}.metric strong{display:block;font-size:36px;line-height:1.4;letter-spacing:-.04em}.metric span{font-size:12px;color:var(--muted)}.panels{display:grid;grid-template-columns:1fr 1fr;gap:24px}.card{background:var(--paper);border:1px solid var(--line);padding:24px;border-radius:8px}.scroll{overflow:auto}table{width:100%;border-collapse:collapse;background:var(--paper);font-size:13px}th{text-align:left;background:#e9eee8;font-size:12px;white-space:nowrap}th,td{padding:12px;border-bottom:1px solid var(--line);vertical-align:top}tbody tr:last-child{font-weight:650}code,pre{font-family:ui-monospace,"SFMono-Regular",Consolas,monospace;font-size:12px;overflow-wrap:anywhere}pre{white-space:pre-wrap;background:#eef1eb;padding:18px;border-radius:5px;max-height:450px;overflow:auto}.tag{display:inline-block;padding:2px 8px;border-radius:4px;font-size:11px;background:#e6eee8;color:#30594e}.tag.direct{background:#fbe6df;color:var(--red)}.tag.transitive{background:#fff0d5;color:#8a5b16}.tag.clean{background:#dceee6;color:#176653}.filters{display:flex;gap:10px;flex-wrap:wrap;margin:20px 0;padding:15px;background:#e9eee8;border-radius:7px}input,select,button{font:inherit;font-size:13px;border:1px solid #c6d0c8;border-radius:4px;padding:9px 12px;background:var(--paper);color:var(--ink)}input{flex:1;min-width:210px}button{cursor:pointer}button:hover{background:#e3eee5}details.interface{border-bottom:1px solid var(--line);background:var(--paper)}details.interface>summary{cursor:pointer;display:grid;grid-template-columns:1fr auto;gap:15px;padding:16px 18px;list-style:none}summary .name{font:12px/1.6 ui-monospace,Consolas,monospace;overflow-wrap:anywhere}summary .meta{font-size:11px;color:var(--muted)}.details-body{padding:0 22px 22px}.details-body p{font-size:13px}.path{border-left:2px solid #c4d8cc;padding-left:14px;list-style:none;font:11px/1.8 ui-monospace,monospace;overflow-wrap:anywhere}.material{margin-bottom:15px}.material p{font-size:13px}.diagram{display:grid;grid-template-columns:repeat(3,1fr);gap:12px}.diagram div{border:1px solid #b7cfc4;padding:16px;background:#ecf3ed;border-radius:6px}.legend{display:flex;gap:18px;flex-wrap:wrap;font-size:12px}.countline{display:flex;justify-content:space-between;gap:15px;margin:12px 0}.empty{padding:30px;text-align:center;color:var(--muted)}footer{border-top:1px solid var(--line);margin-top:40px;padding-top:22px;font-size:12px;color:var(--muted)}.bars{display:flex;height:12px;background:#e4e8e1;border-radius:3px;overflow:hidden}.bars .clean{background:#338b76}.bars .transitive{background:#e7b65f}.bars .direct{background:#b35f57}.family-grid{display:grid;grid-template-columns:1fr 1fr;gap:18px}#material-list .card h3{margin-top:0}.section-lede{max-width:920px;color:var(--muted)}@media(max-width:800px){.metrics{grid-template-columns:1fr 1fr}.panels,.family-grid,.diagram{grid-template-columns:1fr}header{padding-top:38px}main{padding-left:20px;padding-right:20px}.metric strong{font-size:30px}details.interface>summary{grid-template-columns:1fr}.filters{padding:10px}th,td{padding:9px}}@media print{nav,.filters,.paging{display:none}header{color:#000;background:white;padding:20px}header p,header code{color:#333}main{padding:0}.card,.metric{break-inside:avoid}body{background:white}details.interface{break-inside:avoid}section{margin-bottom:25px}}
</style></head><body>
<header><div class="eyebrow">KERVAIRE 126 · INTERFACE EVIDENCE REVIEW</div>
<h1>h₆² 主定理的上游接口<br>证明状态 · 正确性 · 来源</h1>
<p>目标：固定经典球 Adams 谱序列中，标准乘积 h₆·h₆ 在 (s,t) = (2,128) 的非零永久存活。主入口 <code>KIP126.Main.h6_sq_permanent</code>；几何流形存在性不在本次 Lean 终点内。</p>
<div class="small" style="color:#b6cec3">__TIME__ · HEAD __HEAD__ · 当前工作区含未提交改动</div></header>
<nav><a href="#verdict">结论与口径</a><a href="#needed">主链内接口</a><a href="#outside">主链外接口</a><a href="#correctness">正确性与风险</a><a href="#catalog">逐项清单</a><a href="#sources">来源索引</a><a href="#reproduce">验证与复现</a></nav>
<main><section id="verdict"><div class="kicker">01 / READING THE NUMBERS</div><h2>本次 Main 构建失败，当前依赖闭包尚未重新认证</h2>
<div class="danger"><strong>本次实际运行完整 lake build：失败。</strong>最终复测的四处失败模块：<code>Main.Internal.High125.Detector</code>、<code>Main.Internal.High125.Filtration</code>、<code>Main.SectionSeven.WeakRepresentative</code>、<code>Main.Internal.Theta.RealizationKernel</code>。构建时 Main 仍有旧调用；完整内核依赖捕获因此也失败。审计期间其他任务继续修复 Main；随后进行了第二次完整构建，以上为复测结果（__BUILDTIME__）。上游状态另行重新捕获，Main 在修复期间的源码漂移按指纹记录。<a href="build.log">构建日志</a> · <a href="main-capture.log">主链捕获日志</a></div>
<p>为仍能给出可核对的两组完整清单，本报告采用<strong>2026-10-16 最近留存的成功 Main 内核图分组</strong>，并对<strong>当前五个上游模块重新捕获证明状态</strong>。两种时间口径始终分开：下列“主链内 / 主链外”均指历史内核图中的可达性，绝不表示当前未编译源码的精确依赖或未依赖结论。完成 Main 修复后应重新分组。</p>
<div class="metrics"><div class="metric"><span>历史主链内 · 当前命名接口</span><strong>__USED__</strong><span>状态按本次上游捕获更新</span></div><div class="metric"><span>其中依赖也无 sorryAx</span><strong>__USEDCLEAN__</strong><span>当前上游内核公理闭包</span></div><div class="metric"><span>历史主链外 · 当前命名接口</span><strong>__UNUSED__</strong><span>当前是否未依赖仍待复核</span></div><div class="metric"><span>其中依赖也无 sorryAx</span><strong>__UNUSEDCLEAN__</strong><span>当前上游内核公理闭包</span></div></div>
<div class="panels"><div class="card"><h3>什么算一个上游接口？</h3><p>仅统计五份 <code>*-api.json</code> 的 <code>declarations</code>：显式命名公开定义、定理及结构，共 <strong>1503</strong> 项。Main 自己的 17 项不计；mathlib、私有辅助及生成的字段/构造器不混入分母。清单内还可切换“仅定理”或“固定可调用接口”。</p></div><div class="card"><h3>“不含 sorry”给出两个数</h3><p><strong>自身无 sorry</strong>：声明的实际类型与证明/定义体没有占位。<strong>依赖也无 sorryAx</strong>：Lean <code>collectAxioms</code> 的传递结果不含 <code>sorryAx</code>。第二项才排除了间接借用未证明声明；仍允许 Lean 常用的 <code>propext / Classical.choice / Quot.sound</code>。</p></div></div>
<p class="small">历史可达性同时遍历 elaborated type 和 opaque body；一个结构的字段类型也可能引入依赖。因此“依赖”是完整证明项/类型关系，不是手写引文数量，也不是不可替代的数学最小假设集。</p></section>
<section id="needed"><div class="kicker">02 / HISTORICAL MAIN CLOSURE</div><h2>主链内：__USED__ 项；严格无 sorryAx：__USEDCLEAN__ 项</h2><p class="section-lede">自身无占位 __USEDLOCAL__ 项，直接占位 __USEDDIRECT__ 项；还有 __USEDTRANS__ 项自身已写出证明，却仍依赖上游待补。分组是 10 月 16 日历史快照，证明状态是当前值。</p>__USEDTABLE__
<h3>主定理用到的数学层次</h3><div class="diagram"><div><strong>① 固定对象与谱页</strong><br><small>AdamsSynthetic：同一球、ν、HF₂ 单位、塔、标准 h₆ 及其实际乘积。SpectralSequence：页、存活与共同代表。</small></div><div><strong>② 文献、计算与操作</strong><br><small>BX 判据、BHS 比较、realization、Moss/May；122–127 stem 的有限页、微分及基底；零层 ν-MH2 与公共滤过操作。</small></div><div><strong>③ Main 局部推导</strong><br><small>d₁₂ 二分与 C3/C4/C5 判据 → 第七节排除 η-extension → h₆² 非零永久存活。消费者修复需要新的完整构建认证。</small></div></div>
<p>文献判据和计算标签必须绑定同一个固定对象。当前上游构造仍有直接待补，不能因为 Main 最后两步不出现 <code>sorry</code> 就宣布整体形式化完成。历史单根实际可达 __HISTREACH__ 个项目常量、__HISTHOLES__ 个直接占位；这些历史数字不替代当前构建结果。</p><button onclick="showGroup('used')">查看这组全部接口与来源 →</button></section>
<section id="outside"><div class="kicker">03 / OUTSIDE THAT HISTORICAL CLOSURE</div><h2>主链外：__UNUSED__ 项；严格无 sorryAx：__UNUSEDCLEAN__ 项</h2><p class="section-lede">自身无占位 __UNUSEDLOCAL__ 项，直接占位 __UNUSEDDIRECT__ 项，另 __UNUSEDTRANS__ 项含传递待补。这里表示“不在保留的历史证明项中”，并不表示它们无用、错误，或当前重构后一定不会进入主链。</p>__UNUSEDTABLE__
<div class="note"><strong>一般工具与计算来源要分别看。</strong>历史主证明改用 <code>ProofTools.Standard.nuCofiberMahowaldZeroLayer</code>，不直接/递归引用一般 <code>generalizedLeibniz</code> 和 <code>generalizedMahowald</code>。后两者仍各有一个直接占位。外部计算表的生成可能用到一般工具，因此 Lean 依赖图中未引用它们，不能替代表格来源的独立正确性认证。</div>
<p>主链外还包括通用谱序列态射/扩张支撑、未用到的合成/经典比较、额外 Literature 运输与存在性接口，以及计算模块的备用路线。下面的清单按实际声明逐项列出；来源候选与使用条件同样完整展示。</p><button onclick="showGroup('unused')">查看这组全部接口与来源 →</button></section>
<section id="correctness"><div class="kicker">04 / MATHEMATICAL ASSESSMENT</div><h2>形式证明状态和数学适用性是两项检查</h2><p>本次完成上游的内核状态复核、接口指纹比较与重点语义审查；未重新从零证明全部外部定理，也未逐条重放整个机器数据库。每项清单都给出完整签名、证据定位和材料候选；候选材料不等于已经完成从文献到此固定对象的运输证明。</p>
<div class="scroll"><table><thead><tr><th>重点接口 / 问题</th><th>当前判断与理由</th><th>可印证材料 / 尚欠步骤</th></tr></thead><tbody>
<tr><td><code>synthetic_homotopy_separated</code></td><td>当前仅断言实际有限 λⁿ 商的分离性，仍为直接待补。有限商结论不能用于未截断球；n=0 的余纤维零对象边界相容，但不构成一般证明。</td><td>当前 Standard/Separation.lean、BHS 的同一塔/商比较、获批接口审查。必须构造并证明指定商的滤过分离性。</td></tr>
<tr><td><code>classical_sphere_separated</code></td><td>当前结论是无限滤过元素为奇挠；由既有 finite_map_separation 推出，自身无 sorry，传递基础未补。奇挠不能直接改写为零。</td><td>Standard/ClassicalSupport.lean；有限谱的 HF₂-Adams 分离性资料。Main High125 的“=0”消费仍失配。</td></tr>
<tr><td><code>stem62_exponent_two</code></td><td>现在要求同一元素满足 ∃n, 2ⁿa=0，合理排除普通 π₆₂ 的奇挠；仍直接待补。选定 θ₅ 的阶二另有 <code>theta5_order_two</code> 责任。</td><td>IWX 稳定茎计算、Xu 的 62 维结果与来源报告。不能把“被 mod-2 标签检测”自动当作同一 ordinary 元素的 2-primary 证明。</td></tr>
<tr><td>普通球 vs 2 完成球</td><td>AimPaper main.tex:138、254 明确采用 2 完成背景；项目来源识别保留普通球。这是适用范围差异，必须逐条比较，不能把论文的一般分离性或全群阶数照搬。</td><td>本地 AimPaper 原文、当前 Source/Sphere.lean、source-identification 契约及已批准审查。此差异不反驳标准 h₆² 谱页目标本身。</td></tr>
<tr><td>BX / θ₅ 与 Toda</td><td>固定 BX 类的阶二输入和任意被检测代表不同；任意 b 的阶二也不能由 π₆₂ 全群指数二得到。既有审查中的 b 选择与 kernel 论证缺口，须以随后 Main 修复的真实证明重新核验。</td><td>BX §7.2、AimPaper θ₅ choice 备注、Main 作用范围报告。旧通用阶二支路的数学反例只在真实普通对象语义中成立；运输到未完成 Lean 模型仍有条件。</td></tr>
<tr><td>计算表及永久存活</td><td>归档、哈希和 E₂ 算像能印证数据与表达式；它们不会单独证明实际高页微分、无其他 incoming differential 或永久存活。比较对象、标准类、全范围前提均须核验。</td><td>AimPaper Appendix、LWX Machine、Zenodo、SSeqCpp 与 SS-all-results 审查；递归代表粘合、搜索正确性、有限→经典提升应独立认证。</td></tr>
<tr><td>GL / MH2 / stretching</td><td>一般 GL/MH2 未完成；零层特例自身已写出证明但仍有基础依赖。对所有工具，数值界、共同商、crossing 与不定性不能省略。</td><td>AimPaper §6、proof-tools-sources 逐声明原缺口与零层专项证据。历史 Main 已避开一般工具，不代表全部计算生成分支已获证明。</td></tr>
<tr><td>当前无 sorryAx 的通用定理</td><td>在完整 Lean 签名及固定工具链中无需占位，是最强的本次形式证据。对于结构/定义，“无 sorry”只证明定义合法；对带前提定理仍须实际满足前提。</td><td>当前源码 + 本次完整类型/公理捕获。正确性范围限于给定定义，真实谱与文献对象的识别仍需单独检查。</td></tr>
</tbody></table></div>
<h3>第二次完整构建的具体失败点</h3><p><code>High125.Detector:39</code> 仍调用已不存在的 <code>realization_injective_of_lambda_powers</code>；<code>High125.Filtration:76,126</code> 的旧分离性调用仍失配；<code>WeakRepresentative:94</code> 未完成两次 λ²/λ³ 作用与一次 λ⁵ 作用的相容改写；<code>Theta.RealizationKernel:124</code> 仍将有限商分离性用于未截断对象。这些是本次复测定位，后续并发修复可能继续改变状态，详见 <a href="build.log">最终日志</a>。</p>
<p><a href="../../metadata/interface-reviews/approved-upstream-20261017/report.md">已批准上游改动与剩余失败</a> · <a href="../../metadata/interface-reviews/Main/20261017-primary-scope-after-approved-upstream/report.md">Main 具体数学作用范围报告</a> · <a href="../../metadata/interface-reviews/approved-upstream-20261017/evidence/kip-interface-independent-math-audit.md">独立数学核对</a></p></section>
<section id="catalog"><div class="kicker">05 / COMPLETE INTERFACE CATALOG</div><h2>两组完整清单，可逐项展开</h2><p class="small">所有分组均标记历史快照。当前状态来自上游实际内核捕获；“生成声明”另列，不增加 1503 项命名接口的分母。空白文献精确定位表示尚未完成独立原文逐条核对。</p>
<div class="filters"><input id="search" aria-label="搜索接口" placeholder="搜索声明、类型、能力或来源路径…"><select id="group" aria-label="分组"><option value="used">历史主链内</option><option value="unused">历史主链外</option><option value="all">全部</option></select><select id="module" aria-label="模块"><option value="all">全部上游模块</option></select><select id="status" aria-label="证明状态"><option value="all">全部证明状态</option><option value="clean">依赖也无 sorryAx</option><option value="local">自身无 sorry</option><option value="direct">直接占位</option><option value="transitive">仅传递待补</option></select><select id="scope" aria-label="声明口径"><option value="named">命名公共接口</option><option value="theorem">仅定理 / lemma / alias</option><option value="fixed">固定可调用接口</option><option value="frontier">历史 Main 直接边界命名接口</option><option value="generated">生成字段 / 构造器等</option></select></div>
<div class="countline"><span id="count"></span><button id="export">导出当前筛选 JSON</button></div><div id="distribution"></div><div id="list"></div><div class="countline paging"><button id="prev">← 上一页</button><span id="page"></span><button id="next">下一页 →</button></div>
<details class="card"><summary>额外：不属于命名接口的当前直接待补</summary><p>当前上游全部直接占位 __ALLHOLES__ 项；其中 __PRIVATEHOLES__ 项未计入命名接口，含私有构造/辅助。主链分组不应漏掉它们，但也不能把它们算成新的公共承诺。</p><div id="private-pending"></div></details></section>
<section id="sources"><div class="kicker">06 / SOURCE CROSS-CHECKS</div><h2>从哪些材料印证？</h2><p>依照每项声明的用途分为下列材料族。逐项展开中的“代码溯源”来自固定来源清单，保留 commit/path；这些记录证明代码来源，不自行证明数学结论。下列文献/表格是核对入口，精确适用性见完整签名与契约。</p><div id="material-list" class="family-grid"></div>
<div class="note"><strong>证据层次：</strong>内核无占位证明 → 同一对象/前提的文献定理与明确运输 → 可复验的数据/算法证书 → 仅表格/日志 → 仅来源路径或哈希。后两项有溯源价值，不能替代前两项。Zenodo DOI 为本地书目记录，本次网页访问未成功，不声称已经重新下载验证整个数据集。</div>
<p class="small">本次在线核对：LWX 2412.10879v2 的背景与主要定理定位；BX 2302.11869v3 §7.2；BHS 1910.14116 与 Pstrągowski 1803.01804 书目；LWX Machine 2412.10876 摘要。May/Moss/BR21 等 DOI 来自本地 main.bib，未声称阅读全文。当前报告只给“可核对材料”，不为未读全文制造独立验证结论。</p></section>
<section id="reproduce"><div class="kicker">07 / AUDIT TRAIL</div><h2>验证结果与可复现证据</h2><div id="validation"></div>
<p>快照 HEAD：<code>__FULLHEAD__</code>。源树指纹覆盖当前 KIP126 源码、顶层元数据和工具链/依赖锁；报告生成后再次比较，实际差异见 validation.json。没有修改数学源码、公共接口、待补登记、依赖锁，也没有为通过构建添加占位。</p>
<p><a href="audit-data.json">完整逐项数据 JSON</a> · <a href="snapshot-inputs.json">初始源树 SHA-256 清单</a> · <a href="snapshot-before-final-build.json">最终构建前源树清单</a> · <a href="build-initial.log">首次构建日志</a> · <a href="validation.json">验证摘要</a> · <a href="upstream-kernel-capture.json.gz">当前上游内核捕获（gzip）</a> · <a href="historical-main-kernel-graph.json.gz">历史 Main 原始依赖图（gzip）</a> · <a href="ObserveUpstream.lean">只读上游观察器</a> · <a href="ObserveDependencies.lean">Main 观察器（本次受阻）</a> · <a href="build_report.py">报告生成器</a></p>
<pre>python3 scripts/check-source-inventory.py
lake build
lake env lean Reports/upstream-interface-audit-2026-10-17/ObserveUpstream.lean
# Main 修复并完整构建通过后，才可重新运行主链观察器并更新分组。
lake env lean Reports/upstream-interface-audit-2026-10-17/ObserveDependencies.lean</pre>
<p>HTML 已用本地 Chromium 检查两组筛选、搜索、签名展开、状态/生成声明切换与手机宽度，无 JavaScript 错误。<a href="html-check.log">浏览器检查记录</a></p><p class="small">工具链沿用 Lean v4.32.2，mathlib 固定提交 905b95818eb32af7874a58b427f50c1711a5e96c。初始沙箱无法定位工具链，随后在获准环境使用同一安装完成实际构建/捕获；没有升级工具链。此 HTML 无外部脚本/字体依赖，可离线打开；相对链接在保留报告与仓库目录关系时可访问。</p>
</section><footer>本报告的核心限制：两次主定理完整构建均失败，因此无法诚实宣称已取得“当前有效证明的全部依赖 / 全部未依赖”精确二分。提供的是有日期的历史可达性清单，加当前上游真实证明状态和材料分析。Main 修复后，依赖数量可能变化。</footer></main>
<script id="audit-data" type="application/json">__DATA__</script>
<script>
const D=JSON.parse(document.getElementById('audit-data').textContent),$=x=>document.getElementById(x), esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const statuses={direct:'直接占位',transitive:'仅传递待补',clean:'依赖也无 sorryAx'}, mods=['SpectralSequence','AdamsSynthetic','Literature','Computation','ProofTools'];
mods.forEach(m=>$('module').add(new Option(m,m)));
let page=0,filtered=[],size=35;
function selected(){const group=$('group').value,mod=$('module').value,st=$('status').value,sc=$('scope').value,q=$('search').value.toLowerCase();return (sc==='generated'?D.generated:D.rows).filter(r=>(group==='all'||r.historical_used===(group==='used'))&&(mod==='all'||r.responsibility_owner===mod)&&(st==='all'||st==='local'&&!r.direct_sorry||st===r.status)&&(sc!=='theorem'||['theorem','lemma','alias'].includes(r.source_kind))&&(sc!=='fixed'||r.directly_callable)&&(sc!=='frontier'||r.historical_frontier)&&(!q||(r.name+' '+r.full_type+' '+r.source+' '+r.capabilities.map(c=>c.purpose).join(' ')).toLowerCase().includes(q)))}
function link(label,url){return `<a href="${esc(url)}">${esc(label)}</a>`}
function correctness(r){if(r.source_kind&&['structure','class','inductive'].includes(r.source_kind))return '这是类型/结构规格：无占位表示定义合法，不表示已经构造其真实标准实例。';if(r.direct_sorry)return '存在直接占位，当前没有完成此声明的形式构造/证明；材料可用于补证，但不能取代证明。';if(!r.strict_clean)return '本条已有实现/证明，但仍传递依赖 sorryAx，不能归入整体证明完成。';return '当前内核公理闭包无 sorryAx；其结论仅在完整签名、所给定义及全部显式/隐式前提下成立。'}
function detail(r){const m=D.materials[r.family];return `<div class="details-body"><p><strong>正确性判断：</strong>${correctness(r)}</p><p><strong>用途：</strong>${r.capabilities.length?r.capabilities.map(c=>esc(c.purpose)).join('；'):'当前契约未逐条指定能力，按所属源码和完整类型核对。'}</p><p><strong>适用性核对：</strong>${esc(m.check)}</p><p><strong>源码：</strong>${link(r.source+':'+r.line,'../../'+r.source+'#L'+r.line)} · 类型与接口锁 ${r.fingerprint_matches_lock?'一致':'有差异，待审'} · ${r.historical_used?'历史主链内':'历史主链外'}${r.historical_frontier?' · 历史 Main 直接边界':''}</p><p><strong>当前完整签名</strong></p><pre>${esc(r.full_type)}</pre><p><strong>当前公理：</strong><code>${esc(r.axioms.join(', ')||'∅')}</code></p>${r.pending_examples.length?'<p><strong>实际传递待补示例</strong>（至多五项）：<br><code>'+r.pending_examples.map(esc).join('<br>')+'</code></p>':''}<p><strong>可核对材料：</strong>${m.refs.map(x=>link(x[0],x[1])).join(' · ')}</p><p class="small">上述材料是按用途匹配的核对候选，不声称每个声明已获得原文逐条证明；精确代码记录如下。</p><p><strong>代码溯源：</strong>${r.origins.length?r.origins.map(o=>`<code>${esc(o.commit||'')} : ${esc(o.path||'')}</code>`).join('<br>'):'此文件未单独记录旧源；需查看对应模块 sources 清单，不能据此断言有外部证明。'}</p><p class="small">当前文件 SHA-256：<code>${esc(r.source_sha256)}</code></p>${r.historical_used?'<p><strong>历史最短依赖见证</strong>（类型 + opaque body；旧模块路径保留）</p><ol class="path">'+r.historical_path.map(x=>'<li>'+esc(x)+'</li>').join('')+'</ol><p class="small">这条路径属于 2026-10-16 的成功图，尚未获得当前 Main 的重新编译认证。历史类型与本次上游类型指纹：'+(r.old_type_same?'一致；不表示证明体相同':'不同/不可比，须复核')+'。</p>':'<p class="small">历史图中不存在从主根到本声明的可达路径；这是历史阴性证据，不是当前源码的未依赖认证。</p>'}</div>`}
function render(){filtered=selected();page=Math.min(page,Math.max(0,Math.ceil(filtered.length/size)-1));const c=filtered.filter(r=>r.strict_clean).length,l=filtered.filter(r=>!r.direct_sorry).length,t=l-c,a=filtered.length-l;$('count').textContent=`${filtered.length} 项 · 自身无 sorry ${l} · 依赖也无 sorryAx ${c} · 直接占位 ${a}`;$('distribution').innerHTML=`<div class="bars"><span class="clean" style="width:${100*c/(filtered.length||1)}%"></span><span class="transitive" style="width:${100*t/(filtered.length||1)}%"></span><span class="direct" style="width:${100*a/(filtered.length||1)}%"></span></div><div class="legend"><span>绿色：依赖也无占位 ${c}</span><span>黄色：仅传递待补 ${t}</span><span>红色：直接占位 ${a}</span></div>`;$('list').innerHTML=filtered.slice(page*size,(page+1)*size).map(r=>`<details class="interface" data-name="${esc(r.name)}"><summary><div><div class="name">${esc(r.name)}</div><div class="meta">${esc(r.responsibility_owner)} · ${esc(r.source_kind||r.kind)} · ${esc(D.materials[r.family].title)}</div></div><div><span class="tag ${r.status}">${statuses[r.status]}</span></div></summary></details>`).join('')||'<div class="empty">没有符合筛选条件的声明。</div>';$('page').textContent=`第 ${page+1} / ${Math.max(1,Math.ceil(filtered.length/size))} 页`;$('prev').disabled=page===0;$('next').disabled=(page+1)*size>=filtered.length;document.querySelectorAll('details.interface').forEach(el=>el.addEventListener('toggle',()=>{if(el.open&&!el.dataset.loaded){el.insertAdjacentHTML('beforeend',detail(filtered.find(r=>r.name===el.dataset.name)));el.dataset.loaded='1'}}))}
['search','group','module','status','scope'].forEach(id=>$(id).addEventListener(id==='search'?'input':'change',()=>{page=0;render()}));$('prev').onclick=()=>{page--;render();$('catalog').scrollIntoView()};$('next').onclick=()=>{page++;render();$('catalog').scrollIntoView()};window.showGroup=g=>{$('group').value=g;page=0;render();$('catalog').scrollIntoView()};$('export').onclick=()=>{const blob=new Blob([JSON.stringify({note:D.historical.interpretation,created:D.created,rows:filtered},null,2)],{type:'application/json'}),u=URL.createObjectURL(blob),a=document.createElement('a');a.href=u;a.download='upstream-interfaces-'+$('group').value+'.json';a.click();setTimeout(()=>URL.revokeObjectURL(u),500)};
$('private-pending').innerHTML=D.pending.private.map(r=>`<p><code>${esc(r.source_name)}</code><br><small>${link(r.source+':'+r.line,'../../'+r.source)} · ${r.historical_used?'历史图可识别为主链内':'历史图未匹配；不可据此排除当前依赖'}</small></p>`).join('');
$('material-list').innerHTML=Object.values(D.materials).map(m=>`<article class="card material"><h3>${esc(m.title)}</h3><p>${esc(m.check)}</p><p>${m.refs.map(x=>link(x[0],x[1])).join('<br>')}</p></article>`).join('');
const V=D.validation;$('validation').innerHTML=`<div class="scroll"><table><thead><tr><th>检查</th><th>本次结果</th></tr></thead><tbody><tr><td>源码清单与模块边界</td><td>通过，473 项目文件 + 28 消费/审计文件；${link('日志','inventory.log')}</td></tr><tr><td>完整 lake build / Main 内核捕获</td><td><strong>两次均失败；最终四个失败模块见日志，不能宣称当前主定理已验证</strong>；${link('日志','build.log')}</td></tr><tr><td>当前上游全体声明只读捕获</td><td>通过；${link('日志','upstream-capture.log')}</td></tr><tr><td>命名与生成公共接口类型指纹</td><td>${V.type_lock_drift.length?'差异 '+V.type_lock_drift.length:'全部与当前接口锁一致'}</td></tr><tr><td>直接 sorry 与待补登记</td><td>捕获 ${D.pending.total} 项；未登记 ${V.unregistered.length}；登记缺失 ${V.registry_missing.length}</td></tr><tr><td>当前上游项目自建公理 / synthetic sorry</td><td>${V.project_axioms.length} / ${V.synthetic_sorry.length}</td></tr><tr><td>审计期间快照源码漂移</td><td>${V.source_changed_during_audit.length} 文件，清单见 validation.json；另有第二次完整构建复测，见最终日志及其前置快照</td></tr></tbody></table></div>`;
render();
</script></body></html>'''

replace = dict(TIME=data['created'].replace('T',' '), BUILDTIME=valid['final_build_log_time'].replace('T',' '), HEAD=snap['head'][:12], FULLHEAD=snap['head'],
    USED=used['total'],USEDCLEAN=used['strict_clean'],USEDLOCAL=used['local_clean'],USEDDIRECT=used['direct'],USEDTRANS=used['transitive'],
    UNUSED=unused['total'],UNUSEDCLEAN=unused['strict_clean'],UNUSEDLOCAL=unused['local_clean'],UNUSEDDIRECT=unused['direct'],UNUSEDTRANS=unused['transitive'],
    USEDTABLE=table('used'),UNUSEDTABLE=table('unused'),HISTREACH=data['historical']['reachable_project'],
    HISTHOLES=len(history_holes),ALLHOLES=len(pending),PRIVATEHOLES=len(private_pending),
    DATA=json.dumps(data,ensure_ascii=False,separators=(',',':')).replace('<','\\u003c').replace('\u2028','\\u2028').replace('\u2029','\\u2029'))
for key,value in replace.items(): PAGE=PAGE.replace('__'+key+'__',str(value))
(OUT/'index.html').write_text(PAGE)
print(json.dumps(dict(summary=summary,validation=valid,pending=data['pending']['by_module'],html_bytes=len(PAGE.encode())),ensure_ascii=False,indent=2))
