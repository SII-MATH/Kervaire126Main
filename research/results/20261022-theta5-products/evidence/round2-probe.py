"""Bounded read-only AF10 square probes against the unchanged cw210 archive."""
import hashlib
import importlib.util
import json
from pathlib import Path
import resource

resource.setrlimit(resource.RLIMIT_AS, (4 << 30, 4 << 30))
resource.setrlimit(resource.RLIMIT_CPU, (110, 110))
ROOT = Path(__file__).resolve().parent
helper = ROOT.parents[1] / 'theta6' / 'probe.py'
spec = importlib.util.spec_from_file_location('round1_probe', helper)
p = importlib.util.module_from_spec(spec)
spec.loader.exec_module(p)


def package(a, degree):
    return {'degree': degree, 'basis': a.bydeg.get(degree, []), 'rows': a.rows(degree)}


def main():
    sphere = p.algebra('S0')
    cofiber = p.algebra('Ctheta5sq')
    source_degree = (0,125)
    target_degree = (10,134)
    source = 1
    target = cofiber.coords(target_degree, p.mon('0,2,367,1,0'))
    sphere_target = sphere.coords(target_degree, p.mon('0,2,367,1'))
    result = {'source': package(cofiber, source_degree),
              'target': package(cofiber, target_degree),
              'sphere_target': package(sphere, target_degree),
              'source_vector': p.indices(source), 'target_vector': p.indices(target),
              'maps': [], 'incoming_maps': [], 'products': [], 'errors': []}
    for cfg in p.CONFIG['maps']:
        if cfg['from'] != 'Ctheta5sq' and cfg['to'] != 'Ctheta5sq':
            continue
        try:
            f = p.Map(cfg)
            if cfg['from'] == 'Ctheta5sq':
                ds, dt = f.degree(source_degree), f.degree(target_degree)
                xs, xt = f.image(source_degree, source), f.image(target_degree, target)
                result['maps'].append({'config': cfg, 'source_degree': ds, 'target_degree': dt,
                    'source_image': p.indices(xs), 'target_image': p.indices(xt),
                    'source_info': f.B.info(ds, xs, 10), 'target_info': f.B.info(dt, xt, 10)})
            if cfg['to'] == 'Ctheta5sq':
                deg = (-f.fil, 125-f.fil+f.sus)
                if deg[0] < 0 or deg[1] > cfg['t_max']:
                    continue
                basis = f.A.bydeg.get(deg, [])
                cols = [f.image(deg, 1 << i) for i in range(len(basis))]
                preimage = p.solve(cols, source)
                result['incoming_maps'].append({'config': cfg, 'degree': deg,
                    'basis': basis, 'preimage': None if preimage is None else p.indices(preimage),
                    'preimage_info': None if preimage is None else f.A.info(deg, preimage, 10)})
        except Exception as exc:
            result['errors'].append({'config': cfg, 'error': repr(exc)})
    for gen in [0,1,2,3,7,8,13,18,24,25,69]:
        row = sphere.db.execute('SELECT id,name,s,t FROM S0_AdamsE2_generators WHERE id=?', (gen,)).fetchone()
        deg = (10+row[2],134+row[3])
        value = sphere.coords(deg,p.multiply(p.mon(f'{gen},1'),p.mon('0,2,367,1')))
        result['products'].append({'factor':row,'degree':deg,'value':p.indices(value),
                                  'info':sphere.info(deg,value,10)})
    result['stem124_low'] = [package(sphere,(s,124+s)) for s in range(2,14)]
    result['stem96_low'] = [package(sphere,(s,96+s)) for s in range(5,16)]
    result['early_top_sources'] = [package(cofiber,(q,125+q)) for q in range(1,9)]
    result['generators'] = list(sphere.db.execute(
        'SELECT id,name,s,t FROM S0_AdamsE2_generators WHERE id IN (163,367,24,25)'))
    theta_cofiber = p.algebra('Ctheta5')
    theta_target = theta_cofiber.coords(target_degree,p.mon('0,2,367,1,0'))
    result['canonical_factorization_to_Ctheta5'] = {
        'meaning': 'C(theta5^2) -> C(theta5), induced by the factorization theta5^2=theta5 theta5; E2 top image zero, bottom image identity',
        'target':package(theta_cofiber,target_degree), 'image':p.indices(theta_target),
        'image_info':theta_cofiber.info(target_degree,theta_target,10),
        'potential_sources':[package(theta_cofiber,(10-r,135-r)) for r in range(2,11)]}
    unit_cfg = next(cfg for cfg in p.CONFIG['maps'] if cfg['name']=='S0__tmf')
    unit_db = p.connect(p.DATA/unit_cfg['path'])
    table = next(row[0] for row in unit_db.execute("SELECT name FROM sqlite_master WHERE type='table' AND name!='version'"))
    result['tmf_generator_images'] = {'config':unit_cfg,
        'images':list(unit_db.execute(f'SELECT id,map FROM {table} WHERE id IN (0,18,367)'))}
    result['outer_indeterminacy_Ext_product'] = sorted(sphere.normal(p.multiply(p.mon('24,1'),p.mon('1,1,163,1'))))
    result['mixed_product_lemma'] = {
        'stem63_low':[package(sphere,(s,63+s)) for s in range(1,5)],
        'gamma_degree':package(sphere,(10,103)),
        'gamma_times_theta4':[
            {'basis':row,'value':sorted(sphere.normal(p.multiply(p.mon(row[1]),p.mon('7,2'))))}
            for row in sphere.bydeg.get((10,103),[])],
        'h1_theta5_theta4':sorted(sphere.normal(p.mon('1,1,7,2,18,2'))),
        'theta5_a8':sorted(sphere.normal(p.mon('18,2,82,1'))),
        'generator_names':list(sphere.db.execute(
            'SELECT id,name,s,t FROM S0_AdamsE2_generators WHERE id=82 OR (s=8 AND t-s=91)'))}
    result['helper'] = {'path':str(helper),'sha256':hashlib.sha256(helper.read_bytes()).hexdigest()}
    result['config'] = {'path':str(p.DATA/'ss.json'),
                        'sha256':hashlib.sha256((p.DATA/'ss.json').read_bytes()).hexdigest()}
    result['sha256'] = {str(path):hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(p.READ)}
    (ROOT/'probe-result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'maps':len(result['maps']),'incoming_maps':len(result['incoming_maps']),
                      'products':len(result['products']),'errors':result['errors']},indent=2))


if __name__ == '__main__':
    main()
