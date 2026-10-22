"""Small explicit certificates for the page quotient and theta5-square bridge."""
import hashlib
import json

import probe as p


def package(a, deg):
    return {'degree':deg, 'basis':a.bydeg.get(deg,[]), 'rows':a.rows(deg)}


def rows(a, deg, sql):
    return list(a.db.execute(sql, deg))


def version(path):
    db=p.connect(path)
    if db.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='version'").fetchone():
        return list(db.execute('SELECT * FROM version'))
    return None


def main():
    c,s,h = p.algebra('C2'),p.algebra('S0'),p.algebra('Ctheta5sq')
    cfg = next(x for x in p.CONFIG['maps'] if x['name']=='Ctheta5sq__C2_by_eta')
    f = p.Map(cfg)
    target=(12,138)
    result={'C2_target':package(c,target),
            'C2_early_sources':{str(deg):package(c,deg) for deg in [(10,137),(9,136),(8,135),(7,134),(6,133),(4,131)]},
            'sphere_early_sources':{str(deg):package(s,deg) for deg in [(6,132),(6,133),(7,134),(11,137)]},
            'Ctheta5sq_source':package(h,(0,125)),
            'Ctheta5sq_target':package(h,(10,134)),
            'Ctheta5sq_map':cfg,
            'Ctheta5sq_map_generator_rows':{str(i):f.images[i] for i in [0,1]},
            'Ctheta5sq_target_image':p.indices(f.image((10,134),1<<4)),
            'low_filtration_C2':{str((fil,127+fil)):package(c,(fil,127+fil)) for fil in range(3)}}
    assert result['Ctheta5sq_target_image']==[]
    assert f.image((0,125),1)==1
    # E2 target coordinates: e1 has nonzero d2; e2 is d2(source e2);
    # e3 is d3(source e0). These are complete linear-algebra statements
    # conditional on the archived actual differential identifications.
    d2_target=rows(c,target,'SELECT d2 FROM C2_AdamsE2_basis WHERE s=? AND t=? ORDER BY id')
    d2_incoming=rows(c,(10,137),'SELECT d2 FROM C2_AdamsE2_basis WHERE s=? AND t=? ORDER BY id')
    result['raw_d2_target']=d2_target
    result['raw_d2_incoming']=d2_incoming
    result['E4_certificate']={'E2_dim':4,'d2_noncycle_coordinate':1,
                             'd2_boundary_coordinate':2,'d3_boundary_coordinate':3,
                             'surviving_coordinate':0,
                             'trust_boundary':'d2/d3 values come from archive, not a new chain-level calculation'}
    result['top_cell_source_comparison']={
        'map':next(x for x in p.CONFIG['maps'] if x['name']=='C2__S0'),
        'C2_source':package(c,(6,133)), 'sphere_source':package(s,(6,132)),
        'nonzero_disjunction_reference':'AimPaper/main.tex Remark 7.7; d3(x126,6) = A or A+D, both nonzero'}
    result['bottom_target_columns']=[{'sphere_basis':row,
        'image':p.indices(c.coords(target,p.multiply(p.mon(row[1]),p.mon('0'))))}
        for row in s.bydeg.get(target,[])]
    cof=p.connect(p.DATA/'cofseq_S0__C2__S0.db')
    result['next_top_cell_extension']={
        'source':list(cof.execute('SELECT * FROM cofseq_S0__C2__S0 WHERE iC=1 AND s=12 AND t=138')),
        'candidate_sphere_target':package(s,(14,139)),
        'meaning':'The archive first leaves a length-two q extension on z undetermined; no actual theta5-square representative is identified here.'}
    result['provenance']={str(path):{'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
       'version':version(path)}
       for path in sorted(p.READ) if path.suffix=='.db'}
    result['config_sha256']=hashlib.sha256((p.DATA/'ss.json').read_bytes()).hexdigest()
    result['Ravenel_source']={'path':'/inspire/hdd/global_user/czxs25250150/Kervaire126/Source/Ravenel/ravenel.pdf',
        'theorem':'3.4.5(a)', 'formula':'Ext^(s,t)=0 if 0<t-s<2s-epsilon(s); epsilon=1 for s=0,1 mod4, 2 for s=2 mod4, 3 for s=3 mod4',
        'C2_cutoff':'For fixed stem126, the two neighboring sphere Ext groups have stem126 and125; both vanish for s>=64. Thus d_r from (1,128) has zero target for r>=63.'}
    (p.ROOT/'followup-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print('Explicit quotient, cofiber map and vanishing-line evidence written.')


if __name__=='__main__':
    main()
