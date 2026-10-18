"""The map must display exactly the native mathematical graph and statuses."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from blueprint_map import export_map, project_map_data


def fixture():
    def entry(identity, status, deps=(), **extra):
        return {'id': identity, 'label': 'sem:' + identity, 'title': 'Statement ' + identity,
                'body': 'For every $x$, $x=x$.', 'kind': 'theorem', 'lean_status': status,
                'deps': [{'id': dependency, 'type': 'uses'} for dependency in deps], **extra}
    def block(identity, num):
        return {'t': 'stmt', 'id': identity, 'label': 'sem:' + identity,
                'abbr': 'Thm', 'num': num}
    return {'title': 'A blueprint', 'entries': [entry('a', 'sorry'),
                entry('b', 'lean_ok', ['a'], sketch=True), entry('c', 'empty')],
            'chapters': [{'title': 'Foundations', 'blocks': [
                {'t': 'head', 'level': 2, 'title': 'Objects'}, block('a', '1.1')]},
                {'title': 'Consequences', 'blocks': [block('b', '2.1'), block('c', '2.2')]}],
            'refs': {'sem:a': {'id': 'a', 'num': '1.1', 'ch': 0}},
            'macros': {'\\Z': '\\mathbb{Z}'}, 'bib': [{'key': 'Source', 'title': 'A source'}]}


class MapDataTests(unittest.TestCase):
    def test_complete_graph_is_preserved_with_prerequisite_arrows(self):
        project = fixture()
        before = deepcopy(project)
        data = project_map_data(project)
        self.assertEqual(project, before)
        self.assertEqual(data['edges'], [{'from': 'a', 'to': 'b'}])
        self.assertEqual([row['id'] for row in data['nodes']], ['a', 'b', 'c'])
        self.assertEqual([row['status'] for row in data['nodes']], ['sorry', 'lean_ok', 'empty'])
        self.assertTrue(data['nodes'][1]['sketch'])
        self.assertEqual(data['nodes'][1]['body'], project['entries'][1]['body'])
        self.assertEqual(data['stats']['nodes'], 3)
        self.assertEqual(data['stats']['statuses'], {'sorry': 1, 'lean_ok': 1, 'empty': 1})
        self.assertEqual(data['nodes'][1]['url'], '../#/Kervaire126#sem:b')
        self.assertEqual(data['refs'], project['refs'])
        self.assertEqual(data['macros'], project['macros'])

    def test_soft_links_do_not_become_mathematical_dependencies(self):
        project = fixture()
        project['entries'][0]['deps'].append({'id': 'hidden-source', 'type': 'related_to'})
        self.assertEqual(project_map_data(project)['edges'], [{'from': 'a', 'to': 'b'}])

    def test_missing_or_repeated_nodes_and_unknown_dependencies_are_rejected(self):
        project = fixture()
        project['chapters'][1]['blocks'].pop()
        with self.assertRaisesRegex(ValueError, 'missing from map'):
            project_map_data(project)
        project = fixture()
        project['chapters'][0]['blocks'].append(deepcopy(project['chapters'][0]['blocks'][-1]))
        with self.assertRaisesRegex(ValueError, 'repeated map'):
            project_map_data(project)
        project = fixture()
        project['entries'][0]['deps'].append({'id': 'missing', 'type': 'uses'})
        with self.assertRaisesRegex(ValueError, 'outside the published'):
            project_map_data(project)

    def test_export_uses_same_native_payload_and_local_assets(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out = root / '_site'
            (out / 'blueprint-map').mkdir(parents=True)
            renderer = out / 'blueprint-map/renderer.html'
            renderer.write_text('<!doctype html><title>Native Blueprint map</title>')
            renderer_before = renderer.read_bytes()
            (out / 'Kervaire126').mkdir(parents=True)
            payload = out / 'Kervaire126/data.json'
            payload.write_text(json.dumps(fixture()))
            before = payload.read_bytes()
            (out / 'assets').mkdir()
            (out / 'assets/katexLoader-native.js').write_text('export default function() {}')
            (out / 'assets/katexLoader-native.css').write_text('')
            stats = export_map(root, out)
            data = json.loads((out / 'blueprint-map/data.json').read_text())
            self.assertEqual(stats['nodes'], 3)
            self.assertEqual(payload.read_bytes(), before)
            self.assertEqual(data['katex']['js'], '../assets/katexLoader-native.js')
            self.assertEqual(data['katex']['css'], '../assets/katexLoader-native.css')
            self.assertTrue((out / 'blueprint-map/renderer.html').exists())
            self.assertEqual(renderer.read_bytes(), renderer_before)


if __name__ == '__main__':
    unittest.main()
