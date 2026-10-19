"""Presentation regressions; dependency/state semantics are native hgraph."""
from pathlib import Path
import tempfile
import unittest


class AimPaperPresentationTests(unittest.TestCase):
    def test_web_copy_preserves_every_nonpaper_tex_statement(self):
        from blueprint_paper import prepare_web_blueprint
        from hgraph.sync import parse_blueprint, read_blueprint
        root = Path(__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory() as directory:
            web = prepare_web_blueprint(root, Path(directory) / 'web')
            for path in (root / 'blueprint').rglob('*.tex'):
                if 'generated' in path.relative_to(root / 'blueprint').parts:
                    continue
                if path.parent.name == 'paper' and '% AimPaper: ' in path.read_text():
                    continue
                self.assertEqual(path.read_bytes(),
                                 (web / path.relative_to(root / 'blueprint')).read_bytes(),
                                 str(path))
            authored, _ = parse_blueprint(read_blueprint(root / 'blueprint/content.tex'))
            rendered, _ = parse_blueprint(read_blueprint(web / 'content.tex'))
            self.assertEqual([r['label'] for r in authored], [r['label'] for r in rendered])


    def test_two_line_corollary_binds_the_complete_proof_and_keeps_its_target_definition(self):
        from hgraph.sync import parse_blueprint, read_blueprint
        root = Path(__file__).resolve().parents[1]
        _, corollary = self.paper_source(root, 'paper:1.5')
        self.assertEqual(corollary['lean'], ['KIP126.Main.adams_two_line_classification'])
        self.assertFalse(corollary['sketch'])
        rows, _ = parse_blueprint(read_blueprint(root / 'blueprint/semantic/Main.tex'))
        target = next(row for row in rows if row['label'] == 'sem:Main:two-line-classification-goal')
        self.assertEqual(target['content_type'], 'definition')
        self.assertEqual(set(target['lean']), {'KIP126.Main.AdamsTwoLineListed',
                                              'KIP126.Main.AdamsTwoLineClassification'})
        self.assertIn('does not prove', target['body'])
        partial = next(row for row in rows if row['label'] == 'sem:Main:two-line-known-squares')
        self.assertEqual(partial['lean'], ['KIP126.Main.adams_two_line_known_squares'])


    def paper_source(self, root, label):
        from hgraph.sync import parse_blueprint, read_blueprint
        matches = [(path, row) for path in (root / 'blueprint/paper').glob('*.tex')
                   for row in parse_blueprint(read_blueprint(path))[0]
                   if row['label'] == label]
        self.assertEqual(len(matches), 1, f'Expected one authored source for {label}')
        return matches[0]


    def test_chapter_and_detail_rendering_both_use_compatible_math(self):
        from blueprint_paper import (display_body,
                                     prepare_web_blueprint, reference_targets)
        from hgraph.sync import read_blueprint, parse_blueprint
        root = Path(__file__).resolve().parents[1]
        original, _ = parse_blueprint(read_blueprint(root / 'blueprint/content.tex'))
        refs = reference_targets(root, original)
        diagram_sources = [row for row in original
                           if row['label'].startswith('paper:') and r'\xymatrix' in row['body']]
        self.assertTrue(diagram_sources)
        source_path, source_diagram = self.paper_source(root, 'paper:2.12')
        self.assertIn(r'\xymatrix', source_diagram['body'])
        authored = {path: path.read_bytes() for path in (root / 'blueprint/paper').glob('*.tex')}
        with tempfile.TemporaryDirectory() as directory:
            destination = prepare_web_blueprint(root, Path(directory) / 'web')
            statements, _ = parse_blueprint(read_blueprint(destination / 'content.tex'))
            paper = [row for row in statements if row['label'].startswith('paper:')]
            self.assertEqual(len(paper), 55)
            permanence = next(row for row in paper if row['label'] == 'paper:1.4')
            self.assertIn('paper:7.1', permanence['labels'])
            self.assertIn('thm:126survives', permanence['labels'])
            self.assertFalse(any(row['label'] == 'paper:7.1' for row in paper))
            self.assertEqual(permanence['title'], 'Permanence of $h_6^2$')
            self.assertIn(r'(From \cite{LWX126}, Theorem 1.4, Theorem 7.1.)', permanence['body'])
            self.assertNotIn('[Theorem', permanence['body'])
            original_permanence = next(row for row in original if row['label'] == 'paper:1.4')
            self.assertNotIn('[Theorem', display_body(original_permanence['body'], '1.4', refs))
            by_label = {row['label']: row for row in paper}
            for source in diagram_sources:
                with self.subTest(label=source['label']):
                    number = source['label'].removeprefix('paper:')
                    chapter_body = by_label[source['label']]['body']
                    detail_body = display_body(source['body'], number, refs)
                    self.assertNotIn(r'\xymatrix', chapter_body)
                    self.assertNotIn(r'\xymatrix', detail_body)
                    diagram_link = r'\href{paper/diagrams/' + number + '-1.svg}'
                    diagram_path, _ = self.paper_source(root, source['label'])
                    rendered_path = destination / diagram_path.relative_to(root / 'blueprint')
                    self.assertIn(diagram_link, rendered_path.read_text())
                    self.assertIn(diagram_link, chapter_body)
                    self.assertNotIn('see the original commutative diagram', chapter_body)
                    self.assertEqual(' '.join(chapter_body.split()),
                                     ' '.join(detail_body.split()))
            self.assertIn('Suppose $m,n,l', by_label['paper:2.12']['body'])
            self.assertNotIn(r'\xymatrix',
                             (destination / source_path.relative_to(root / 'blueprint')).read_text())
        for path, content in authored.items():
            self.assertEqual(path.read_bytes(), content, f'Rendering changed authored source: {path}')


    def test_external_bx_criterion_stays_upstream_of_main_choice_transport(self):
        from hgraph.sync import parse_blueprint, read_blueprint
        root = Path(__file__).resolve().parents[1]
        rows, _ = parse_blueprint(read_blueprint(root / 'blueprint/content.tex'))
        entries = {row['label']: row for row in rows}
        external = entries['paper:7.3']
        transport = entries['sem:Main:any-choice-criterion']
        self.assertTrue(external['chapter'].startswith('Literature'))
        self.assertEqual(set(external['lean']), {
            'KIP126.Literature.Standard.bx_finite',
            'KIP126.Literature.Standard.bx_untruncated'})
        self.assertTrue(external['sketch'])
        self.assertIn(r'\ref{sem:Main:any-choice-criterion}', external['body'])
        self.assertNotIn('sem:Main:any-choice-criterion', external['uses'])
        self.assertTrue(transport['chapter'].startswith('Main'))
        self.assertEqual(transport['lean'], ['KIP126.Main.any_choice_criterion'])


    def test_web_bibliography_resolves_doi_urls_without_changing_sources(self):
        from blueprint_paper import prepare_web_blueprint
        from hgraph.dashboard import discover_bib
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'blueprint'
            source.mkdir()
            (source / 'content.tex').write_text('')
            bibliography = source / 'references.bib'
            original = '''@article{full,
  title = {Full DOI URL},
  DOI = {https://doi.org/10.1007/s00222-024-01298-6},
}
@article{legacy,
  title = {Legacy DOI resolver},
  doi = "http://dx.doi.org/10.48550/arXiv.2105.07628",
}
@article{bare,
  title = {Bare DOI},
  doi = {10.1007/example},
}
@article{explicit,
  title = {Explicit URL},
  doi = {https://doi.org/10.1007/ignored},
  url = {https://example.org/paper},
}
'''
            bibliography.write_text(original)
            destination = prepare_web_blueprint(root, root / 'web')
            urls = {row['key']: row['url']
                    for row in discover_bib(destination / 'content.tex')}
            self.assertEqual(urls, {
                'full': 'https://doi.org/10.1007/s00222-024-01298-6',
                'legacy': 'https://doi.org/10.48550/arXiv.2105.07628',
                'bare': 'https://doi.org/10.1007/example',
                'explicit': 'https://example.org/paper'})
            self.assertEqual(bibliography.read_text(), original)


    def test_paper_statement_numbers_and_primes_survive_browser_layout(self):
        from blueprint_paper import display_body
        text = r"\begin{enumerate} \setcounter{enumi}{2}\item first \item second \end{enumerate}"
        result = display_body(text, '7.8')
        self.assertIn(r'\item[(3)]', result)
        self.assertIn(r'\item[(4)]', result)
        prime = r"\begin{enumerate}[label=(\arabic*')]\setcounter{enumi}{3}\item hypothesis\end{enumerate}"
        self.assertIn(r"\item[(4')]", display_body(prime, '7.10'))


    def test_diagram_and_reference_fallback_retain_original_conditions(self):
        from blueprint_paper import display_body
        original = r"Assume $x=0$. $$\xymatrix{X \ar[r]^f & Y}$$ Then $y=0$ (\ref{original})."
        rendered = display_body(original, '2.12', {'original': ('#/Kervaire126#paper:1.4', '1.4')})
        self.assertIn('Assume $x=0$', rendered)
        self.assertIn('Then $y=0$', rendered)
        self.assertIn('paper/diagrams/2.12-1.svg', rendered)
        self.assertLess(rendered.index('Assume'), rendered.index('paper/diagrams/'))
        self.assertLess(rendered.index('paper/diagrams/'), rendered.index('Then'))
        self.assertNotIn('$$', rendered)
        self.assertIn(r'\href{#/Kervaire126#paper:1.4}{1.4}', rendered)
        self.assertNotIn(r'\xymatrix', rendered)


    def test_diagram_conversion_cannot_drop_adjacent_mathematics(self):
        from blueprint_paper import display_body
        with self.assertRaisesRegex(ValueError, 'standalone display'):
            display_body(r'$$x=0,\quad\xymatrix{X & Y}$$', '2.12')
        rendered = display_body(r'\[\xymatrix{X & Y}\] and $$\xymatrix{Y & Z}$$', '2.12')
        self.assertIn('2.12-1.svg', rendered)
        self.assertIn('2.12-2.svg', rendered)
        self.assertNotIn(r'\[', rendered)



if __name__ == "__main__":
    unittest.main()
