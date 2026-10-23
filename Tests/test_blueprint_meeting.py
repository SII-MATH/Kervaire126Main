"""Meeting archive navigation and source-record integrity."""
from collections import Counter
from copy import deepcopy
from pathlib import Path
import sys
import tempfile
import unittest

import yaml

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import blueprint_meeting as meeting


class MeetingArchiveTests(unittest.TestCase):
    def test_latest_meeting_preserves_source_categories_and_ids(self):
        records = meeting.read_meetings(ROOT)
        self.assertEqual([record['date'] for record in records],
                         ['2026-10-21', '2026-10-20', '2026-10-13'])
        tasks = records[0]['tasks']
        self.assertEqual({task['id'] for task in tasks},
                         {'M01', 'M02', 'M03', 'M04', 'F01', 'P01', 'P02', 'P03', 'E01', 'Q01', 'Q02'})
        self.assertEqual(Counter(task['category'] for task in tasks),
                         {'会中待办': 4, '会后确认': 1, '后续计划': 3, '探索建议': 1, '待核事项': 2})
        self.assertEqual(next(task['owner'] for task in tasks if task['id'] == 'F01'), '袁瑞松')
        self.assertTrue(all(task['details'][0]['links'] for task in tasks))

    def test_october_20_keeps_original_numbering_and_both_recordings(self):
        record = meeting.read_meeting(ROOT / 'meeting/2026-10-20.yaml')
        tasks = {task['id']: task for task in record['tasks']}
        self.assertEqual(len(tasks), 15)
        self.assertEqual(Counter(task['category'] for task in tasks.values()),
                         {'会中待办': 6, '后续计划': 4, '探索建议': 3, '待核事项': 2})
        self.assertEqual(tasks['M06']['category'], '后续计划')
        self.assertEqual(tasks['M07']['category'], '会中待办')
        self.assertEqual(tasks['M04']['owner'], '原稿说话人2（姓名待确认）')
        self.assertIn('10月20日', tasks['M05']['note'])
        page = meeting.render_meeting(record, ROOT)
        for key in ['recording_a', 'recording_b']:
            self.assertIn(record['sources'][key], page)

    def test_follow_up_includes_discussion_once_and_excludes_merges(self):
        record = meeting.read_meeting(ROOT / 'meeting/2026-10-13.yaml')
        self.assertEqual(meeting.summary(record), {'completed': 18, 'follow_up': 6, 'merged': 3})
        page = meeting.render_meeting(record, ROOT)
        self.assertEqual(page.count('class="metric metric-'), 3)
        self.assertNotIn('data-filter="to_discuss"', page)
        self.assertIn('href="#T08" data-target="T08">并入 T08', page)

    def test_export_keeps_dated_pages_and_old_task_links(self):
        with tempfile.TemporaryDirectory() as temporary:
            meeting.export_meeting(ROOT, temporary)
            directory = Path(temporary) / 'meeting'
            latest = (directory / 'index.html').read_text()
            self.assertIn('id="M01"', latest)
            self.assertIn('value="2026-10-21.html" selected', latest)
            self.assertIn('data-legacy-task="T13" href="2026-10-13.html#T13"', latest)
            historical = (directory / '2026-10-13.html').read_text()
            self.assertIn('id="T13"', historical)
            self.assertIn('href="index.html">返回最新会议', historical)
            self.assertIn('../source/KIP126/', historical)
            self.assertNotIn('data-legacy-task=', historical)
            self.assertTrue((directory / '2026-10-21.html').exists())
            october_20 = (directory / '2026-10-20.html').read_text()
            self.assertIn('id="M01"', october_20)
            self.assertIn('更新最简主定理与 h₆ 输入', october_20)
            self.assertNotIn('建立Adams输出验证器', october_20)
            self.assertTrue((directory / 'meeting.js').exists())
            self.assertTrue((directory / 'meeting.css').exists())

    def test_new_records_sort_by_meeting_date_and_may_reuse_task_ids(self):
        original = meeting.read_meeting(ROOT / 'meeting/2026-10-21.yaml')
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / 'meeting'
            directory.mkdir()
            for day in ['2026-11-02', '2026-09-01', '2026-10-21']:
                record = deepcopy(original)
                record['date'] = day
                record['updated'] = '2026-12-01'
                (directory / f'{day}.yaml').write_text(yaml.safe_dump(record))
            self.assertEqual([record['date'] for record in meeting.read_meetings(temporary)],
                             ['2026-11-02', '2026-10-21', '2026-09-01'])

    def test_invalid_record_identity_or_merge_fails_before_export(self):
        original = meeting.read_meeting(ROOT / 'meeting/2026-10-21.yaml')
        duplicate = deepcopy(original)
        duplicate['tasks'][1]['id'] = duplicate['tasks'][0]['id']
        mismatch = deepcopy(original)
        mismatch['date'] = '2026-10-22'
        invalid_date = deepcopy(original)
        invalid_date['date'] = '2026-02-30'
        invalid_merge = deepcopy(original)
        invalid_merge['tasks'][0].update(status='merged', merged_into='M01')
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / '2026-10-21.yaml'
            for record in [duplicate, mismatch, invalid_date, invalid_merge]:
                with self.subTest(record=record['date']):
                    path.write_text(yaml.safe_dump(record))
                    with self.assertRaises(ValueError):
                        meeting.read_meeting(path)

    def test_authored_navigation_and_categories_are_escaped(self):
        record = deepcopy(meeting.read_meetings(ROOT)[0])
        record['title'] = '<script>alert(1)</script>'
        record['tasks'][0]['category'] = '"><img src=x>'
        page = meeting.render_meeting(record, ROOT)
        self.assertNotIn('<script>alert(1)</script>', page)
        self.assertNotIn('<img src=x>', page)
        self.assertIn('&lt;script&gt;alert(1)&lt;/script&gt;', page)


if __name__ == '__main__':
    unittest.main()
