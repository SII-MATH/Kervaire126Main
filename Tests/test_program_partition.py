"""Program provenance determines the direct-Adams/SS certification boundary."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]


class ProgramPartitionTests(unittest.TestCase):
    def test_selected_records_keep_their_original_program_origin(self):
        direct = (ROOT / 'KIP126/AdamsComputation/Table/D2.lean').read_text()
        propagated = (ROOT / 'KIP126/SSComputation/Table/Data.lean').read_text()
        rows = re.findall(r'^  ⟨.*⟩,?$', direct, re.M)
        self.assertEqual(len(rows), 4)
        self.assertEqual([int(re.search(r', (\d+)⟩', row)[1]) for row in rows],
                         [513, 2855, 2923, 2926])
        self.assertTrue(all('.equation, 2,' in row and
                            '"S0_AdamsE2_basis/d2"' in row for row in rows))
        self.assertNotIn('S0_AdamsE2_basis/d2', propagated)
        ss_rows = re.findall(r'^  ⟨.*⟩,?$', propagated, re.M)
        self.assertEqual(len(ss_rows) + len(rows), 671)
        # A d2 statement remains SS-owned when its source is a propagated row.
        self.assertTrue(any('.equation, 2, 8, 133,' in row and
                            'S0_AdamsE2_ss' in row for row in ss_rows))

    def test_named_direct_calculation_uses_the_direct_certification(self):
        source = (ROOT / 'KIP126/AdamsComputation/D2.lean').read_text()
        self.assertIn('have hrow := direct_d2_result', source)
        self.assertNotIn('KIP126.SSComputation', source)
        self.assertNotIn('KIP126.ProofTools', source)
        self.assertIn('KIP126.Literature.Standard.adamsOneLine_d2', source)
        ss = (ROOT / 'KIP126/SSComputation/Standard.lean').read_text()
        self.assertIn('public theorem d2_x125_8', ss)
        self.assertNotIn('public theorem d2_h0Six_h6', ss)


if __name__ == '__main__':
    unittest.main()
