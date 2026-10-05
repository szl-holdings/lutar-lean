"""Offline source/preservation contract, not hosted dataset or Lean proof qualification.

The import SHA binds the historical card documented in huggingface/README.md.
A later intentional prose edit must update this binding with reviewed evidence;
it must not accidentally restore the stale Hub proposal while fixing its config.
"""
import hashlib
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
CARD = ROOT / 'huggingface/datasets/lean-theorem-tree/README.md'
IMPORT_SHA256 = '6a11e1311a2c09b49829d650e1a17fe8b66d3de7cea72b1759c5c430bd55c019'
SELECTOR = (
    b'configs:\n- config_name: default\n  data_files:\n'
    b'  - split: train\n    path: data/lean_theorem_tree.json\n'
    b'  field: declarations\n'
)


def require_config_only_change(raw):
    # Git may materialize CRLF on Windows. Only that checkout equivalence is allowed.
    # Immutable provider/source fingerprints are verified separately against raw bytes.
    raw = raw.replace(b'\r\n', b'\n')
    if not raw.startswith(b'---\n') or raw.count(SELECTOR) != 1:
        raise ValueError('exact dataset selector missing or duplicated')
    front, separator, _ = raw.partition(b'\n---\n')
    if not separator or SELECTOR.rstrip(b'\n') not in front:
        raise ValueError('selector must be inside the first YAML front matter')
    restored = raw.replace(SELECTOR, b'', 1)
    if hashlib.sha256(restored).hexdigest() != IMPORT_SHA256:
        raise ValueError('non-configuration card bytes changed')


class DatasetConfigContract(unittest.TestCase):
    def setUp(self):
        self.raw = CARD.read_bytes()

    def test_checked_in_card_passes(self):
        require_config_only_change(self.raw)

    def test_windows_crlf_checkout_is_equivalent(self):
        require_config_only_change(self.raw.replace(b'\n', b'\r\n'))

    def test_original_card_is_rejected(self):
        with self.assertRaises(ValueError):
            require_config_only_change(self.raw.replace(SELECTOR, b'', 1))

    def test_management_receipt_as_training_data_is_rejected(self):
        with self.assertRaises(ValueError):
            require_config_only_change(self.raw.replace(b'path: data/lean_theorem_tree.json', b'path: SZL_ESTATE_MANAGED.json', 1))

    def test_wrong_json_field_is_rejected(self):
        with self.assertRaises(ValueError):
            require_config_only_change(self.raw.replace(b'field: declarations', b'field: meta', 1))

    def test_duplicate_selector_is_rejected(self):
        with self.assertRaises(ValueError):
            require_config_only_change(self.raw.replace(SELECTOR, SELECTOR + SELECTOR, 1))

    def test_selector_in_markdown_instead_of_yaml_is_rejected(self):
        moved = self.raw.replace(SELECTOR, b'', 1) + b'\n' + SELECTOR
        with self.assertRaises(ValueError):
            require_config_only_change(moved)

    def test_unrelated_prose_or_badge_change_is_rejected(self):
        with self.assertRaises(ValueError):
            require_config_only_change(self.raw + b'\nUnqualified live claim.\n')


if __name__ == '__main__':
    unittest.main()
