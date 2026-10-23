#!/usr/bin/env python3
"""Validate the canonical ledger and project only one audit's actual inputs.

The reviewed ledger remains the only maintained source. Lake writes these
derived projections under .lake/audit-inputs; no projection accepts new holes
or updates the canonical ledger. Unchanged projections retain their mtimes.
"""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import stat
import tempfile


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_LEDGER = ROOT / 'interface/baselines/proof-obligations.json'
MODULES = (
    'SpectralSequence', 'AdamsSynthetic', 'Literature', 'AdamsComputation',
    'ProofTools', 'SSComputation', 'Main', 'Geometry',
)
ROUTE_KEY = 'main_zero_layer_rewire_2026_10_16'
ROUTE_FIELDS = ('public_main_roots', 'proofTools_boundary_declarations')
ROW_FIELDS = ('name', 'module', 'type_fingerprint', 'body_fingerprint', 'status')
STATUSES = ('pending-proof', 'pending-construction')


def _object(value, description, keys=None):
    if not isinstance(value, dict):
        raise ValueError(description + ' must be an object')
    if keys is not None and set(value) != set(keys):
        raise ValueError(description + ' fields differ: missing ' +
                         str(sorted(set(keys) - set(value))) + ', unknown ' +
                         str(sorted(set(value) - set(keys))))
    return value


def _string(value, description):
    if not isinstance(value, str) or not value.strip():
        raise ValueError(description + ' must be a nonempty string')
    return value


def module_owner(module):
    """Use the defining source module, never the declaration's namespace."""
    _string(module, 'Obligation module')
    parts = module.split('.')
    if (len(parts) < 2 or parts[0] != 'KIP126' or parts[1] not in MODULES or
            any(not part for part in parts)):
        raise ValueError('Unknown obligation source module: ' + module)
    return parts[1]


def _counts(value, description, permitted):
    _object(value, description)
    for key, count in value.items():
        if key not in permitted or type(count) is not int or count < 0:
            raise ValueError('Invalid ' + description + ' count: ' + str(key))


def validate_ledger(ledger):
    """Validate global coverage before any field can be omitted from a shard."""
    _object(ledger, 'Ledger', ('schema_version', 'summary', 'obligations', ROUTE_KEY))
    if type(ledger['schema_version']) is not int or ledger['schema_version'] != 2:
        raise ValueError('Unsupported proof obligation schema_version')
    rows = ledger['obligations']
    if not isinstance(rows, list):
        raise ValueError('Ledger obligations must be an array')
    names = set()
    owners = []
    for index, row in enumerate(rows):
        _object(row, 'Obligation row ' + str(index))
        missing = set(ROW_FIELDS) - set(row)
        if missing:
            raise ValueError('Obligation row missing fields: ' + str(sorted(missing)))
        name = _string(row['name'], 'Obligation name')
        if name in names:
            raise ValueError('Duplicate obligation name: ' + name)
        names.add(name)
        owner = module_owner(row['module'])
        # Its independent audit is unconditionally sorry-free and consumes no
        # ledger shard, so no permission may disappear through that boundary.
        if owner == 'SpectralSequence':
            raise ValueError('SpectralSequence permits no proof/construction obligations')
        owners.append(owner)
        for field in ('type_fingerprint', 'body_fingerprint'):
            value = row[field]
            if not isinstance(value, str) or re.fullmatch(r'[0-9]+', value) is None:
                raise ValueError('Invalid obligation ' + field + ': ' + name)
        if row['status'] not in STATUSES:
            raise ValueError('Unknown obligation status: ' + name)

    summary = _object(ledger['summary'], 'Ledger summary',
                      ('total', 'by_module', 'by_kind'))
    if type(summary['total']) is not int or summary['total'] < 0:
        raise ValueError('Ledger summary total must be a nonnegative integer')
    _counts(summary['by_module'], 'summary by_module', MODULES)
    _counts(summary['by_kind'], 'summary by_kind', STATUSES)
    expected_summary = {
        'total': len(rows),
        'by_module': dict(Counter(owners)),
        'by_kind': dict(Counter(row['status'] for row in rows)),
    }
    if summary != expected_summary:
        raise ValueError('Ledger summary does not match all obligation rows')

    route = _object(ledger[ROUTE_KEY], 'Main/ProofTools audit boundary', ROUTE_FIELDS)
    for field in ROUTE_FIELDS:
        values = route[field]
        if not isinstance(values, list):
            raise ValueError('Audit boundary ' + field + ' must be an array')
        seen = set()
        for value in values:
            _string(value, 'Audit boundary ' + field + ' entry')
            if value in seen:
                raise ValueError('Duplicate audit boundary ' + field + ' entry: ' + value)
            seen.add(value)


def project_ledger(ledger, module):
    """Preserve complete rows and only the boundary fields this audit reads."""
    if module not in MODULES:
        raise ValueError('Unknown audit module: ' + str(module))
    validate_ledger(ledger)
    result = {
        'schema_version': ledger['schema_version'],
        'audit_module': module,
        'obligations': [row for row in ledger['obligations']
                        if module_owner(row['module']) == module],
    }
    if module == 'Main':
        result[ROUTE_KEY] = {field: ledger[ROUTE_KEY][field] for field in ROUTE_FIELDS}
    elif module == 'ProofTools':
        result[ROUTE_KEY] = {
            'proofTools_boundary_declarations':
                ledger[ROUTE_KEY]['proofTools_boundary_declarations'],
        }
    return result


def projection_bytes(ledger, module):
    return (json.dumps(project_ledger(ledger, module), ensure_ascii=False,
                       sort_keys=True, separators=(',', ':'), allow_nan=False) + '\n').encode('utf-8')


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate JSON object key: ' + key)
        result[key] = value
    return result


def _invalid_constant(value):
    raise ValueError('Invalid JSON numeric constant: ' + value)


def load_ledger(path):
    return json.loads(Path(path).read_text(encoding='utf-8'),
                      object_pairs_hook=_unique_object, parse_constant=_invalid_constant)


def write_if_changed(path, contents):
    """Atomically replace changed output; leave healthy cached files untouched."""
    path = Path(path)
    if path.exists() and path.read_bytes() == contents:
        return False
    mode = stat.S_IMODE(path.stat().st_mode) if path.exists() else 0o644
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix='.' + path.name + '.',
                                         delete=False) as output:
            temporary = Path(output.name)
            output.write(contents)
        temporary.chmod(mode)
        os.replace(temporary, path)
        temporary = None
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return True


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument('--check', action='store_true', help='validate the entire canonical ledger')
    action.add_argument('--module', choices=MODULES, help='audit whose derived inputs to write')
    parser.add_argument('--ledger', type=Path, default=DEFAULT_LEDGER)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args(argv)
    if args.check and args.output is not None:
        parser.error('--check does not write --output')
    if not args.check and args.output is None:
        parser.error('--module requires --output')
    try:
        ledger = load_ledger(args.ledger)
        if args.check:
            validate_ledger(ledger)
        else:
            if args.output.resolve() in {args.ledger.resolve(), DEFAULT_LEDGER.resolve()}:
                raise ValueError('Refusing to replace the canonical ledger with a projection')
            contents = projection_bytes(ledger, args.module)
            write_if_changed(args.output, contents)
    except (OSError, ValueError, TypeError) as error:
        parser.error(str(error))


if __name__ == '__main__':
    main()
