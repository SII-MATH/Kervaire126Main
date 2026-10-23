#!/usr/bin/env python3
"""Fetch imported dependency artifacts once per environment and import set."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


def write_json(path, data):
    with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, prefix='.dependency-', delete=False) as stream:
        json.dump(data, stream, sort_keys=True)
    Path(stream.name).replace(path)


def source_digests(root):
    names = subprocess.check_output(['git', 'ls-files', '-z', '--cached', '--others',
                                     '--exclude-standard', '--', 'KIP126.lean', 'lakefile.lean',
                                     'KIP126', 'Tests', 'Checks'], cwd=root).decode().split('\0')
    result = {}
    for name in sorted(set(names)):
        if name.endswith('.lean'):
            try:
                result[name] = hashlib.sha256((root / name).read_bytes()).hexdigest()
            except FileNotFoundError:
                pass
    if not result:
        raise ValueError('No active Lean sources found')
    return result


def import_roots(root):
    """Lean remains the parser; unchanged file headers need no Lean startup."""
    key = hashlib.sha256((root / 'lean-toolchain').read_bytes() + b'\0' +
                         (root / 'lake-manifest.json').read_bytes() + b'\0' +
                         Path(__file__).read_bytes()).hexdigest()
    path = root / '.lake/packages' / ('.runner-import-headers-' + key + '.json')
    try:
        cached = json.loads(path.read_text())
        if not isinstance(cached, dict):
            cached = {}
    except (FileNotFoundError, ValueError):
        cached = {}
    sources = source_digests(root)
    headers, changed = {}, []
    for name, digest in sources.items():
        entry = cached.get(name, {})
        if (isinstance(entry, dict) and entry.get('sha256') == digest and
                isinstance(entry.get('imports'), list) and
                all(isinstance(module, str) for module in entry['imports'])):
            headers[name] = entry
        else:
            changed.append(name)
    if changed:
        parsed = json.loads(subprocess.check_output(
            ['lake', 'env', 'lean', '--deps-json', *changed], cwd=root, text=True))['imports']
        if len(parsed) != len(changed):
            raise ValueError('Lean did not return an import header for every changed source')
        for name, header in zip(changed, parsed):
            if header['errors'] or header.get('result') is None:
                raise ValueError(f'Cannot parse imports in {name}: {header["errors"]}')
            headers[name] = {'sha256': sources[name],
                             'imports': [item['module'] for item in header['result']['imports']]}
        write_json(path, headers)
    elif set(cached) != set(headers):
        write_json(path, headers)
    local = {str(Path(name).with_suffix('')).replace('/', '.') for name in sources}
    modules = sorted({module for header in headers.values() for module in header['imports']
                      if module not in local and module.split('.', 1)[0] not in {'Init', 'Lean', 'Std', 'Lake'}})
    print(f'Native import headers: parsed {len(changed)}, reused {len(headers) - len(changed)}', flush=True)
    return modules


def artifact_paths(root, modules, known=None):
    packages = root / '.lake/packages'
    known = known if isinstance(known, dict) else {}
    result = {}
    bases = None
    for name in modules:
        suffix = Path(name.replace('.', '/') + '.olean')
        value = known.get(name, '')
        recorded = Path(value if isinstance(value, str) else '')
        if (not recorded.is_absolute() and '..' not in recorded.parts and
                len(recorded.parts) == len(suffix.parts) + 5 and
                recorded.parts[1:5] == ('.lake', 'build', 'lib', 'lean') and
                recorded.parts[5:] == suffix.parts and (packages / recorded).is_file()):
            result[name] = str(recorded)
            continue
        if bases is None:
            bases = [p / '.lake/build/lib/lean' for p in packages.iterdir() if p.is_dir()]
        for base in bases:
            if (base / suffix).is_file():
                result[name] = str((base / suffix).relative_to(packages))
                break
    return result


def artifacts_present(root, modules):
    return len(artifact_paths(root, modules)) == len(modules)


def ensure(root, run=subprocess.run):
    modules = import_roots(root)
    key = hashlib.sha256(json.dumps({
        'toolchain': (root / 'lean-toolchain').read_text(),
        'manifest': (root / 'lake-manifest.json').read_text(),
        'imports': modules,
    }, sort_keys=True).encode()).hexdigest()
    marker = root / '.lake/packages' / ('.runner-mathlib-' + key)
    try:
        recorded = json.loads(marker.read_text())
        known = recorded.get('artifacts', {}) if recorded.get('key') == key else {}
    except (FileNotFoundError, ValueError, AttributeError):
        known = {}
    present = artifact_paths(root, modules, known)
    if marker.is_file() and len(present) == len(modules):
        if known != present:
            write_json(marker, {'key': key, 'artifacts': present})
        print('Imported Mathlib artifacts already verified for this environment/import set', flush=True)
        return
    if modules:
        run(['lake', 'exe', 'cache', 'get', *modules], cwd=root, check=True)
        present = artifact_paths(root, modules)
        if len(present) != len(modules):
            raise ValueError('Dependency cache completed without all imported artifacts')
    write_json(marker, {'key': key, 'artifacts': present})
    print('Recorded successful dependency cache for this import set', flush=True)


if __name__ == '__main__':
    ensure(Path(os.environ['GITHUB_WORKSPACE']))
