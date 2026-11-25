#!/usr/bin/env python3
"""Check the public source snapshot without private tools or Python packages."""
import json
import os
from pathlib import Path
import re
import sys
from urllib.parse import unquote

from lean_source import code, code_hash, sha256

ROOT = Path(__file__).resolve().parents[1]


def check(root=ROOT):
    lock = json.loads((root / 'verification/source-lock.json').read_text())
    problems = []
    expected = lock['files']
    ignored = {'.git', '.lake', '.verification', '__pycache__'}
    paths = []
    for directory, subdirs, names in os.walk(root):
        subdirs[:] = [d for d in subdirs if d not in ignored]
        paths.extend(Path(directory) / name for name in [*subdirs, *names])
    actual = {str(p.relative_to(root)) for p in paths if p.is_file()}
    if actual != set(expected) | {'verification/source-lock.json'}:
        problems.append(f'file inventory: missing={sorted(set(expected)-actual)}, '
                        f'extra={sorted(actual-set(expected)-{"verification/source-lock.json"})}')
    for name, digest in expected.items():
        p = root / name
        if not p.is_file() or sha256(p) != digest:
            problems.append(f'checksum: {name}')
    for p in paths:
        rel = p.relative_to(root)
        if p.is_symlink():
            problems.append(f'symlink: {rel}')
    sources = sorted([root / 'ClockBarrier.lean', *root.glob('ClockBarrier/**/*.lean')])
    modules = {str(p.relative_to(root).with_suffix('')).replace('/', '.') for p in sources}
    if modules != set(lock['modules']):
        problems.append('production module inventory')
    forbidden = re.compile(r'\b(?:sorry|admit|axiom|unsafe|partial|native_decide)\b|'
                           r'\bset_option\s+(?:maxHeartbeats|maxRecDepth|debug\.)')
    for p in sources:
        name = str(p.relative_to(root))
        text = p.read_text()
        body = code(text)
        if not re.match(r'\s*module\b', body):
            problems.append(f'module header: {name}')
        if forbidden.search(body):
            problems.append(f'forbidden production construct: {name}')
        if code_hash(text) != lock['code_sha256'][name]:
            problems.append(f'code changed: {name}')
        for dep in re.findall(r'^\s*(?:(?:public|private)\s+)?import\s+(\S+)', body, re.M):
            if dep.split('.')[0] not in {'ClockBarrier', 'Mathlib', 'Lean', 'Std', 'Init',
                                         'Batteries', 'Aesop', 'Qq'}:
                problems.append(f'undeclared import: {name}: {dep}')
            if dep.startswith('ClockBarrier') and dep not in modules:
                problems.append(f'missing project import: {name}: {dep}')
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        if package['type'] != 'git' or not re.fullmatch(r'[0-9a-f]{40}', package['rev']):
            problems.append(f'unpinned dependency: {package["name"]}')
    private = re.compile('/' + r'(?:Users|home)/|/' + r'(?:private/)?tmp/|'
                         r'\.codex/|author-rulings|approval packet|FROZEN_UNPROVED|'
                         r'BEGIN (?:RSA |OPENSSH |EC )?PRIVATE KEY|'
                         r'gh[pousr]_[A-Za-z0-9]{30,}|AKIA[A-Z0-9]{16}')
    for name in expected:
        p = root / name
        if p.suffix not in {'.lean', '.md', '.json', '.toml', '.cff', '.py'}:
            continue
        text = p.read_text()
        # The checker contains patterns, not personal paths or credentials.
        if name != 'scripts/check_release.py' and private.search(text):
            problems.append(f'private reference or credential pattern: {name}')
        if p.suffix == '.md':
            if re.search(r'\\(?:operatorname|DeclareMathOperator|newcommand|def)\b', text):
                problems.append(f'unsupported Markdown math macro: {name}')
            for target in re.findall(r'\]\(([^\s)]+)\)', text):
                if re.match(r'[a-z]+://|#|mailto:', target):
                    continue
                q = (p.parent / unquote(target.split('#')[0])).resolve()
                if not q.is_relative_to(root.resolve()) or not q.exists():
                    problems.append(f'broken or external local link: {name}: {target}')
    if problems:
        raise ValueError('\n'.join(problems))
    return {'status': 'PASS', 'files': len(expected) + 1, 'production_modules': len(modules),
            'source_snapshot': sha256(root / 'verification/source-lock.json')}


if __name__ == '__main__':
    try:
        print(json.dumps(check(), indent=2))
    except (ValueError, KeyError, OSError) as exc:
        print(f'RELEASE CHECK FAILED: {exc}', file=sys.stderr)
        sys.exit(1)
