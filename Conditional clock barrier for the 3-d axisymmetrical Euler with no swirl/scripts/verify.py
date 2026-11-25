#!/usr/bin/env python3
"""Reproduce source checks, a build, exact types/axioms, and full kernel replay."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import time

from check_release import check, ROOT


def require_local_directory(path):
    if not path.resolve().is_relative_to(ROOT):
        raise RuntimeError(f'Directory resolves outside this checkout: {path.name}')
    while path != ROOT:
        if path.is_symlink():
            raise RuntimeError('Verification requires independent directories without symlink ancestors')
        path = path.parent


def run_checks(args, result, output):
    result['source'] = check()
    env = dict(os.environ)
    for key in ['LEAN_PATH', 'LEAN_SRC_PATH', 'LAKE_PACKAGES_DIR', 'LAKE_HOME',
                'ELAN_TOOLCHAIN', 'LEAN_SYSROOT']:
        env.pop(key, None)
    require_local_directory(ROOT / '.lake/build')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    for package in manifest['packages']:
        path = ROOT / '.lake/packages' / package['name']
        require_local_directory(path)
        commit = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'],
                                         env=env, text=True).strip()
        if commit != package['rev']:
            raise RuntimeError(f'Dependency revision mismatch: {package["name"]}')
        subprocess.run(['git', '-C', str(path), 'diff', '--quiet', 'HEAD', '--'],
                       env=env, check=True)
    lock = json.loads((ROOT / 'verification/source-lock.json').read_text())
    commands = []
    if not args.skip_build:
        commands.append(('build', ['lake', '--no-cache', '--wfail', 'build', *lock['modules']]))
    commands.extend([
        ('exact-types-and-axioms', ['lake', '--no-cache', 'env', 'lean',
                                  '-DwarningAsError=true', 'verification/Statements.lean']),
        ('kernel-replay', ['lake', '--no-cache', 'env', 'lean', '--run',
                           'verification/Replay.lean', *lock['modules']]),
    ])
    for name, command in commands:
        print(f'Running {name}; output: .verification/{name}.log', flush=True)
        start = time.monotonic()
        with (output / f'{name}.log').open('w') as log:
            done = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        step = {'name': name, 'exit_code': done.returncode,
                'seconds': round(time.monotonic() - start, 3)}
        result['steps'].append(step)
        text = (output / f'{name}.log').read_text()
        if done.returncode:
            (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
            raise RuntimeError(f'{name} failed; see .verification/{name}.log')
        if name == 'exact-types-and-axioms':
            closures = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S)
            closures += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", text)]
            expected = set(lock['axiom_exports'])
            if {n for n, _ in closures} != expected or len(closures) != len(expected):
                raise RuntimeError('Incomplete or duplicate axiom audit output')
            for theorem, axioms in closures:
                actual = {x.strip() for x in axioms.split(',') if x.strip()}
                if not actual <= {'propext', 'Classical.choice', 'Quot.sound'}:
                    raise RuntimeError(f'Unexpected axiom in {theorem}: {actual}')
            step['axiom_closures'] = len(closures)
        elif name == 'kernel-replay':
            replayed = re.findall(r'^REPLAY_OK (\S+) (\d+)$', text, re.M)
            if {n for n, _ in replayed} != set(lock['modules']) or len(replayed) != len(lock['modules']):
                raise RuntimeError('Incomplete kernel replay')
            step['modules'] = len(replayed)
            step['constants'] = sum(int(n) for _, n in replayed)
            step['positive_proof_paths'] = text.count('PROOF_ROUTE_OK ')
            step['excluded_proof_paths'] = text.count('OLD_ROUTE_ABSENT ')
            if (step['positive_proof_paths'], step['excluded_proof_paths']) != (10, 6):
                raise RuntimeError('Incomplete proof route audit')
        print(f'{name}: PASS ({step["seconds"]} seconds)', flush=True)
    result['status'] = 'PASS'
    (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print('VERIFICATION PASS; details in .verification/result.json', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-build', action='store_true',
                        help='Use only after a successful build of this exact source tree.')
    args = parser.parse_args()
    output = ROOT / '.verification'
    require_local_directory(output)
    output.mkdir(exist_ok=True)
    result = {'status': 'RUNNING', 'steps': []}
    path = output / 'result.json'
    path.write_text(json.dumps(result, indent=2) + '\n')
    try:
        run_checks(args, result, output)
    except BaseException as exc:
        result.update(status='FAIL', error=str(exc))
        path.write_text(json.dumps(result, indent=2) + '\n')
        raise


if __name__ == '__main__':
    main()
