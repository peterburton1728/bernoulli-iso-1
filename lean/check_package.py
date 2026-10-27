#!/usr/bin/env python3
"""Source-only packaging preflight; no Lean execution or third-party packages.

Usage: python3 check_package.py [PROJECT_ROOT]
This is a lexical advisory check, not Lean parsing, an axiom audit, or Palomar.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

EXCLUDE = {'.git', '.lake'}
ARTIFACT_SUFFIXES = {'.a', '.bc', '.dll', '.dylib', '.ilean', '.ir', '.o', '.obj',
                     '.olean', '.so', '.trace'}
ARTIFACT_TAILS = ('.olean.private', '.olean.server')
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}

def erase_comments_strings(text: str) -> str:
    """Keep line layout while ignoring nested Lean comments and string literals."""
    chars = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                chars[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                chars[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] not in '\r\n': chars[i] = ' '
                i += 1
        elif string:
            if text[i] == '\\':
                chars[i] = ' '; i += 1
                if i < len(text):
                    if text[i] not in '\r\n': chars[i] = ' '
                    i += 1
            else:
                if text[i] == '"': string = False
                if text[i] not in '\r\n': chars[i] = ' '
                i += 1
        elif text.startswith('--', i):
            while i < len(text) and text[i] not in '\r\n':
                chars[i] = ' '; i += 1
        elif text.startswith('/-', i):
            chars[i:i+2] = '  '; depth = 1; i += 2
        elif text[i] == '"':
            chars[i] = ' '; string = True; i += 1
        else:
            i += 1
    if depth or string:
        raise ValueError('unterminated comment or string in lexical scan')
    return ''.join(chars)

def scan(root: Path) -> dict:
    errors = []
    lean_files = []
    hashes = {}
    total = 0
    challenge_holes = 0
    for directory, dirs, files in os.walk(root, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in EXCLUDE and not (Path(directory)/d).is_symlink())
        for name in sorted(files):
            path = Path(directory)/name
            relative = path.relative_to(root).as_posix()
            if path.is_symlink():
                if path.suffix == '.lean': errors.append(f'{relative}: Lean symlink')
                continue
            if not path.is_file(): continue
            size = path.stat().st_size
            total += size
            if path.suffix in ARTIFACT_SUFFIXES or name.endswith(ARTIFACT_TAILS):
                errors.append(f'{relative}: committed build artifact outside .lake')
            if name == '.gitmodules': errors.append(f'{relative}: remove submodules from release')
            with path.open('rb') as handle:
                if handle.read(256).startswith(b'version https://git-lfs.github.com/spec/v1'):
                    errors.append(f'{relative}: Git LFS pointer')
            if path.suffix != '.lean': continue
            data = path.read_bytes()
            hashes[relative] = hashlib.sha256(data).hexdigest()
            lines = data.count(b'\n') + bool(data and not data.endswith(b'\n'))
            lean_files.append({'path': relative, 'lines': lines, 'bytes': len(data)})
            if lines > 10000: errors.append(f'{relative}: {lines} physical lines exceeds 10000')
            try:
                source = data.decode('utf-8')
                code = erase_comments_strings(source)
            except (UnicodeError, ValueError) as exc:
                errors.append(f'{relative}: {exc}'); continue
            if name != 'lakefile.lean' and not re.match(r'\s*module\b', code):
                errors.append(f'{relative}: first command must be module')
            for match in re.finditer(r'\b(sorry|admit|axiom)\b', code):
                token = match.group()
                line = code.count('\n', 0, match.start()) + 1
                if relative == 'Challenge.lean' and token == 'sorry':
                    challenge_holes += 1
                else:
                    errors.append(f'{relative}:{line}: proof placeholder/new axiom token {token}')
            if relative == 'Challenge.lean':
                if lines > 1000 or len(data) > 100*1024:
                    errors.append('Challenge.lean: exceeds 1000 lines or 100 KiB')
                if re.search(r'^\s*axiom\s+unequal_finite_bernoulli_shifts', code, re.M):
                    errors.append('Challenge.lean: compared declaration must be theorem, not axiom')
    if challenge_holes != 1:
        errors.append(f'Challenge.lean: expected exactly one deliberate sorry; found {challenge_holes}')
    if total > 500*1024*1024: errors.append(f'checkout {total} bytes exceeds 500 MiB')
    required = ['lean-toolchain','lake-manifest.json','formalization.yaml',
                'Challenge.lean','Solution.lean','comparator.json']
    for name in required:
        if not (root/name).is_file(): errors.append(f'missing {name}')
    if sum((root/name).is_file() for name in ['lakefile.lean','lakefile.toml']) != 1:
        errors.append('exactly one Lakefile is required')
    license_re = re.compile(r'^(?:licen[cs]e|copying|unlicense|ofl)(?:\.(?:md|markdown|txt))?$', re.I)
    licenses = [p.name for p in root.iterdir() if p.is_file() and license_re.fullmatch(p.name)]
    if len(licenses) != 1: errors.append(f'exactly one root license required; found {licenses}')
    try:
        config = json.loads((root/'comparator.json').read_text())
        required_config = {'challenge_module','solution_module','theorem_names','permitted_axioms'}
        if not required_config <= config.keys(): errors.append('Comparator required keys missing')
        if not config.keys() <= required_config | {'definition_names','enable_nanoda'}:
            errors.append('Comparator unknown keys')
        if not set(config['permitted_axioms']) <= STANDARD_AXIOMS:
            errors.append('Comparator nonstandard axioms')
        if not config['theorem_names']: errors.append('Comparator theorem_names empty')
    except (ValueError, KeyError, OSError, TypeError) as exc:
        errors.append(f'Comparator configuration: {exc}')
    return {'check':'source-only lexical packaging scan','errors':errors,
            'checkout_bytes_excluding_git_lake_symlinks':total,
            'lean_source_count':len(lean_files),'challenge_deliberate_sorry_count':challenge_holes,
            'lean_files':lean_files,'observed_lean_sha256':hashes,
            'limits':'Does not parse Lean, authenticate manifests, detect all metaprogramming, inspect axioms/proof terms, validate YAML/licensee, or run Palomar.'}

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', nargs='?', default='.')
    args = parser.parse_args()
    result = scan(Path(args.root).resolve())
    print(json.dumps(result, indent=2))
    return 1 if result['errors'] else 0

if __name__ == '__main__':
    sys.exit(main())
