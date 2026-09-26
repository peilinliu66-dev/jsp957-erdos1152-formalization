#!/usr/bin/env python3
"""Lexical source/import inspection only; this does not elaborate or prove Lean code."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]


def mask_comments_strings(s: str) -> str:
    # Retain line positions; handle nested Lean block comments and ordinary strings.
    out = list(s)
    i, depth, string = 0, 0, False
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif s.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if s[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            if s[i] == '\\' and i + 1 < len(s):
                out[i] = out[i+1] = ' '; i += 2
            elif s[i] == '"':
                out[i] = ' '; string = False; i += 1
            else:
                if s[i] != '\n': out[i] = ' '
                i += 1
        elif s.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif s.startswith('--', i):
            end = s.find('\n', i)
            if end < 0: end = len(s)
            out[i:end] = ' ' * (end - i); i = end
        elif s[i] == '"':
            out[i] = ' '; string = True; i += 1
        else:
            i += 1
    return ''.join(out)


EXTERNAL_ROOTS = {'Mathlib', 'Lean', 'Std', 'Init', 'Batteries', 'Aesop', 'Qq',
                  'Cli', 'LeanSearchClient', 'ProofWidgets', 'Plausible', 'ImportGraph'}


def inspect(root: Path = ROOT) -> dict:
    paths = sorted(p for p in root.rglob('*.lean')
                   if '.lake' not in p.parts and '.git' not in p.parts)
    modules = {p.relative_to(root).with_suffix('').as_posix().replace('/', '.'): p for p in paths}
    imports, holes, digests, read_errors = {}, {}, {}, []
    for name, p in modules.items():
        try:
            data = p.read_bytes()
            raw = data.decode('utf-8')
        except (OSError, UnicodeError) as exc:
            read_errors.append({'file': p.relative_to(root).as_posix(), 'error': str(exc)})
            imports[name] = []
            continue
        masked = mask_comments_strings(raw)
        imports[name] = []
        for match in re.finditer(r'(?m)^[ \t]*(?:(?:public|meta)[ \t]+)*import[ \t]+([^\n;]*)', masked):
            imports[name].extend(token for token in re.findall(r"[\w.']+", match.group(1))
                                 if token != 'all')
        found = []
        for m in re.finditer(r'\b(sorry|admit|axiom|sorryAx)\b|\bdebug\.skipKernelTC\b', masked):
            found.append({'token': m.group(), 'line': masked.count('\n', 0, m.start()) + 1})
        if found: holes[p.relative_to(root).as_posix()] = found
        digests[p.relative_to(root).as_posix()] = hashlib.sha256(data).hexdigest()
    reached, active, cycles, missing, external = set(), [], [], [], set()
    def visit(n: str) -> None:
        if n in active:
            cycles.append(active[active.index(n):] + [n]); return
        if n in reached: return
        reached.add(n); active.append(n)
        for dep in imports[n]:
            if dep in modules:
                visit(dep)
            elif dep.split('.')[0] in EXTERNAL_ROOTS:
                external.add(dep)
            else:
                missing.append({'module': n, 'unresolved_import': dep})
        active.pop()
    if 'JSP957Final' in modules:
        visit('JSP957Final')
    else:
        missing.append({'module': None, 'unresolved_import': 'JSP957Final'})
    active_holes = {modules[n].relative_to(root).as_posix(): holes[modules[n].relative_to(root).as_posix()]
                    for n in sorted(reached) if modules[n].relative_to(root).as_posix() in holes}
    return {'status': 'STATIC_ONLY_NOT_LEAN_VALIDATION', 'lean_elaborated': False,
            'has_blocking_findings': bool(cycles or missing or active_holes or read_errors),
            'read_errors': read_errors,
            'all_project_lean_files': len(paths), 'final_local_import_closure_count': len(reached),
            'final_local_import_closure': sorted(reached), 'local_imports': imports,
            'cycles_in_final_closure': cycles, 'unresolved_local_imports': missing,
            'external_imports_not_validated': sorted(external),
            'placeholder_tokens_all_project': holes, 'placeholder_tokens_final_closure': active_holes,
            'source_sha256': digests,
            'limitations': ['No Lean parsing, instance synthesis, tactic execution, or kernel checking.',
                            'Mathlib/Lean imports are external and not validated by this script.',
                            'Import inspection covers ordinary single-line module import syntax only.',
                            'Absence of literal placeholder tokens is not an axiom audit.']}


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    r = inspect(); args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(r, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(f"STATIC ONLY: {r['all_project_lean_files']} Lean files; "
          f"{r['final_local_import_closure_count']} local modules reachable from JSP957Final.")
    print(f"Import cycles: {len(r['cycles_in_final_closure'])}; "
          f"unresolved local imports: {len(r['unresolved_local_imports'])}; "
          f"literal placeholder files in final closure: {len(r['placeholder_tokens_final_closure'])}.")
    sys.exit(1 if r['has_blocking_findings'] else 0)
