"""Acceptance tests of the exported-effects census (d-effects, piece A).

Standard library only, Python 3.11.9, run with -I -B. Two hosts, chosen explicitly; nothing skips:

    python3 -I -B tests/test_census.py --host mac --root DIR --owner-ask OWNER-ASK.md [--tmp WRITABLE]
        The workflow's and the census's text, the owner's commands (run against a local bare
        repository and a stand-in gh, every scratch folder under --tmp, else TMPDIR), and the
        validator's refusals.
    python3 -I -B tests/test_census.py --host github --planted P.json --edition E.json \
        --edition-dir DIR --commit SHA --out OUT
        The same static checks, the planted self-test, the census's own failures and the edition.

Exit 0 when every test passes, 1 when any fails, 2 on a usage error.
"""

import argparse
import copy
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCHEMA = 'stoicheia.effects-census.exported/1'
EDITION_COMMIT = '391da4e353e0c6e05b25afe5e17f1f2e3916bf64'
LEAN_URL = 'https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst'
LEAN_SHA256 = '7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d'
WORKFLOW = Path('.github/workflows/effects-census.yml')
FAMILIES = {'instance', 'simp', 'reducibility', 'notation', 'macro', 'coercion', 'unif_hint', 'default_instance',
            'alias', 'class', 'csimp', 'attribute', 'grind'}
PARTS = {'toolchain', 'foundations', 'edition'}
EFFECT_FIELDS = {'family': str, 'extension': str, 'module': str, 'part': str, 'outside_foundations': bool,
                 'scope': str, 'keyed_on': list, 'own_keyed': bool, 'escapes': bool, 'coercion': bool, 'detail': str,
                 'payload': dict}
SUMMARY_INTS = ('modules_walked', 'toolchain_modules', 'foundations_modules', 'edition_modules', 'effects',
                'outside_foundations', 'escaping_outside_foundations', 'own_keyed_outside_foundations',
                'scoped_outside_foundations')
# Every field of each 4.35 entry type, under the names Census.lean's field sweep keeps it (simp and notation
# by their entry kind). A payload without one of them is refused (payload_incomplete).
PAYLOAD_FIELDS = {
    'instance': {'keys', 'val', 'priority', 'global_name', 'synth_order', 'attr_kind'},
    'simp/theorem': {'entry', 'simp_set', 'keys', 'level_params', 'proof', 'priority', 'post', 'perm', 'origin', 'rfl',
                     'backward_rfl'},
    'simp/unfold': {'entry', 'simp_set', 'decl'},
    'simp/unfold_by_equations': {'entry', 'simp_set', 'decl', 'theorems'},
    'reducibility': {'decl', 'status'},
    'notation/token': {'entry', 'token'},
    'notation/kind': {'entry', 'kind'},
    'notation/category': {'entry', 'category', 'decl', 'behavior'},
    'notation/parser': {'entry', 'category', 'decl', 'priority'},
    'macro': {'attribute', 'key', 'decl'},
    'coercion': {'decl', 'num_args', 'coercee', 'type'},
    'unif_hint': {'keys', 'val'},
    'default_instance': {'class', 'instance', 'priority'},
    'alias': {'alias', 'of'},
    'class': {'name', 'out_params', 'out_level_params'},
    'csimp': {'from', 'to', 'thm'},
    'attribute': {'attribute', 'decl', 'value'},
    'grind/ext': {'entry', 'grind_set', 'decl'},
    'grind/funCC': {'entry', 'grind_set', 'decl'},
    'grind/cases': {'entry', 'grind_set', 'decl', 'eager'},
    'grind/ematch': {'entry', 'grind_set', 'level_params', 'proof', 'num_params', 'patterns', 'symbols', 'origin', 'kind',
                     'min_indexable', 'cnstrs'},
    'grind/inj': {'entry', 'grind_set', 'level_params', 'proof', 'symbols', 'origin'},
}
ENTRY_FAMILIES = ('simp', 'notation', 'grind')   # payloads told apart by their `entry`
# A discrimination-tree key in full: each constructor of DiscrTree.Key with its fields (a literal: nat or str).
KEY_FIELDS = {'star': set(), 'other': set(), 'arrow': set(), 'fvar': {'fvar', 'arity'}, 'const': {'name', 'arity'},
              'proj': {'struct', 'index', 'arity'}}
ORIGIN_FIELDS = {'simp': {'decl': {'decl', 'post', 'inv'}, 'other': {'name'}}, 'grind': {'decl': {'decl'}}}
# A grind symbol in full: each constructor of HeadIndex with its fields (a literal: nat or str).
HEAD_FIELDS = {'fvar': {'fvar'}, 'mvar': {'mvar'}, 'const': {'name'}, 'proj': {'struct', 'index'}, 'sort': set(),
               'lam': set(), 'forallE': set()}


# ---------------------------------------------------------------------------------------------
# The validator: what a census document must satisfy before anyone reads its list.
# ---------------------------------------------------------------------------------------------

def schema_problems(doc):
    """Named defects in the document's shape; never raises on malformed input."""
    if not isinstance(doc, dict):
        return ['schema: not an object']
    out = []
    if doc.get('schema') != SCHEMA:
        out.append(f'schema: expected {SCHEMA}, got {doc.get("schema")!r}')
    for key, kind in (('claim', str), ('not_claimed', list), ('reviewed', list), ('modules', list), ('effects', list),
                      ('bookkeeping', list), ('summary', dict), ('reasons', list), ('foundations', list),
                      ('edition_commit', str), ('registry', list), ('registry_gap', list),
                      ('reviewed_unregistered', list)):
        if not isinstance(doc.get(key), kind):
            out.append(f'schema: {key} is not a {kind.__name__}')
    if doc.get('verdict') not in ('complete', 'incomplete'):
        out.append(f'schema: verdict {doc.get("verdict")!r}')
    if out:
        return out
    for i, m in enumerate(doc['modules']):
        if not isinstance(m, dict) or not isinstance(m.get('name'), str) or m.get('part') not in PARTS:
            out.append(f'schema: modules[{i}] lacks a name or a part')
    for i, r in enumerate(doc['effects']):
        if not isinstance(r, dict):
            out.append(f'schema: effects[{i}] is not an object')
            continue
        for key, kind in EFFECT_FIELDS.items():
            if not isinstance(r.get(key), kind):
                out.append(f'schema: effects[{i}].{key} is not a {kind.__name__}')
        if r.get('family') not in FAMILIES:
            out.append(f'schema: effects[{i}] has an unknown family {r.get("family")!r}')
    for key in SUMMARY_INTS:
        v = doc['summary'].get(key)
        if not isinstance(v, int) or isinstance(v, bool):
            out.append(f'schema: summary.{key} is not an integer')
    for i, r in enumerate(doc['reviewed']):
        if not (isinstance(r, dict) and r.get('reason') and r.get('kind') in ('attr_tag', 'attr_map', 'tag', 'map', 'decl', 'other')):
            out.append(f'schema: reviewed[{i}] lacks a kind or a reason')
    return out


def key_problem(key):
    """Why a payload key is not a full DiscrTree.Key, or None."""
    if not isinstance(key, dict) or key.get('key') not in set(KEY_FIELDS) | {'lit'}:
        return 'not a full key'
    if key['key'] == 'lit':
        return None if ('nat' in key) != ('str' in key) else 'a literal key without its value'
    missing = KEY_FIELDS[key['key']] - set(key)
    return f'a {key["key"]} key without {", ".join(sorted(missing))}' if missing else None


def payload_problems(i, r):
    """Named defects of one record's payload: a field of its entry type missing, or a key not in full."""
    p = r['payload']
    kind = r['family'] + (f'/{p.get("entry")}' if r['family'] in ENTRY_FAMILIES else '')
    where = f'payload_incomplete: effects[{i}] {r["module"]} {kind}'
    want = PAYLOAD_FIELDS.get(kind)
    if want is None:
        return [f'{where}: no such entry kind']
    out = [f'{where} lacks {field}' for field in sorted(want - set(p))]
    keys = p.get('keys', [])
    if not isinstance(keys, list):
        out.append(f'{where} keys is not a list')
    else:
        out += [f'{where} keys[{j}] is {why}' for j, why in enumerate(map(key_problem, keys)) if why]
    origin, origins = p.get('origin'), ORIGIN_FIELDS.get(r['family'], {})
    if 'origin' in want and 'origin' in p and not (isinstance(origin, dict) and origin.get('kind') in origins
                                                  and origins[origin['kind']] <= set(origin)):
        out.append(f'{where} origin is not a decoded origin')
    for j, h in enumerate(p.get('symbols', []) if isinstance(p.get('symbols', []), list) else [None]):
        if not (isinstance(h, dict) and (h.get('head') in HEAD_FIELDS and HEAD_FIELDS[h['head']] <= set(h)
                                         or h.get('head') == 'lit' and ('nat' in h) != ('str' in h))):
            out.append(f'{where} symbols[{j}] is not a full symbol')
    return out


def env_list(doc):
    """The ENV list: exported effects outside the foundations that escape their file."""
    return [r for r in doc['effects'] if r['outside_foundations'] and r['escapes']]


def acceptance_problems(doc, commit):
    """Every refusal, by name. `commit` None skips the edition-commit check (the planted run)."""
    out = schema_problems(doc)
    if out:
        return out
    if commit is not None and doc['edition_commit'] != commit:
        out.append(f'edition_commit_mismatch: {doc["edition_commit"]!r}, expected {commit}')
    if doc['verdict'] == 'incomplete':
        out.append('census_incomplete: ' + '; '.join(map(str, doc['reasons'])))
    elif doc['reasons']:
        out.append('verdict_inconsistent: complete with reasons')
    if not any('file-local' in n for n in doc['not_claimed']):
        out.append('claim_inconsistent: the exported census must say it does not list file-local effects')
    for i, r in enumerate(doc['effects']):
        if r['scope'] not in ('global', 'scoped'):
            out.append(f'local_in_olean: effects[{i}] {r["module"]} scope {r["scope"]}')
        if r['escapes'] != (r['scope'] in ('global', 'scoped') and not r['own_keyed']):
            out.append(f'escapes_inconsistent: effects[{i}] {r["module"]} {r["family"]}')
        if r['outside_foundations'] != (r['part'] == 'edition'):
            out.append(f'flag_inconsistent: effects[{i}] {r["module"]}')
        out += payload_problems(i, r)
    if doc['summary']['escaping_outside_foundations'] != len(env_list(doc)):
        out.append('summary_mismatch: escaping_outside_foundations')
    if doc['summary']['modules_walked'] != len(doc['modules']):
        out.append('summary_mismatch: modules_walked')
    statuses = {e.get('status') for e in doc['registry'] if isinstance(e, dict)}
    if not doc['registry'] or not statuses <= {'decoded', 'reviewed', 'neither'}:
        out.append('registry_inconsistent: every registered extension needs a status')
    elif doc['registry_gap'] != [e['extension'] for e in doc['registry'] if e['status'] == 'neither']:
        out.append('registry_inconsistent: registry_gap is not the registry\'s "neither" entries')
    return out


def gap_report(paths):
    """The registry gap of each census document: every registered extension it neither decodes nor
    reviews, populated or not, and every reviewed name no registered extension has."""
    lines = []
    for path in paths:
        try:
            doc = load(path)
        except (OSError, ValueError) as exc:
            lines.append(f'{path}: not read ({exc})')
            continue
        gap, stale = doc.get('registry_gap', []), doc.get('reviewed_unregistered', [])
        lines.append(f'{path}: {len(doc.get("registry", []))} registered; {len(gap)} neither decoded nor reviewed; '
                     f'{len(stale)} reviewed names not registered; verdict {doc.get("verdict")}')
        lines += [f'  neither: {n}' for n in gap] + [f'  reviewed, not registered: {n}' for n in stale]
        lines += [f'  reason: {r}' for r in doc.get('reasons', [])]
    return lines


def _problems_of(doc):
    try:
        return acceptance_problems(doc, None)
    except AssertionError as exc:
        return [str(exc)]


def recs(doc, module=None, family=None, scope=None):
    return [r for r in doc['effects'] if (module is None or r['module'] == module)
            and (family is None or r['family'] == family) and (scope is None or r['scope'] == scope)]


def by_target(rs):
    return {r['target']: r for r in rs}


def load(path):
    with open(path, encoding='utf-8') as stream:
        return json.load(stream)


class Missing(dict):
    """An output its step did not write: every test that reads it fails, naming the file."""
    def __init__(self, path):
        super().__init__()
        self.path = path

    def __getitem__(self, key):
        raise AssertionError(f'{self.path} was not written: its census step failed')

    def get(self, key, *default):
        return self[key]


def load_or_missing(path):
    return load(path) if Path(path).is_file() else Missing(path)


def fixture():
    return load(HERE / 'fixtures' / 'minimal-effects.json')


# ---------------------------------------------------------------------------------------------
# Static: the workflow as written. Runs on both hosts.
# ---------------------------------------------------------------------------------------------

def workflow_text(ctx):
    return (Path(ctx.root) / WORKFLOW).read_text(encoding='utf-8')


def steps_of(text):
    return re.split(r'\n(?=      - )', text)


def test_workflow_pins_every_action_by_commit(ctx):
    text = workflow_text(ctx)
    uses = re.findall(r'^\s*(?:-\s*)?uses:\s*(\S+)', text, re.M)
    assert uses, 'no action used'
    for ref in uses:
        assert re.fullmatch(r'[\w.-]+/[\w.-]+@[0-9a-f]{40}', ref), f'not pinned by commit: {ref}'
    assert re.search(r'^\s*runs-on:\s*ubuntu-24\.04\s*$', text, re.M), 'runner not pinned'
    walls = [int(x) for x in re.findall(r'^\s*timeout-minutes:\s*(\d+)\s*$', text, re.M)]
    assert walls and all(0 < w <= 45 for w in walls), f'job wall {walls}'
    assert re.search(r'python-version:\s*"3\.11\.9"', text), 'Python not pinned to 3.11.9'


def test_workflow_reads_only_and_verifies_lean(ctx):
    text = workflow_text(ctx)
    block = re.search(r'^permissions:\n((?:[ \t]+\S.*\n)+)', text, re.M)
    assert block and [l.strip() for l in block.group(1).splitlines()] == ['contents: read'], \
        'permissions must be contents: read only'
    assert 'secrets.' not in text and 'id-token' not in text, 'a secret or an identity token is used'
    checkouts = len(re.findall(r'uses:\s*actions/checkout@', text))
    assert checkouts == 2 and text.count('persist-credentials: false') == checkouts
    assert re.search(r'repository:\s*dodecaplex-co/stoicheia\s*$', text, re.M)
    assert re.search(r'ref:\s*' + EDITION_COMMIT + r'\s*$', text, re.M), 'edition not at the frozen commit'
    assert 'git -C edition rev-parse HEAD' in text and 'edition_commit_mismatch' in text
    assert re.search(r'^on:\n\s+push:\n\s+branches:\s*\[\s*effects-census\s*\]', text, re.M), 'trigger'
    assert 'pull_request' not in text and 'workflow_run' not in text
    assert not re.search(r'git push|gh (api|pr|release|workflow|repo|run)|curl .*-X ?(POST|PUT|PATCH|DELETE)', text)
    assert 'install_lean.sh' not in text and 'elan' not in text, 'an unverified install path'
    assert f'LEAN_URL: {LEAN_URL}' in text and f'LEAN_SHA256: {LEAN_SHA256}' in text
    lean = [s for s in steps_of(text) if 'LEAN_URL' in s and 'curl' in s]
    assert len(lean) == 1 and len(re.findall(r'\bcurl\b|\bwget\b', text)) == 1, 'exactly one download'
    step = lean[0]
    assert 'set -euo pipefail' in step and 'sha256sum -c -' in step and '||' not in step
    assert step.index('sha256sum -c -') < step.index('zstd -dc'), 'unpacked before it is checked'
    upload = [s for s in steps_of(text) if 'actions/upload-artifact@' in s]
    assert len(upload) == 1 and "if: ${{ !cancelled() }}" in upload[0], 'the artifact must upload when red'
    # Every step after the build runs when an earlier one fails, so one run shows everything (run 2).
    for name in ('Self-test on the planted package', "The census's own failures", 'Census of the edition',
                 'Report every registered extension', 'Acceptance tests'):
        step = [s for s in steps_of(text) if f'- name: {name}' in s]
        assert len(step) == 1 and "if: ${{ !cancelled() }}" in step[0], f'{name} must run after a failure'
        assert 'continue-on-error' not in step[0], f'{name} must still fail the job'
    gap = [s for s in steps_of(text) if '--host gap' in s]
    assert len(gap) == 1 and 'out/planted-effects.json' in gap[0] and 'out/effects.json' in gap[0] \
        and 'out/registry-gap.txt' in gap[0], 'the registry gap is reported for both census runs'
    assert '--edition-commit "$EDITION_COMMIT"' in text and '--foundation Elements.Foundations' in text \
        and '--foundation Elements.Figure' in text


# ---------------------------------------------------------------------------------------------
# Static: the census's field sweep, each row against the decoder it names. Runs on both hosts.
# ---------------------------------------------------------------------------------------------

SWEEP_ROW = re.compile(r'^\| ([^|]+?) \| ([^|]+?) \| (Lean/[^|]+?:\d+) \| (\w+) \| ([^|]+?) \|$', re.M)
LEAN_DEF = r'^(?:(?:unsafe|private|partial) )*def {}(?![\w.])'
LEAN_NEXT = re.compile(r'^(?:(?:unsafe|private|partial) )*def |^structure |^/-|^end |^@\[|^abbrev |^namespace ', re.M)
LEAN_STRING = r'"((?:[^"\\]|\\.)*)"'


def lean_body(text, name):
    """The source of one Lean definition, up to the next declaration or comment block."""
    m = re.search(LEAN_DEF.format(re.escape(name)), text, re.M)
    assert m, f'Census.lean has no definition {name}'
    end = LEAN_NEXT.search(text, m.end())
    return text[m.start():end.start() if end else len(text)]


def code_and_strings(body):
    """The body's code with comments and string literals blanked, and the set of its string literals."""
    body = re.sub(r'/-.*?-/', ' ', body, flags=re.S)
    strings = set(re.findall(LEAN_STRING, body))
    code = re.sub(r'--[^\n]*', ' ', re.sub(LEAN_STRING, '""', body))
    return code, strings


def test_census_keeps_every_field(ctx):
    text = (Path(ctx.root) / 'Census.lean').read_text(encoding='utf-8')
    rows = SWEEP_ROW.findall(text)
    table = [line for line in text.splitlines() if line.startswith('| ')]
    assert len(rows) >= 80 and len(rows) == len(table) - 1, f'{len(rows)} of the sweep\'s {len(table) - 1} rows parse'
    _, record_strings = code_and_strings(lean_body(text, 'Effect.json'))
    for entry, field, source, decoder, kept in rows:
        code, strings = code_and_strings(lean_body(text, decoder))
        where = f'{entry} {field} ({source}), in {decoder}'
        reads = re.compile(r'\.' + re.escape(field) + r'(?![\w?])')
        if kept.startswith('refused'):
            lines = [line for line in code.splitlines() if reads.search(line)]
            assert lines and all('.error' in line for line in lines), f'{where}: marked refused, but not refused'
            continue
        if kept.startswith('not behaviour-bearing'):
            assert len(kept) > len('not behaviour-bearing because '), f'{where}: no reason given'
            continue
        if re.fullmatch(r"[A-Za-z_]\w*\??", field):
            assert reads.search(code), f'{where}: the field is not read'
        names = re.findall(r'(record )?"([^"]+)"', kept)
        assert names or kept.startswith('value ('), f'{where}: kept as what?'
        for record, name in names:
            assert name in (record_strings if record else strings), f'{where}: "{name}" is not written'
    refusals = lean_body(text, 'decodeAll')
    assert 'unknown_payload' in refusals and '.refusal.isNone' in code_and_strings(refusals)[0], \
        'an entry it cannot decode is not refused'
    assert 'd.unknownPayload' in code_and_strings(lean_body(text, 'runEnv'))[0], 'unknown_payload is not a reason'
    # The run-time registry (run 2): read from the registry ref, written whole into the JSON.
    code, strings = code_and_strings(lean_body(text, 'runEnv'))
    assert 'persistentEnvExtensionsRef' in code and {'registry', 'registry_gap', 'reviewed_unregistered'} <= strings, \
        'the census must write the run-time registry'
    reviewed = text[text.index('def reviewed : Array Reviewed := #['):]
    reviewed = set(re.findall(r'⟨"([^"]+)", "(?:attr_tag|attr_map|tag|map|decl|other)"', reviewed[:reviewed.index(']\n')]))
    for name, want in RUN2_EXTENSIONS.items():
        user = re.sub(r'^_private\.[\w.]+?\.0\.', '', name)
        assert (user in reviewed) == (want == 'reviewed'), (name, want)
    known = code_and_strings(lean_body(text, 'mkKnown'))[0]
    assert 'Grind.extensionMapRef' in known and re.search(r'in grindSets do\s+decoded := decoded\.insert ext\.ext\.name', known), \
        'every grind set must count as decoded'
    assert 'decodeGrind s k.grindSets' in code_and_strings(lean_body(text, 'decodeAll'))[0], 'grind entries must be decoded'


# ---------------------------------------------------------------------------------------------
# Mac: the owner's commands, run against a local bare repository and a stand-in gh.
# ---------------------------------------------------------------------------------------------

FAKE_GH = r'''#!/bin/bash
# A stand-in for gh, faithful in what the owner's scripts depend on. Runs are made by the push itself
# (POST_RECEIVE) and kept in runs.tsv (id, commit, workflow path); a run keeps its commit whatever later
# happens to the branch, and a deleted run is gone. `api .../actions/runs?head_sha=` answers as the REST
# API does, and `--jq` is applied with jq. `run list --workflow FILE` resolves FILE on the default branch,
# as GitHub does, and fails with HTTP 404 when that branch lacks it (run 1). A run's status: completed,
# or in_progress until it is cancelled (FAKE_RUNNING), or for ever (FAKE_NEVER_STOPS). While
# FAKE_NO_RUN is set, no run is listed yet. Every write is logged.
set -u
log="$FAKE_DIR/gh.log"; runs="$FAKE_DIR/runs.tsv"; touch "$runs"
default=${FAKE_DEFAULT:-main}
arg() { local want=$1; shift; while [ $# -gt 1 ]; do [ "$1" = "$want" ] && { printf '%s' "$2"; return; }; shift; done; }
run_sha() { if [ -n "${FAKE_RUN_SHA:-}" ]; then echo "$FAKE_RUN_SHA"; else awk -F'\t' -v id="$1" '$1 == id {print $2}' "$runs"; fi; }
status() {
  if [ -n "${FAKE_NEVER_STOPS:-}" ]; then echo in_progress
  elif [ -n "${FAKE_RUNNING:-}" ] && ! grep -q "^run cancel $1\$" "$log" 2>/dev/null; then echo in_progress
  else echo completed; fi
}
# A run that does not exist (never made, or deleted) answers HTTP 404, as GitHub does.
case "$1 $2" in
  "run view"|"run cancel"|"run delete")
     if ! awk -F'\t' -v id="$3" '$1 == id {found = 1} END {exit !found}' "$runs"; then
       echo "failed to get run: HTTP 404: Not Found (https://api.github.com/repos/$REPO/actions/runs/$3?exclude_pull_requests=true)" >&2
       exit 1
     fi ;;
esac
case "$1 $2" in
  "repo view") echo "$default" ;;
  "run list")
     wf=$(arg --workflow "$@")
     if [ -n "$wf" ] && ! git --git-dir="$FAKE_BARE" cat-file -e "refs/heads/$default:.github/workflows/$wf" 2>/dev/null; then
       echo "HTTP 404: workflow $wf not found on the default branch" >&2; exit 1
     fi
     echo "fake gh: run list is modelled only as far as the default-branch check" >&2; exit 9 ;;
  "api repos/$REPO/actions/runs?"*)
     query=${2#*\?}
     sha=$(printf '%s\n' "$query" | tr '&' '\n' | sed -n 's/^head_sha=//p')
     event=$(printf '%s\n' "$query" | tr '&' '\n' | sed -n 's/^event=//p')
     json=$(awk -F'\t' -v s="$sha" -v ev="$event" -v hide="${FAKE_NO_RUN:-}" '
       BEGIN { n = 0; out = "" }
       hide == "" && $2 == s && (ev == "" || ev == "push") {
         out = out (n++ ? "," : "") sprintf("{\"id\":%s,\"head_sha\":\"%s\",\"path\":\"%s\",\"event\":\"push\"}", $1, $2, $3) }
       END { printf "{\"total_count\":%d,\"workflow_runs\":[%s]}", n, out }' "$runs")
     filter=$(arg --jq "$@")
     if [ -z "$filter" ]; then printf '%s\n' "$json"
     else command -v jq >/dev/null || { echo "fake gh: jq is needed to apply --jq" >&2; exit 9; }
          printf '%s' "$json" | jq -r "$filter"; fi ;;
  "run view") case "$*" in *headSha*) echo "$(status "$3") $(run_sha "$3")";; *) status "$3";; esac ;;
  "run cancel") echo "$1 $2 $3" >> "$log" ;;
  "run delete") echo "$1 $2 $3" >> "$log"
     awk -F'\t' -v id="$3" '$1 != id' "$runs" > "$runs.new" && mv "$runs.new" "$runs"
     if [ -n "${FAKE_MOVE_ON_DELETE:-}" ]; then
       git --git-dir="$FAKE_BARE" update-ref refs/heads/effects-census "$(git --git-dir="$FAKE_BARE" rev-parse refs/heads/main)"
     fi ;;
  *) echo "fake gh: unexpected $*" >&2; exit 9 ;;
esac
'''

# The probe's side of a push: GitHub starts one run of each workflow file in the pushed commit (ids
# from 4242) and, here, also a run of another workflow for the same commit (as code scanning's default
# setup does), which the lookup must leave out.
POST_RECEIVE = r'''#!/bin/bash
dir='@FAKE_DIR@'
touch "$dir/runs.tsv"
while read -r old new ref; do
  [ "$ref" = refs/heads/effects-census ] || continue
  case "$new" in *[!0]*) ;; *) continue ;; esac
  if git cat-file -e "$new:.github/workflows/effects-census.yml" 2>/dev/null; then
    id=$(cat "$dir/next_id" 2>/dev/null || echo 4242)
    printf '%s\t%s\t%s\n' "$id" "$new" .github/workflows/effects-census.yml >> "$dir/runs.tsv"
    echo $((id + 1)) > "$dir/next_id"
  fi
  decoy=$((9000 + $(wc -l < "$dir/runs.tsv")))
  printf '%s\t%s\t%s\n' "$decoy" "$new" dynamic/github-code-scanning/codeql >> "$dir/runs.tsv"
done
'''

# A stand-in for git whose branch deletion meets GitHub's HTTP 500 and is not applied (run 2's undo).
FLAKY_GIT = r'''#!/bin/bash
for a in "$@"; do
  if [ "$a" = :refs/heads/effects-census ]; then
    echo "error: RPC failed; HTTP 500 curl 22 The requested URL returned error: 500" >&2; exit 1
  fi
done
exec "$REAL_GIT" "$@"
'''

# A stand-in for git whose push reaches the server and then reports a transport failure, as when the
# connection drops after the server has accepted the push.
LOSSY_GIT = r'''#!/bin/bash
"$REAL_GIT" "$@"; status=$?
if [ "$status" = 0 ] && [ "${1:-}" = -C ] && [ "${3:-}" = push ]; then
  echo "fatal: the remote end hung up unexpectedly" >&2; exit 128
fi
exit "$status"
'''


def owner_blocks(path):
    text = Path(path).read_text(encoding='utf-8')
    blocks = dict(re.findall(r'```bash (push|undo)\n(.*?)```', text, re.S))
    assert set(blocks) == {'push', 'undo'}, 'OWNER-ASK.md needs a ```bash push and a ```bash undo block'
    return blocks


def run_bash(script, env, cwd):
    return subprocess.run(['bash', '-c', script], env=env, cwd=cwd, capture_output=True, text=True, timeout=120)


def git(*args, cwd=None, env=None):
    return subprocess.run(['git', *args], cwd=cwd, env=env, check=True, capture_output=True, text=True).stdout.strip()


def make_world(tmp, with_main=True):
    tmp = Path(tmp)
    (tmp / 'home').mkdir()
    (tmp / 'scratch').mkdir()
    env = {'PATH': f'{tmp}:{os.environ["PATH"]}', 'HOME': str(tmp / 'home'), 'TMPDIR': str(tmp / 'scratch'),
           'GIT_AUTHOR_NAME': 'Test', 'GIT_AUTHOR_EMAIL': 'test@example.invalid', 'GIT_COMMITTER_NAME': 'Test',
           'GIT_COMMITTER_EMAIL': 'test@example.invalid', 'GIT_CONFIG_NOSYSTEM': '1',
           'FAKE_DIR': str(tmp), 'FAKE_BARE': str(tmp / 'origin.git'), 'REPO': 'example/probe',
           'REMOTE': f'file://{tmp / "origin.git"}', 'GH': str(tmp / 'gh'),
           # The record's folder does not exist yet: the push must create it.
           'RECORD': str(tmp / 'records' / 'd-effects' / 'record.txt'), 'POLL_SECONDS': '0'}
    git('init', '-q', '--bare', str(tmp / 'origin.git'), env=env)
    hook = tmp / 'origin.git' / 'hooks' / 'post-receive'
    hook.write_text(POST_RECEIVE.replace('@FAKE_DIR@', str(tmp)))
    hook.chmod(0o755)
    if with_main:
        seed = tmp / 'seed'
        git('init', '-q', '-b', 'main', str(seed), env=env)
        (seed / 'README').write_text('probe\n')
        git('add', 'README', cwd=seed, env=env)
        git('commit', '-q', '-m', 'seed', cwd=seed, env=env)
        git('push', '-q', env['REMOTE'], 'main', cwd=seed, env=env)
    (tmp / 'gh').write_text(FAKE_GH)
    (tmp / 'gh').chmod(0o755)
    return env


def branch(env):
    return git('--git-dir', env['FAKE_BARE'], 'branch', '--list', 'effects-census', env=env)


def gh_log(tmp):
    p = Path(tmp, 'gh.log')
    return p.read_text().splitlines() if p.exists() else []


def test_owner_commands_fail_fast_and_undo_exactly(ctx):
    blocks = owner_blocks(ctx.owner_ask)
    for name, script in blocks.items():
        assert script.lstrip().startswith('set -euo pipefail'), f'{name} does not fail fast'
    design = Path(ctx.owner_ask).resolve().parent
    manifest = re.findall(r'^([0-9a-f]{64})  (\S+)$', blocks['push'], re.M)
    pushed = sorted(re.findall(r'^\s*"(\S+)=(\S+)"\s*$', blocks['push'], re.M))
    assert manifest and len(manifest) == len(pushed), 'every pushed file is checked by hash'
    assert {p for _, p in manifest} == {src for src, _ in pushed}, 'the hash list and the file list differ'
    for name, script in blocks.items():
        assert not re.search(r'mktemp -d\s*\)', script), f'{name}: a bare mktemp -d ignores TMPDIR on macOS'
    cap = re.search(r'capped at\s+\*\*(\d+) minutes\*\*', Path(ctx.owner_ask).read_text(encoding='utf-8'))
    walls = re.findall(r'^\s*timeout-minutes:\s*(\d+)\s*$', workflow_text(ctx), re.M)
    assert cap and walls == [cap.group(1)], ('the page must state the enforced cap', cap and cap.group(1), walls)
    for name, script in blocks.items():
        assert '"$GH" run list' not in script, f'{name}: `gh run list --workflow` resolves the file on the default branch (run 1)'
    world = lambda: tempfile.TemporaryDirectory(dir=ctx.tmp)
    # 1. The happy path: pushed, its run recorded, then undone exactly. As on the probe, the workflow is on
    #    effects-census only, and the commit also has another workflow's run: run 1's lookup fails here (404).
    with world() as tmp:
        env = make_world(tmp) | {'SRC': str(design)}
        r = run_bash(blocks['push'], env, tmp)
        assert r.returncode == 0, r.stderr[-800:]
        sha = git('--git-dir', env['FAKE_BARE'], 'rev-parse', 'refs/heads/effects-census', env=env)
        record = Path(env['RECORD']).read_text()
        assert f'commit {sha}' in record and 'run 4242' in record, record
        files = git('--git-dir', env['FAKE_BARE'], 'ls-tree', '-r', '--name-only', sha, env=env).split()
        assert sorted(files) == sorted(dest for _, dest in pushed), files
        r = run_bash(blocks['undo'], env, tmp)
        assert r.returncode == 0, r.stderr[-800:]
        assert branch(env) == '' and gh_log(tmp) == ['run delete 4242'], gh_log(tmp)
    # 2. No main: stops before any push.
    with world() as tmp:
        env = make_world(tmp, with_main=False) | {'SRC': str(design)}
        assert run_bash(blocks['push'], env, tmp).returncode != 0
        assert git('--git-dir', env['FAKE_BARE'], 'branch', '--list', env=env) == ''
    # 3. One byte changed in one file: stops before any push.
    with world() as tmp:
        env = make_world(tmp)
        altered = Path(tmp) / 'src'
        subprocess.run(['cp', '-R', str(design), str(altered)], check=True)
        victim = altered / pushed[-1][0]
        victim.write_bytes(victim.read_bytes() + b' ')
        assert run_bash(blocks['push'], env | {'SRC': str(altered)}, tmp).returncode != 0
        assert branch(env) == ''
    # 4. The branch moved after the push: undo deletes nothing.
    with world() as tmp:
        env = make_world(tmp) | {'SRC': str(design)}
        assert run_bash(blocks['push'], env, tmp).returncode == 0
        main = git('--git-dir', env['FAKE_BARE'], 'rev-parse', 'refs/heads/main', env=env)
        git('--git-dir', env['FAKE_BARE'], 'update-ref', 'refs/heads/effects-census', main, env=env)
        r = run_bash(blocks['undo'], env, tmp)
        assert r.returncode != 0 and 'branch_moved' in r.stderr and gh_log(tmp) == [], (r.stderr, gh_log(tmp))
    # 5. The recorded run belongs to another commit: undo deletes nothing.
    with world() as tmp:
        env = make_world(tmp) | {'SRC': str(design)}
        assert run_bash(blocks['push'], env, tmp).returncode == 0
        r = run_bash(blocks['undo'], env | {'FAKE_RUN_SHA': 'f' * 40}, tmp)
        assert r.returncode != 0 and 'run_of_other_commit' in r.stderr and gh_log(tmp) == [] and branch(env) != ''
    # 6. The branch moves between the check and the delete: the lease refuses the delete.
    with world() as tmp:
        env = make_world(tmp) | {'SRC': str(design)}
        assert run_bash(blocks['push'], env, tmp).returncode == 0
        assert run_bash(blocks['undo'], env | {'FAKE_MOVE_ON_DELETE': '1'}, tmp).returncode != 0
        assert branch(env) != '', 'the branch was deleted although it had moved'
    # 7. The run was still pending at the push: the undo finds it by commit, cancels it, waits,
    #    deletes it, and only then deletes the branch.
    with world() as tmp:
        env = make_world(tmp) | {'SRC': str(design)}
        r = run_bash(blocks['push'], env | {'FAKE_NO_RUN': '1'}, tmp)
        assert r.returncode != 0 and 'run pending' in Path(env['RECORD']).read_text(), r.stderr
        r = run_bash(blocks['undo'], env | {'FAKE_RUNNING': '1'}, tmp)
        assert r.returncode == 0, r.stderr[-800:]
        assert gh_log(tmp) == ['run cancel 4242', 'run delete 4242'] and branch(env) == '', gh_log(tmp)
    # 8. The run never stops: the undo stops with a named reason, deletes no run, leaves the branch.
    with world() as tmp:
        env = make_world(tmp) | {'SRC': str(design)}
        assert run_bash(blocks['push'], env, tmp).returncode == 0
        r = run_bash(blocks['undo'], env | {'FAKE_NEVER_STOPS': '1'}, tmp)
        assert r.returncode != 0 and 'run_did_not_stop' in r.stderr, r.stderr
        assert gh_log(tmp) == ['run cancel 4242'] and branch(env) != '', gh_log(tmp)
    # 9. The record cannot be written (its folder's parent is a file): stops before the push.
    with world() as tmp:
        env = make_world(tmp) | {'SRC': str(design)}
        Path(tmp, 'blocker').write_text('a file, not a folder\n')
        r = run_bash(blocks['push'], env | {'RECORD': str(Path(tmp, 'blocker', 'record.txt'))}, tmp)
        assert r.returncode != 0 and 'record_unwritable' in r.stderr, r.stderr
        assert branch(env) == '', 'pushed although the undo record could not be written'
    # 10. The push reaches the server, then the connection fails: the record already holds the commit
    #     and `run pending`, so the undo finds the branch and its run by commit.
    with world() as tmp:
        env = make_world(tmp) | {'SRC': str(design)}
        shim = Path(tmp, 'lossy')
        shim.mkdir()
        (shim / 'git').write_text(LOSSY_GIT)
        (shim / 'git').chmod(0o755)
        lossy = env | {'PATH': f'{shim}:{env["PATH"]}', 'REAL_GIT': shutil.which('git', path=os.environ['PATH'])}
        r = run_bash(blocks['push'], lossy, tmp)
        sha = git('--git-dir', env['FAKE_BARE'], 'rev-parse', 'refs/heads/effects-census', env=env)
        assert r.returncode != 0 and 'push_failed' in r.stderr, r.stderr
        assert Path(env['RECORD']).read_text() == f'commit {sha}\nrun pending\n', Path(env['RECORD']).read_text()
        r = run_bash(blocks['undo'], env, tmp)
        assert r.returncode == 0, r.stderr[-800:]
        assert branch(env) == '' and gh_log(tmp) == ['run delete 4242'], gh_log(tmp)
    # 11. Run 1 again: a completed (failed) run, its id written into the record by hand; the undo deletes
    #     that run and the branch, and a second push then goes through, with a new run.
    with world() as tmp:
        env = make_world(tmp) | {'SRC': str(design)}
        assert run_bash(blocks['push'], env | {'FAKE_NO_RUN': '1'}, tmp).returncode != 0
        first = git('--git-dir', env['FAKE_BARE'], 'rev-parse', 'refs/heads/effects-census', env=env)
        Path(env['RECORD']).write_text(f'commit {first}\nrun 4242\n')
        r = run_bash(blocks['push'], env, tmp)
        assert r.returncode != 0 and 'effects-census already exists' in r.stderr, 'the push must wait for the undo'
        r = run_bash(blocks['undo'], env, tmp)
        assert r.returncode == 0 and branch(env) == '' and gh_log(tmp) == ['run delete 4242'], (r.stderr, gh_log(tmp))
        r = run_bash(blocks['push'], env, tmp)
        assert r.returncode == 0, r.stderr[-800:]
        second = git('--git-dir', env['FAKE_BARE'], 'rev-parse', 'refs/heads/effects-census', env=env)
        assert Path(env['RECORD']).read_text() == f'commit {second}\nrun 4243\n', Path(env['RECORD']).read_text()
    # 12. Run 2's undo: the run is deleted, then GitHub answers the branch deletion with HTTP 500. The same
    #     undo, run again, finds the run gone (404), counts it done, and deletes the branch with its lease;
    #     the same with a pending record, whose run the first undo wrote into the record before deleting it.
    for pending in (False, True):
        with world() as tmp:
            env = make_world(tmp) | {'SRC': str(design)}
            assert (run_bash(blocks['push'], env | {'FAKE_NO_RUN': '1'} if pending else env, tmp).returncode != 0) == pending
            flaky = Path(tmp, 'flaky')
            flaky.mkdir()
            (flaky / 'git').write_text(FLAKY_GIT)
            (flaky / 'git').chmod(0o755)
            real = shutil.which('git', path=os.environ['PATH'])
            r = run_bash(blocks['undo'], env | {'PATH': f'{flaky}:{env["PATH"]}', 'REAL_GIT': real}, tmp)
            assert r.returncode != 0 and 'HTTP 500' in r.stderr and branch(env) != '', (pending, r.stderr)
            assert gh_log(tmp) == ['run delete 4242'] and 'run 4242' in Path(env['RECORD']).read_text(), gh_log(tmp)
            r = run_bash(blocks['undo'], env, tmp)
            assert r.returncode == 0 and 'already gone' in r.stdout, (pending, r.stderr)
            assert branch(env) == '' and gh_log(tmp) == ['run delete 4242'], (pending, gh_log(tmp))
            r = run_bash(blocks['undo'], env, tmp)
            assert r.returncode == 0, ('a third undo, with nothing left, is done', r.stderr)


# ---------------------------------------------------------------------------------------------
# The validator's refusals, on the fixture. Runs on both hosts.
# ---------------------------------------------------------------------------------------------

def test_validator_refusals(ctx):
    doc = fixture()
    assert acceptance_problems(doc, EDITION_COMMIT) == [], acceptance_problems(doc, EDITION_COMMIT)
    bad = copy.deepcopy(doc)
    bad['edition_commit'] = '0' * 40
    assert any(p.startswith('edition_commit_mismatch') for p in acceptance_problems(bad, EDITION_COMMIT))
    for reason in ('unknown_extension: Lean.Elab.Command.assertExistsExt in Elements.BookI.Prop04 (1 entries)',
                   'unknown_extension: Lean.Meta.Ext.extExtension in Elements.BookI.Prop04 (2 entries, scoped)',
                   'not_own: Lean.declRangeExt in Elements.BookI.Prop04 names Nat.add',
                   'unknown_payload: Lean.Meta.simpExtension in Elements.BookI.Prop04 names x: the origin is a '
                   'local hypothesis (Origin.fvar), which an exported entry never has'):
        bad = copy.deepcopy(doc)
        bad['verdict'], bad['reasons'] = 'incomplete', [reason]
        problems = acceptance_problems(bad, EDITION_COMMIT)
        assert any(p.startswith('census_incomplete') and reason in p for p in problems), (reason, problems)
    bad = copy.deepcopy(doc)
    bad['reasons'] = ['unknown_extension: x']
    assert any(p.startswith('verdict_inconsistent') for p in acceptance_problems(bad, EDITION_COMMIT))
    bad = copy.deepcopy(doc)
    bad['not_claimed'] = []
    assert any(p.startswith('claim_inconsistent') for p in acceptance_problems(bad, EDITION_COMMIT))
    for broken in ([], {'schema': SCHEMA}, dict(doc, effects='none'), dict(doc, effects=[1])):
        problems = acceptance_problems(copy.deepcopy(broken), EDITION_COMMIT)
        assert problems and all(p.startswith('schema') for p in problems), problems
    listed = {(r['module'], r['target']) for r in env_list(doc)}
    assert ('Elements.BookI.Prop99', 'Elements.BookI.Prop99.instShapeNat') in listed
    assert ('Elements.BookI.Prop99', 'Elements.BookI.Prop99.instSymbolsPt') not in listed
    bad = copy.deepcopy(doc)
    next(r for r in bad['effects'] if r['target'] == 'Elements.BookI.Prop99.instSymbolsPt')['own_keyed'] = False
    assert any(p.startswith('escapes_inconsistent') for p in acceptance_problems(bad, EDITION_COMMIT))
    bad = copy.deepcopy(doc)
    bad['effects'][0]['scope'] = 'local'
    assert any(p.startswith('local_in_olean') for p in acceptance_problems(bad, EDITION_COMMIT))
    # Payloads: each field of the entry, and every key in full (round 4).
    for family, field in (('instance', 'synth_order'), ('simp', 'backward_rfl'), ('simp', 'origin'),
                          ('class', 'out_level_params'), ('attribute', 'value')):
        bad = copy.deepcopy(doc)
        del next(r for r in bad['effects'] if r['family'] == family)['payload'][field]
        problems = acceptance_problems(bad, EDITION_COMMIT)
        assert any(p.startswith('payload_incomplete') and p.endswith(' lacks ' + field) for p in problems), \
            (family, field, problems)
    for keys in (['Elements.BookI.Prop99.tagOf'], [{'key': 'lit'}], [{'key': 'const', 'name': 'Nat'}],
                 [{'key': 'proj', 'struct': 'Prod', 'arity': 0}]):
        bad = copy.deepcopy(doc)
        next(r for r in bad['effects'] if r['family'] == 'simp')['payload']['keys'] = keys
        problems = acceptance_problems(bad, EDITION_COMMIT)
        assert any(p.startswith('payload_incomplete') and ' keys[0] is ' in p for p in problems), (keys, problems)
    bad = copy.deepcopy(doc)
    next(r for r in bad['effects'] if r['family'] == 'simp')['payload']['origin'] = {'kind': 'fvar'}
    assert any(p.endswith('origin is not a decoded origin') for p in acceptance_problems(bad, EDITION_COMMIT))
    # grind (run 2): each field of an E-matching theorem, and every symbol in full.
    for field in ('kind', 'patterns', 'cnstrs', 'min_indexable'):
        bad = copy.deepcopy(doc)
        del next(r for r in bad['effects'] if r['family'] == 'grind')['payload'][field]
        assert any(p.endswith(' lacks ' + field) for p in acceptance_problems(bad, EDITION_COMMIT)), field
    bad = copy.deepcopy(doc)
    next(r for r in bad['effects'] if r['family'] == 'grind')['payload']['symbols'] = ['SizeOf.sizeOf']
    assert any(p.endswith('symbols[0] is not a full symbol') for p in acceptance_problems(bad, EDITION_COMMIT))
    # The registry (run 2): every registered extension with its status; the gap is its "neither" entries.
    bad = copy.deepcopy(doc)
    bad['registry_gap'] = []
    assert any(p.startswith('registry_inconsistent') for p in acceptance_problems(bad, EDITION_COMMIT))
    bad = copy.deepcopy(doc)
    bad['registry'][0]['status'] = 'skipped'
    assert any(p.startswith('registry_inconsistent') for p in acceptance_problems(bad, EDITION_COMMIT))
    report = gap_report([HERE / 'fixtures' / 'minimal-effects.json', Path(ctx.tmp) / 'absent.json'])
    assert any('neither: Lean.Meta.Ext.extExtension' in l for l in report) and any('not read' in l for l in report), report
    missing = Missing('out/effects.json')
    assert any('out/effects.json was not written' in p for p in _problems_of(missing)), 'a missing output must name itself'


# ---------------------------------------------------------------------------------------------
# GitHub: the planted self-test (Planted.Base stands in for the foundations).
# ---------------------------------------------------------------------------------------------

BOOK = 'Planted.Book'
# Run 2's six populated extensions that the round-4 list missed, and how the census now treats each.
RUN2_EXTENSIONS = {
    '_private.Lean.DocString.Extension.0.Lean.moduleDocExt': 'reviewed',
    '_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt': 'reviewed',
    '_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTrivialStructureInfoExt': 'reviewed',
    'Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt': 'reviewed',
    'Lean.deprecatedModuleExt': 'reviewed',
    'Lean.Meta.Grind.grindExt': 'decoded',
}
PAYLOAD = 'Planted.Payload'
NAMING = {'origin', 'proof', 'decl'}   # payload fields that name the entry's own declaration


def payload_difference(a, b):
    """The payload fields in which two records differ, beyond those that name their own declarations."""
    pa, pb = a['payload'], b['payload']
    return {k for k in set(pa) | set(pb) if k not in NAMING and pa.get(k) != pb.get(k)}


def test_planted_instances_in_every_scope(ctx):
    inst = by_target(recs(ctx.planted, BOOK, 'instance'))
    g = inst.get('Planted.Book.instShapeNat')
    assert g and g['scope'] == 'global' and g['escapes'] and g['outside_foundations'], g
    assert 'priority 900' in g['detail'], g['detail']
    s = inst.get('Planted.Book.instShapeString')
    assert s and s['scope'] == 'scoped' and s['namespace'] == BOOK and s['escapes'], s
    assert 'Planted.Book.instShapeBool' not in inst, 'a local instance reached the olean'


def test_planted_simp_in_every_scope(ctx):
    simp = by_target(recs(ctx.planted, BOOK, 'simp'))
    g = simp.get('Planted.Book.area_mk')
    assert g and g['scope'] == 'global' and g['escapes'] and 'Planted.area' in g['keyed_on'], g
    assert 'priority 1000, post true, inv false' in g['detail'], g['detail']
    s = simp.get("Planted.Book.area_mk'")
    assert s and s['scope'] == 'scoped' and s['namespace'] == BOOK, s
    assert not {'Nat.add_zero', 'Nat.zero_add'} & set(simp), 'a local simp attribute reached the olean'
    # Payloads one field apart (Planted.Payload): only backwardRfl, then only a literal key.
    pay = by_target(recs(ctx.planted, PAYLOAD, 'simp'))
    bw, plain = pay.get(PAYLOAD + '.perimeter_bw'), pay.get(PAYLOAD + '.perimeter_plain')
    assert bw and plain and bw['payload']['backward_rfl'] is True and plain['payload']['backward_rfl'] is False, (bw, plain)
    assert payload_difference(bw, plain) == {'backward_rfl'}, payload_difference(bw, plain)
    two, three = pay.get(PAYLOAD + '.tagOf_two'), pay.get(PAYLOAD + '.tagOf_three')
    assert two and three and two['keyed_on'] == three['keyed_on'], ('names alone cannot tell them apart', two, three)
    assert {'key': 'lit', 'nat': 2} in two['payload']['keys'] and {'key': 'lit', 'nat': 3} in three['payload']['keys'], \
        (two, three)
    assert payload_difference(two, three) == {'keys'}, payload_difference(two, three)
    # grind's theorem sets (run 2). Every structure and inductive adds one `@[grind =]` sizeOf_spec per
    # constructor (Meta/SizeOf.lean:470-473): own-keyed. Payload's grind theorems escape, global and scoped;
    # its two inductives differ only in `cases` versus `cases eager`.
    for module, ctors in (('Planted.Base', ('Planted.Tri.mk', 'Planted.Tag.mk')),
                          ('Planted.Plain', ('Planted.Plain.Pt.a', 'Planted.Plain.Pt.b'))):
        grind = by_target(recs(ctx.planted, module, 'grind'))
        for ctor in ctors:
            g = grind.get(ctor + '.sizeOf_spec')
            assert g and g['own_keyed'] and not g['escapes'] and g['payload']['entry'] == 'ematch', (ctor, g)
    grind = by_target(recs(ctx.planted, PAYLOAD, 'grind'))
    g = grind.get(PAYLOAD + '.perimeter_grind')
    assert g and g['scope'] == 'global' and g['escapes'] and 'Planted.perimeter' in g['keyed_on'], g
    g = grind.get(PAYLOAD + ".perimeter_grind'")
    assert g and g['scope'] == 'scoped' and g['namespace'] == PAYLOAD, g
    lazy, eager = grind.get(PAYLOAD + '.Lazy'), grind.get(PAYLOAD + '.Eager')
    assert lazy and eager and lazy['payload']['eager'] is False and eager['payload']['eager'] is True, (lazy, eager)
    assert payload_difference(lazy, eager) == {'eager'}, payload_difference(lazy, eager)


def test_planted_reducibility_in_every_scope(ctx):
    red = recs(ctx.planted, BOOK, 'reducibility')
    g = [r for r in red if r['target'] == 'Planted.area']
    assert len(g) == 1 and g[0]['scope'] == 'global' and g[0]['detail'] == 'irreducible' and g[0]['escapes'], g
    s = [r for r in red if r['target'] == 'Planted.perimeter']
    assert len(s) == 1 and s[0]['scope'] == 'scoped' and s[0]['namespace'] == BOOK, s
    assert not [r for r in red if r['target'] == 'Planted.volume'], 'a local setting reached the olean'
    own = [r for r in recs(ctx.planted, 'Planted.Plain', 'reducibility') if r['target'] == 'Planted.Plain.Four']
    assert own and own[0]['detail'] == 'reducible' and own[0]['own_keyed'] and not own[0]['escapes'], own


def test_planted_notation_and_macros(ctx):
    notation = recs(ctx.planted, BOOK, 'notation')
    tokens = {r['detail'] for r in notation if r['detail'].startswith('token ')}
    assert 'token plantedG' in tokens, tokens
    # A tactic's leading identifier is not a token (its category reads identifiers as symbols), so the
    # global tactic macro shows as its parser in category tactic, not as a token (run 2).
    assert any(r['target'] == 'Planted.Book.tacticPlanted_g' and r['detail'].startswith('parser in category tactic')
               and r['scope'] == 'global' and r['escapes'] for r in notation), 'the tactic macro planted_g'
    # Exact tokens: `planted_local_simp`, a global command keyword, contains `planted_l` (run 2).
    assert not {'token plantedL', 'token planted_l'} & tokens, 'a local token reached the olean'
    parsers = [r for r in notation if r['detail'].startswith('parser in category')]
    assert any(r['scope'] == 'global' and r['escapes'] for r in parsers), parsers
    assert any(r['scope'] == 'scoped' and r['namespace'] == BOOK for r in parsers), parsers
    keyed = recs(ctx.planted, BOOK, 'macro')
    assert any(r['scope'] == 'global' and r['escapes'] and not any(k.startswith('Planted') for k in r['keyed_on'])
               for r in keyed), 'the macro rule on `trivial` is not listed as escaping'
    assert any(r['own_keyed'] for r in keyed) and any(r['scope'] == 'scoped' for r in keyed)


def test_planted_coercions_classes_and_attributes(ctx):
    inst = by_target(recs(ctx.planted, BOOK, 'instance'))
    c = inst.get('Planted.Book.instCoeNatTri')
    assert c and c['coercion'] and c['escapes'] and c['scope'] == 'global', c
    sc = inst.get('Planted.Book.instCoeStringTri')
    assert sc and sc['coercion'] and sc['scope'] == 'scoped' and sc['namespace'] == BOOK, sc
    assert 'Planted.Book.instCoeBoolTri' not in inst
    f = by_target(recs(ctx.planted, BOOK, 'coercion')).get('Planted.Book.toTri')
    assert f and f['own_keyed'] and not f['escapes'] and f['detail'].startswith('@[coe] coe'), f
    classes = by_target(recs(ctx.planted, BOOK, 'class'))
    foreign = classes.get('Planted.Tag')
    assert foreign and not foreign['own_keyed'] and foreign['escapes'], ('attribute [class] on Base\'s Tag', foreign)
    own = classes.get('Planted.Book.OwnShape')
    assert own and own['own_keyed'] and not own['escapes'] and own['payload']['out_level_params'] == [], own
    measure = by_target(recs(ctx.planted, PAYLOAD, 'class')).get(PAYLOAD + '.Measure')
    assert measure and measure['payload']['out_params'] == [1] and len(measure['payload']['out_level_params']) == 1, \
        measure
    csimp = recs(ctx.planted, BOOK, 'csimp')
    assert len(csimp) == 1 and csimp[0]['target'] == 'Planted.Book.dbl_eq' and csimp[0]['own_keyed'], csimp
    dep = [r for r in recs(ctx.planted, 'Planted.Plain', 'attribute')
           if r['target'] == 'Planted.Plain.oldTwo' and r['extension'] == 'Lean.Linter.deprecatedAttr']
    assert dep and dep[0]['own_keyed'] and 'deprecated' in dep[0]['detail'], dep
    assert dep[0]['payload']['value']['new_name'] == 'Planted.Plain.two', dep
    # Two definitions one field apart: only their @[implemented_by] target (Planted.Payload).
    impl = by_target([r for r in recs(ctx.planted, PAYLOAD, 'attribute')
                      if r['extension'] == 'Lean.Compiler.implementedByAttr'])
    a, b = impl.get(PAYLOAD + '.viaA'), impl.get(PAYLOAD + '.viaB')
    assert a and b and a['payload']['value'] == PAYLOAD + '.implA' and b['payload']['value'] == PAYLOAD + '.implB', (a, b)
    assert payload_difference(a, b) == {'value'}, payload_difference(a, b)


def test_planted_flags_and_reviewed(ctx):
    doc = ctx.planted
    assert acceptance_problems(doc, None) == [], acceptance_problems(doc, None)
    base = by_target(recs(doc, 'Planted.Base'))
    for target in ('Planted.instShapeTri', 'Planted.area_def', 'Planted.Scope.instShapeUnit'):
        r = base.get(target)
        assert r and r['part'] == 'foundations' and not r['outside_foundations'], (target, r)
    assert not [r for r in recs(doc, 'Planted.Plain') if r['escapes']], 'the plain module escapes'
    inst = recs(doc, 'Planted.Plain', 'instance')
    # Each inductive also gets a SizeOf instance, Pt._sizeOf_inst (run 2): count by name, not by number.
    assert {'Planted.Plain.instShapePt', 'Planted.Plain.instDecidableEqPt'} <= {r['target'] for r in inst} \
        and all(r['own_keyed'] for r in inst), inst
    assert doc['bookkeeping'] and all(b['reason'] for b in doc['bookkeeping']), 'bookkeeping without its reason'
    assert 'Lean.classExtension' not in {r['extension'] for r in doc['reviewed']}, 'classes must be decoded'
    status = {e['extension']: e['status'] for e in doc['registry']}
    for name, want in RUN2_EXTENSIONS.items():
        assert status.get(name) == want, (name, status.get(name))
    assert doc['reviewed_unregistered'] == [], ('reviewed names no registered extension has', doc['reviewed_unregistered'])


def test_census_failure_paths(ctx):
    expect = {'unknown': ('unknown_extension:', 'assertExists'), 'unknown-scoped': ('unknown_extension:', 'scoped')}
    for case, (reason, word) in expect.items():
        text = Path(ctx.out, f'fail-{case}.txt').read_text(encoding='utf-8')
        assert text.rstrip().splitlines()[-1] == 'exit 1', (case, text[-400:])
        hits = [l for l in text.splitlines() if reason in l]
        assert hits and any(word in l for l in hits), (case, text[-800:])
        doc = load(Path(ctx.out, f'fail-{case}.json'))
        assert doc['verdict'] == 'incomplete' and any(reason in r for r in doc['reasons']), (case, doc['reasons'][:5])


# ---------------------------------------------------------------------------------------------
# GitHub: the edition census.
# ---------------------------------------------------------------------------------------------

def test_edition_walks_every_module(ctx):
    doc = ctx.edition
    head = subprocess.run(['git', '-C', ctx.edition_dir, 'rev-parse', 'HEAD'], check=True,
                          capture_output=True, text=True).stdout.strip()
    assert head == ctx.commit == doc['edition_commit'] == EDITION_COMMIT, (head, doc['edition_commit'])
    files = subprocess.run(['git', '-C', ctx.edition_dir, 'ls-files', 'Elements.lean', 'Elements/'],
                           check=True, capture_output=True, text=True).stdout.split()
    expected = {f[:-5].replace('/', '.') for f in files if f.endswith('.lean')}
    parts = {m['name']: m['part'] for m in doc['modules']}
    package = {n for n, p in parts.items() if p != 'toolchain'}
    assert package == expected, sorted(package ^ expected)[:10]
    assert sum(p == 'toolchain' for p in parts.values()) > 0, 'the toolchain modules were not walked'
    for name in package:
        want = 'foundations' if name.startswith(('Elements.Foundations.', 'Elements.Figure.')) else 'edition'
        assert parts[name] == want, (name, parts[name])


def test_edition_known_effects(ctx):
    doc = ctx.edition
    assert doc['verdict'] == 'complete', doc['reasons'][:10]
    for module in ('Elements.BookI.Prop04', 'Elements.BookI.Prop08'):
        inst = recs(doc, module, 'instance')
        assert len(inst) >= 4 and all(r['own_keyed'] and not r['escapes'] for r in inst), (module, inst)
        assert sum('Symbols' in ' '.join(r['keyed_on']) for r in inst) == 2, (module, inst)
        assert sum('DecidableEq' in (r['target'] or '') for r in inst) == 2, (module, inst)
    assert not [r for r in recs(doc, 'Elements.Figure.AreaRules', 'instance')
                if {'Std.Associative', 'Std.Commutative'} & set(r['keyed_on'])], 'a local instance reached the olean'
    deprecated = sorted(r['module'] for r in recs(doc, family='attribute')
                        if 'deprecated' in r['detail'] and r['outside_foundations'])
    assert deprecated == ['Elements.BookI.Prop24'] + ['Elements.Deprecated'] * 3, deprecated
    abbrevs = [r for r in recs(doc, family='reducibility')
               if r['outside_foundations'] and r['detail'] == 'reducible' and r['own_keyed']]
    assert len(abbrevs) >= 22, len(abbrevs)
    assert not [r for r in recs(doc, family='class') if r['outside_foundations']], 'a class outside the foundations'


def test_census_json_schema(ctx):
    for name, doc, commit in (('planted', ctx.planted, None), ('edition', ctx.edition, ctx.commit)):
        problems = acceptance_problems(doc, commit)
        assert not problems, (name, problems[:10])
        assert doc['lean_version'].startswith('4.35.0'), (name, doc['lean_version'])


STATIC = [test_workflow_pins_every_action_by_commit, test_workflow_reads_only_and_verifies_lean, test_validator_refusals,
          test_census_keeps_every_field]
MAC = STATIC[:2] + [test_owner_commands_fail_fast_and_undo_exactly] + STATIC[2:]
GITHUB = STATIC + [test_planted_instances_in_every_scope, test_planted_simp_in_every_scope,
                   test_planted_reducibility_in_every_scope, test_planted_notation_and_macros,
                   test_planted_coercions_classes_and_attributes, test_planted_flags_and_reviewed,
                   test_census_failure_paths, test_edition_walks_every_module, test_edition_known_effects,
                   test_census_json_schema]


def main(argv):
    parser = argparse.ArgumentParser(description='Acceptance tests of the exported-effects census.')
    parser.add_argument('--host', choices=('mac', 'github', 'gap'), required=True)
    parser.add_argument('--root', default=str(HERE.parent))
    parser.add_argument('--owner-ask')
    parser.add_argument('--tmp', help='the writable folder for every scratch folder of the owner-command simulation '
                        '(default: TMPDIR)')
    parser.add_argument('--planted')
    parser.add_argument('--edition')
    parser.add_argument('--edition-dir')
    parser.add_argument('--commit')
    parser.add_argument('--out')
    ctx = parser.parse_args(argv)
    # Every scratch folder goes under --tmp, else TMPDIR, exactly, never a silent fallback elsewhere.
    ctx.tmp = os.path.abspath(ctx.tmp or os.environ.get('TMPDIR') or tempfile.gettempdir())
    if ctx.host == 'gap':
        if not (ctx.planted and ctx.edition):
            parser.error('--host gap needs --planted and --edition')
        print('\n'.join(gap_report([ctx.planted, ctx.edition])))
        return 0
    if ctx.host == 'mac' and not ctx.owner_ask:
        parser.error('--host mac needs --owner-ask')
    if ctx.host == 'github':
        if not (ctx.planted and ctx.edition and ctx.edition_dir and ctx.commit and ctx.out):
            parser.error('--host github needs --planted, --edition, --edition-dir, --commit and --out')
        ctx.planted, ctx.edition = load_or_missing(ctx.planted), load_or_missing(ctx.edition)
    tests = MAC if ctx.host == 'mac' else GITHUB
    failed = 0
    for test in tests:
        try:
            test(ctx)
            print(f'PASS {test.__name__}')
        except Exception as exc:  # a failed assertion or a malformed document both fail the test
            failed += 1
            print(f'FAIL {test.__name__}: {type(exc).__name__}: {str(exc)[:600]}')
    print(f'{len(tests) - failed} passed, {failed} failed')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
