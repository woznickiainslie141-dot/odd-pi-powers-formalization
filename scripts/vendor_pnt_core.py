"""Reproduce the small, proof-bearing PNT closure from the pinned local source.

No network, compiler, mathematical replacement, or dependency update is used.
Blueprint metadata is omitted; the unused unfinished decay branch is omitted.
"""
from pathlib import Path
import hashlib
import json
import re
import shutil

ROOT = Path(__file__).resolve().parent.parent
PROJECT = ROOT / 'formalization' / 'OddPiPowers'
SOURCE = PROJECT / '.lake/packages/PrimeNumberTheoremAnd'
DEST = PROJECT / 'OddPiPowers/Vendor/PNT'
REV = '127b50e33f6033e2147921167a117af96d9ba4ea'


def omit_blueprints(text):
    # Balance brackets while ignoring strings and nested Lean block comments.
    while (start := text.find('@[blueprint')) >= 0:
        i, depth, comment, string = start + 1, 0, 0, False
        while i < len(text):
            if comment:
                if text.startswith('/-', i):
                    comment += 1; i += 2; continue
                if text.startswith('-/', i):
                    comment -= 1; i += 2; continue
            elif string:
                if text[i] == '\\':
                    i += 2; continue
                if text[i] == '"':
                    string = False
            elif text.startswith('/-', i):
                comment = 1; i += 2; continue
            elif text[i] == '"':
                string = True
            elif text[i] == '[':
                depth += 1
            elif text[i] == ']':
                depth -= 1
                if depth == 0:
                    text = text[:start] + text[i + 1:]
                    break
            i += 1
        else:
            raise ValueError('Unclosed blueprint attribute')
    # Keep these prose blocks as ordinary comments.
    return text.replace('blueprint_comment /--', '/-')


def as_lean_module(text):
    """Export the upstream declarations through Lean 4.35's module format."""
    matches = list(re.finditer(r'^import [^\n]+\n', text, re.M))
    if not matches:
        raise ValueError('Expected an import block')
    end = matches[-1].end()
    text = text[:end] + '\n@[expose] public section\n' + text[end:]
    text = re.sub(r'^import ', 'public import ', text, flags=re.M)
    return 'module\n\n' + text


def main():
    DEST.mkdir(parents=True, exist_ok=True)
    files = ['Sobolev', 'Fourier', 'SmoothExistence',
             'Mathlib/Algebra/Notation/Support',
             'Mathlib/Analysis/Asymptotics/Asymptotics',
             'Mathlib/Analysis/SpecialFunctions/Log/Basic',
             'Wiener', 'Consequences']
    records = []
    for name in files:
        source = SOURCE / 'PrimeNumberTheoremAnd' / (name + '.lean')
        raw = source.read_text(encoding='utf-8')
        text = raw
        changes = ['remove documentation-only Architect blueprint metadata',
                   'redirect local imports to OddPiPowers.Vendor.PNT']
        if name == 'Wiener':
            text = text[:text.index('-- #print axioms WeakPNT')]
            lo = text.index('@[blueprint "prelim-decay-2"')
            hi = text.index('lemma decay_bounds_key', lo)
            text = text[:lo] + text[hi:]
            changes += ['retain prefix through WeakPNT',
                        'omit unused prelim_decay_2, AbsolutelyContinuous, '
                        'prelim_decay_3 and decay_alt declarations']
        if name == 'Consequences':
            text = text[:text.index('theorem chebyshev_asymptotic_finsum')]
            # Its attribute belongs to the omitted theorem.
            # At this revision the preceding theorem has no subsequent attribute.
            text = text.replace('import PrimeNumberTheoremAnd.Defs\n', '')
            changes += ['retain prefix through chebyshev_asymptotic',
                        'omit unused Defs import']
        text = omit_blueprints(text)
        text = text.replace('import Architect\n', '')
        # Mathlib already supplies its standard lemma command. The Batteries
        # alternative was an Architect dependency, not mathematical content.
        text = text.replace('import Batteries.Tactic.Lemma\n', '')
        text = text.replace('set_option lang.lemmaCmd true\n', '')
        text = text.replace('PrimeNumberTheoremAnd.', 'OddPiPowers.Vendor.PNT.')
        # The old upstream format could see private transitive imports.
        # The module format requires these used declarations explicitly.
        extra_imports = {
            'Mathlib/Analysis/Asymptotics/Asymptotics': [
                'Mathlib.Analysis.Normed.Group.Bounded',
                'Mathlib.Order.Filter.AtTopBot.Archimedean'],
            'Mathlib/Analysis/SpecialFunctions/Log/Basic': [
                'Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics'],
        }.get(name, [])
        if extra_imports:
            text = ''.join(f'import {m}\n' for m in extra_imports) + text
            changes += ['make used Mathlib imports explicit for module visibility']
        if re.search(r'\b(sorry|admit|axiom)\b', text):
            raise ValueError(f'Unfinished or axiom declaration in {name}')
        header = ('/-\nAdapted from PrimeNumberTheoremAnd, Apache-2.0.\n'
                  f'Pinned upstream commit: {REV}.\n'
                  f'Original file: PrimeNumberTheoremAnd/{name}.lean\n'
                  'See PROVENANCE.json and LICENSE in this directory.\n-/\n\n')
        if name == 'Wiener':
            cuts = ['lemma one_add_sq_pos', 'section nabla',
                    'lemma log_isbigo_log_div', 'theorem limiting_fourier_lim1 (',
                    'lemma smooth_urysohn (', 'theorem sum_le_integral',
                    'variable (f x) in', 'lemma fourier_surjection_on_schwartz',
                    'lemma interval_approx_inf', 'lemma le_floor_mul_iff']
            begin = text.index('noncomputable\ndef nterm')
            positions = [begin] + [text.index(c) for c in cuts] + [len(text)]
            assert positions == sorted(positions)
            # File-local opens/variables/instance scopes must be reproduced;
            # declarations and their proofs stay byte-for-byte unchanged.
            preamble = text[:begin]
            for i, (lo, hi) in enumerate(zip(positions, positions[1:])):
                prefix = preamble if i == 0 else (
                    f'import OddPiPowers.Vendor.PNT.Wiener{i-1:02}\n' +
                    preamble[preamble.index('set_option linter.style.header false'):])
                if i == 2:
                    prefix = 'import Mathlib.Analysis.Asymptotics.SpecificAsymptotics\n' + prefix
                if i >= 9:
                    prefix += '\nlocal instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩\n'
                split_target = DEST / f'Wiener{i:02}.lean'
                split_target.write_text(header + as_lean_module(prefix + text[lo:hi]), encoding='utf-8')
                records.append(dict(file=split_target.name, changes=changes +
                    ['split at complete declaration boundaries; repeat file-local context'],
                    source_sha256=hashlib.sha256(raw.encode()).hexdigest(),
                    adapted_sha256=hashlib.sha256(split_target.read_bytes()).hexdigest()))
            text = f'import OddPiPowers.Vendor.PNT.Wiener{len(positions)-2:02}\n'
            changes += ['aggregate the sequential memory-bounded proof modules']
        target = DEST / (name + '.lean')
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(header + as_lean_module(text), encoding='utf-8')
        records.append(dict(file=name + '.lean', changes=changes,
                            source_sha256=hashlib.sha256(raw.encode()).hexdigest(),
                            adapted_sha256=hashlib.sha256(target.read_bytes()).hexdigest()))
    shutil.copyfile(SOURCE / 'LICENSE', DEST / 'LICENSE')
    (DEST / 'PROVENANCE.json').write_text(json.dumps(dict(
        repository='https://github.com/AlexKontorovich/PrimeNumberTheoremAnd',
        revision=REV, license='Apache-2.0', files=records), indent=2), encoding='utf-8')
    print(f'Prepared {len(records)} vendored proof modules; no compiler invoked.')


if __name__ == '__main__':
    main()
