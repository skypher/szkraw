"""Check the fixed cross-paper numbers in p1.tex, p2.tex, p3.tex against the companion papers' .aux files.

A reference to another paper is written \\xnum{P1-thm:lc}{3.1}: the prefix names the paper, the label is its label
there, and the number is printed as given, so each paper compiles alone. Run after building all three papers; exits
with status 1 if a number differs from the companion paper's current numbering or a label is missing.
Usage: check_xref.py [papers directory]"""
import os
import re
import sys

ROOT = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))


def aux_numbers(name):
    numbers = {}
    with open(os.path.join(ROOT, name + '.aux'), encoding='utf-8') as f:
        for line in f:
            m = re.match(r'\\newlabel\{([^}]*)\}\{\{([^}]*)\}', line)
            if m:
                numbers[m.group(1)] = m.group(2)
    return numbers


def main():
    cache, bad, total = {}, 0, 0
    for paper in ('p1', 'p2', 'p3'):
        with open(os.path.join(ROOT, paper + '.tex'), encoding='utf-8') as f:
            text = f.read()
        if re.search(r'\\ref\{P[123]-', text) or '\\externaldocument' in text:
            print(f'{paper}: cross-paper \\ref or \\externaldocument left; use \\xnum')
            bad += 1
        for m in re.finditer(r'\\xnum\{(P[123])-([^}]*)\}\{([^}]*)\}', text):
            other, label, fixed = 'p' + m.group(1)[1], m.group(2), m.group(3)
            total += 1
            if other not in cache:
                cache[other] = aux_numbers(other)
            actual = cache[other].get(label)
            if actual != fixed:
                print(f'{paper}: {m.group(1)}-{label} is {actual!r} in {other}, written {fixed!r}')
                bad += 1
    print(f'{total} cross-paper numbers checked, {bad} problems')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
