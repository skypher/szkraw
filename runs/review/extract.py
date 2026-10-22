"""Extract Lean declarations (docstring + signature, proof elided) for review briefs."""
import re, sys
def extract(path, names, full_defs=()):
    lines = open(path).read().split('\n')
    out = []
    for name in names:
        pat = re.compile(r'^(theorem|def|noncomputable def|lemma|structure|abbrev)\s+' + re.escape(name) + r'\b')
        idx = next((i for i, l in enumerate(lines) if pat.match(l)), None)
        if idx is None:
            out.append(f'-- NOT FOUND: {name}'); continue
        # docstring above
        j = idx
        if j > 0 and lines[j-1].rstrip().endswith('-/'):
            j -= 1
            while not lines[j].lstrip().startswith('/--'):
                j -= 1
        k = idx
        block = []
        if name in full_defs:
            # whole definition until blank line
            while k < len(lines) and lines[k].strip() != '':
                block.append(lines[k]); k += 1
        else:
            while True:
                l = lines[k]
                m = re.search(r':=( by)?\s*$', l) or re.search(r':= by\b.*$', l)
                if m:
                    block.append(l[:m.start()] + ':= …'); break
                if re.search(r'\s:=\s', l) and not l.lstrip().startswith('--'):
                    block.append(l[:l.index(':=')] + ':= …'); break
                block.append(l); k += 1
        out.append('\n'.join(lines[j:idx] + block))
    return '\n\n'.join(out)
if __name__ == '__main__':
    pass
