"""Write scripts/CheckAxioms.lean: `#print axioms` for every `problem1_iff*`, `problem1_of*`,
`problem2_iff*` and `problem2_of*` theorem of the library, Basic first, then the modules in
alphabetical order.

Run from the kit root: python3 equivalents/scripts/gen_check_axioms.py
"""
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
LIB = os.path.join(HERE, '..', 'Rule30Equivalents')
OUT = os.path.join(HERE, 'CheckAxioms.lean')

THEOREM = re.compile(r'^theorem (problem[12]_(?:iff|of)\w*)')
NAMESPACE = re.compile(r'^namespace (\S+)')
SECTION = re.compile(r'^section\b')
END = re.compile(r'^end(\s+\S+)?\s*$')


def names(path):
    stack, found = [], []
    with open(path, encoding='utf-8') as f:
        for line in f:
            m = NAMESPACE.match(line)
            if m:
                stack.append(m.group(1))
                continue
            if SECTION.match(line):
                stack.append('')
                continue
            if END.match(line) and stack:
                stack.pop()
                continue
            m = THEOREM.match(line)
            if m:
                found.append('.'.join([s for s in stack if s] + [m.group(1)]))
    return found


modules = sorted(f for f in os.listdir(LIB) if f.endswith('.lean'))
modules.remove('Basic.lean')
lines = []
for mod in ['Basic.lean'] + modules:
    lines += names(os.path.join(LIB, mod))

with open(OUT, 'w', encoding='utf-8') as f:
    f.write('import Rule30Equivalents\n\n')
    f.write('/-! Prints the axioms of every `problem1_iff_*`, `problem1_of_*`, `problem2_iff_*` and\n')
    f.write('`problem2_of_*` theorem in the library.\n')
    f.write('Run from the kit root: `lake env lean equivalents/scripts/CheckAxioms.lean`.\n')
    f.write('Regenerate with `python3 equivalents/scripts/gen_check_axioms.py`. -/\n\n')
    for n in lines:
        f.write(f'#print axioms {n}\n')
print(f'{len(lines)} theorems')
