import csv
from itertools import permutations
import json
import os
import sys
import textdistance
from functools import reduce
from bin import list_routines_misc
from dreamcoder.grammar import Grammar
from dreamcoder.program import Program, Primitive
from dreamcoder.utilities import parseSExpression as parse

## features computed by checking if a concept relies on any of a set of primitives

def relies_on(expression, primitives):
    if type(expression) is str:
        return expression in primitives
    return reduce(lambda x, y: x or y, (relies_on(expr, primitives) for expr in expression))

grouped_features = {}
def grouped_feature_gen(prims):
    return lambda prog, *args: relies_on(prog, prims)
grouped_features.update((feature, grouped_feature_gen(prims)) for feature, prims in [
    ('indexing', [
        'first', 'nth', 'second', 'third', 'last', 'foldi', 'mapi', 'filteri',
        'insert', 'replace', 'cut_idx', 'swap', 'cut_slice', 'slice', 'drop',
        'take', 'droplast', 'takelast', 'splice', 'find'
    ]),
    ('indexing_not_first', [
        'nth', 'second', 'third', 'last', 'foldi', 'mapi', 'filteri', 'insert',
        'replace', 'cut_idx', 'swap', 'cut_slice', 'slice', 'drop', 'take',
        'droplast', 'takelast', 'splice', 'find'
    ]),
    ('uniqueness', ['unique', 'group']),
    ('unfolding', ['range', 'repeat']),
    ('counting', ['count', 'length', 'range', 'mapi']),
    ('higher', ['map', 'mapi', 'filter', 'filteri', 'fold', 'foldi', 'count', 'sort', 'find'])
])

# digit manipulation exception

arithmetic_digit_features = ['+', '*', '/', '%']
arithmetic_nondigit_features = ['-', '<', '>', 'is_even', 'is_odd', 'sum', 'product', 'range', 'max', 'min', 'sort']

def has_divmod_nondigit(expression):
    if expression[0] in ['/', '%']:
        return expression[2] != '10'
    return reduce(lambda x, y: x or y, (has_divmod_nondigit(expr) for expr in expression if type(expr) is list), False)

def arithmetic_nondigit(prog, _, __, unparsed, *args):
    if relies_on(prog, arithmetic_nondigit_features):
        return True
    if not relies_on(prog, arithmetic_digit_features):
        return False
    # else relies on digit features but not on digit features

    if relies_on(prog, ['+', '*']):
        # whether it still relies on + or * beyond the 'swap digits' paradigm
        return relies_on(parse(unparsed.replace('(+ (* (% $0 10) 10) (/ $0 10))', '0')), arithmetic_digit_features)
    else:
        # relies on / or %; whether there is a non-digit use of either
        return has_divmod_nondigit(prog)
grouped_features['arithmetic'] = arithmetic_nondigit


all_primitives = {}
def all_primitives_gen(prim):
    return lambda prog, *args: relies_on(prog, [prim])
all_primitives.update((prim, all_primitives_gen(prim)) for prim in [
    'true', 'false', 'not', 'if', 'and', 'or', '+', '-', '*',
    '/', '<', '>', '==', '%', 'is_even', 'is_odd', 'empty', 'cons',
    'singleton', 'fold', 'map', 'filter', 'zip', 'first', 'nth', 'second',
    'third', 'length', 'last', 'concat', 'append', 'count', 'cut_vals', 'is_in',
    'flatten', 'max', 'min', 'product', 'reverse', 'sum', 'unique', 'range',
    'repeat', 'foldi', 'mapi', 'filteri', 'insert', 'replace', 'cut_idx',
    'swap', 'cut_slice', 'slice', 'drop', 'take', 'droplast', 'takelast',
    'splice', 'find', 'cut_val', 'group', 'sort'
])



## features computed by recursively pattern-matching the concept against any of
## a list of patterns

def mark_top_argument(expression, level=0):
    for i in range(len(expression)):
        expr = expression[i]
        if type(expr) is str:
            if expr == '$' + str(level):
                expression[i] = '$l'
        elif type(expr) is list:
            if expr[0] == 'lambda':
                mark_top_argument(expr[1:], level + 1)
            else:
                mark_top_argument(expr, level)

def pattern_match(expression, pattern):
    if len(expression) != len(pattern):
        return False
    for i in range(len(pattern)):
        if type(pattern[i]) is list:
            if type(expression[i]) is list:
                if not pattern_match(expression[i], pattern[i]):
                    return False
            else:
                return False
        elif pattern[i] not in ['_', '$x'] and pattern[i] != expression[i]:
            return False
    return True

def find_marks(expression, pattern):
    if type(pattern) is str:
        if pattern == '$x':
            return [expression]
        else:
            return []
    return [expr for i in range(len(pattern)) for expr in find_marks(expression[i], pattern[i])]

def recursive_pattern_match(expression, patterns, base, top=True):
    if type(expression) is str:
        return base(expression)
    if top:
        mark_top_argument(expression)
        expression = expression[1] # [0] will always be 'lambda'
    for pattern in patterns:
        if pattern_match(expression, pattern):
            if reduce(lambda x, y: x or y,
                      (recursive_pattern_match(expr, patterns, base, top=False)
                       for expr in find_marks(expression, pattern)),
                      False):
                return True
            else:
                return False
    return False

recursive_features = {}
def recursive_features_gen(patterns, basefun, a=False):
    return lambda prog, *args: recursive_pattern_match(prog[:], [parse(p) for p in patterns], basefun)
recursive_features.update(
    (feature, recursive_features_gen(patterns, basefun)) for feature, patterns, basefun in [
        ('list_constants', [
            '(cons $x $x)',
            '(singleton $x)',
            '(concat $x $x)',
            '(append $x $x)',
            '(repeat $x _)',
            '(insert $x _ _)',
            '(replace _ $x _)',
            '(splice $x _ $x)',
            '(if _ $x $x)',
            '(filter _ $x)',
            '(filteri _ $x)'
        ], lambda e: e.isdigit()),

        ('filtering', [
            '(filter _ $x)',
            '(filteri _ $x)',
            '(cut_val _ $x)',
            '(cut_vals _ $x)',
            '(cut_idx _ $x)',
            '(cut_slice _ _ $x)',
            '(take _ $x)',
            '(drop _ $x)',
            '(takelast _ $x)',
            '(droplast _ $x)',
            '(slice _ _ $x)',
            '(map first (filter _ (zip $x _)))',
            '(fold (lambda (lambda (if _ (cons $0 $1) $1))) (take 1 _) (drop 1 $x))'
        ], lambda e: e == '$l'),

        ('mapping', [
            '(map _ $x)',
            '(mapi _ $x)',
            '(flatten $x)',
            '(map _ (zip (droplast 1 $x) (drop 1 $x)))',
            '(map _ (drop 1 $x))'
        ], lambda e: e == '$l')
    ])



## features computed in 'predict()' in bin/list_routines_misc.py

Primitive.GLOBALS.clear()
Grammar.uniform(list_routines_misc.primitives())
pre_features = {
    'program_length': lambda _, __, ___, p: Program.parse(p).size(),
    'depth': lambda _, __, ___, p: Program.parse(p).depth(),
    'apps': lambda _, __, ___, p: list_routines_misc.count_applications(Program.parse(p))
}


## miscellaneous features

misc_features = {}

concept_examples = {'model': {}, 'dataset': {}}
for purpose, num in [('model', 100), ('dataset', 150)]:
    concepts = os.listdir('analysis/concept_examples/{}'.format(purpose))
    for concept in map(lambda n: 'c{:03}'.format(n), range(1, num+1)):
        with open('analysis/concept_examples/{}/{}'.format(
                purpose,
                list(filter(lambda c: c.startswith(concept), concepts))[0]), 'r') as f:
            concept_examples[purpose][concept] = json.load(f)['examples']

bignums = set(range(10, 100))
bignumprims = list(map(str, range(10, 100)))
def relies_on_bignums(program, purpose, concept, *args):
    if relies_on(program, bignumprims):
        return True
    for example in concept_examples[purpose][concept]:
        for inout in example.values():
            if bignums & set(inout):
                return True
    return False
misc_features['numbers'] = relies_on_bignums


length_conditions = {
    'first': lambda *args: 1,
    'second': lambda *args: 2,
    'third': lambda *args: 3,
    'nth': lambda i, *args: int(i),
    'insert': lambda _, i, *args: int(i)-1,
    'splice': lambda _, i, *args: int(i)-1,
    'replace': lambda i, *args: int(i),
    'cut_idx': lambda i, *args: int(i),
    'swap': lambda i, j, *args: max(int(i), int(j)),
    'cut_slice': lambda _, j, *args: int(j),
    'slice': lambda _, j, *args: int(j),
    'drop': lambda i, *args: int(i),
    'take': lambda i, *args: int(i),
    'droplast': lambda i, *args: int(i),
    'takelast': lambda i, *args: int(i)
}
def relies_on_conditional(program, purpose, concept, *args):
    if relies_on(program, ['if', 'filter', 'filteri', 'group', 'count', '==',
                           '<', '>', 'is_even', 'is_odd', 'find']):
        return True
    if program[1][0] in length_conditions:
        for example in concept_examples[purpose][concept]:
            try:
                if len(example['i']) < length_conditions[program[1][0]](*program[1][1:]):
                    return True
            except (ValueError, TypeError):
                break
    return False
misc_features['conditional'] = relies_on_conditional


def indices_of_prim(expression, primitive):
    if type(expression) is str:
        return [()] if expression == primitive else []
    return [(i,) + inds for i in range(len(expression)) for inds in indices_of_prim(expression[i], primitive)]

def get_expr_at(expression, indices):
    for ind in indices:
        expression = expression[ind]
    return expression

def uses_recursion(prog, top=True, *args):
    if top: mark_top_argument(prog)
    if relies_on(prog, [
        'foldi', 'mapi', 'filteri', 'cut_vals', 'is_in',  'count', 'last',
        'fold', 'map', 'filter', 'zip', 'flatten', 'max', 'min', 'product',
        'reverse', 'sum', 'unique', 'group', 'sort', 'find', 'cut_val',
        'append', 'length', 'droplast', 'takelast'
    ]):
        return True
    for pattern in [parse(p) for p in [
        '(nth $x _)', '(repeat _ $x)', '(insert _ $x _)', '(replace $x _ _)',
        '(cut_idx $x _)', '(swap $x $x _)', '(cut_slice $x $x _)',
        '(slice $x $x _)', '(drop $x _)', '(take $x _)', '(splice $y $x _)',
        '(concat $y _)'
    ]]:
        for inds in indices_of_prim(prog, pattern[0]):
            for i in range(len(pattern)):
                arg = get_expr_at(prog, inds[:-1] + (i,))
                if pattern[i] == '$x':
                    if type(arg) is list:
                        if arg[0] == 'if':
                            if uses_recursion(arg, top=False):
                                return True
                        else:
                            return True
                    elif not arg.isdigit():
                        return True
                elif pattern[i] == '$y' and (arg == '$l' or uses_recursion(arg, top=False)):
                    return True
    return False

misc_features['recursive'] = lambda _, __, ___, unparsed, *args: \
    uses_recursion(parse(unparsed.replace('first', 'nth 1').replace('second', 'nth 2').replace('third', 'nth 3')))


misc_features['variables'] = lambda _, __, ___, p: p.count('$')
misc_features['lambdas'] = lambda _, __, ___, p: p.count('lambda') - 1

def output_1(program, purpose, concept, *args):
    return all(len(datum['o']) == 1
               for datum in concept_examples[purpose][concept])

def output_LT(program, purpose, concept, *args):
    return all(len(datum['o']) < len(datum['i'])
               for datum in concept_examples[purpose][concept])

def output_EQ(program, purpose, concept, *args):
    return all(len(datum['o']) == len(datum['i'])
               for datum in concept_examples[purpose][concept])

def output_GT(program, purpose, concept, *args):
    return all(len(datum['o']) > len(datum['i'])
               for datum in concept_examples[purpose][concept])

def elements_disjoint(program, purpose, concept, *args):
    return all(set(datum['o']).isdisjoint(set(datum['i']))
               for datum in concept_examples[purpose][concept])

def elements_same(program, purpose, concept, *args):
    return all(set(datum['o']) == set(datum['i'])
               for datum in concept_examples[purpose][concept])

def elements_super(program, purpose, concept, *args):
    return (all(set(datum['o']).issuperset(set(datum['i']))
               for datum in concept_examples[purpose][concept]) and
            not elements_same(program, purpose, concept, *args))

def elements_sub(program, purpose, concept, *args):
    return (all(set(datum['o']).issubset(set(datum['i']))
               for datum in concept_examples[purpose][concept]) and
            not elements_same(program, purpose, concept, *args))

def elements_overlapping(program, purpose, concept, *args):
    return (any(len(set(datum['i']).difference(set(datum['o']))) > 0
                 for datum in concept_examples[purpose][concept]) and
            any(len(set(datum['o']).difference(set(datum['i']))) > 0
                 for datum in concept_examples[purpose][concept]))

def is_constant(program, purpose, concept, *args):
    return len({str(datum['o']) for datum in concept_examples[purpose][concept]}) == 1

def input_repeats(program, purpose, concept, *args):
    return all(len(datum['i']) > len(set(datum['i'])) for datum in concept_examples[purpose][concept])

def output_repeats(program, purpose, concept, *args):
    return all(len(datum['o']) > len(set(datum['o'])) for datum in concept_examples[purpose][concept])

def constant_distance(program, purpose, concept, *args):
    return len({textdistance.levenshtein.distance(datum['i'], datum['o'])
                for datum in concept_examples[purpose][concept]}) == 1

def monotonic_o_up(program, purpose, concept, *args):
    return all(monotonic(datum['o']) and (len(datum['o']) > 1) for datum in concept_examples[purpose][concept])

def monotonic_o_down(program, purpose, concept, *args):
    return all(monotonic(list(reversed(datum['o']))) and (len(datum['o']) > 1) for datum in concept_examples[purpose][concept])

def monotonic_i_up(program, purpose, concept, *args):
    return all(monotonic(datum['i']) for datum in concept_examples[purpose][concept])

def monotonic_i_down(program, purpose, concept, *args):
    return all(monotonic(list(reversed(datum['i']))) for datum in concept_examples[purpose][concept])

def ones_and_zeros(program, purpose, concept, *args):
    return all(set(datum['o']) == set([0, 1]) for datum in concept_examples[purpose][concept])

def counts_or_indices(program, purpose, concept, *args):
    return all(len(datum['o']) == 0 or max(datum['o']) <= len(datum['i']) for datum in concept_examples[purpose][concept])

def common_spacing_0(program, purpose, concept, *args):
    return (all(len(set(datum['o'])) == 1 for datum in concept_examples[purpose][concept]) and
            any(len(datum['o']) > 1 for datum in concept_examples[purpose][concept]))


def common_spacing_1(program, purpose, concept, *args):
    return (all((len(set(spacing(datum['o']))) == 1) and (len(set(datum['o'])) > 1)
               for datum in concept_examples[purpose][concept]) and
            any(len(datum['o']) > 2 for datum in concept_examples[purpose][concept]))

def common_spacing_2(program, purpose, concept, *args):
    return (all((len(set(spacing(spacing(datum['o'])))) == 1) and (len(set(spacing(datum['o']))) > 1) and (len(set(datum['o'])) > 1)
               for datum in concept_examples[purpose][concept]) and
            any(len(datum['o']) > 3 for datum in concept_examples[purpose][concept]))

def contains_length(program, purpose, concept, *args):
    return all((len(datum['o']) > 0) and (len(datum['i']) in datum['o'])
               for datum in concept_examples[purpose][concept])

def reverse_heuristic(program, purpose, concept, *args):
    return all(datum['o'] == list(reversed(datum['i']))
               for datum in concept_examples[purpose][concept])

def contains_less(program, purpose, concept, *args):
    return all((len(datum['i']) == 0) or any(x < min(datum['i']) for x in datum['o'])
               for datum in concept_examples[purpose][concept])

def contains_greater(program, purpose, concept, *args):
    return all((len(datum['i']) == 0) or any(x > max(datum['i']) for x in datum['o'])
               for datum in concept_examples[purpose][concept])

def contains_min(program, purpose, concept, *args):
    return all((len(datum['i']) > 0) and (min(datum['i']) in datum['o'])
               for datum in concept_examples[purpose][concept])

def contains_max(program, purpose, concept, *args):
    return all((len(datum['i']) > 0) and (max(datum['i']) in datum['o'])
               for datum in concept_examples[purpose][concept])

def single_sometimes_zero(program, purpose, concept, *args):
    return (all(len(datum['o']) == 1
                for datum in concept_examples[purpose][concept]) and
            any((datum['o'][0] == 0) and (0 in datum['i'])
                for datum in concept_examples[purpose][concept]))

def shared_order(program, purpose, concept, *args):
    return all(shares_order(datum['i'], datum['o'])
               for datum in concept_examples[purpose][concept])

def shared_i_continuous(program, purpose, concept, *args):
    return all(shared_is_continuous(datum['i'], datum['o'])
               for datum in concept_examples[purpose][concept])

def shared_o_continuous(program, purpose, concept, *args):
    return all(shared_is_continuous(datum['o'], datum['i'])
               for datum in concept_examples[purpose][concept])

def output_length_same(program, purpose, concept, *args):
    return any(all(len(datum['o']) == x for datum in concept_examples[purpose][concept])
               for x in range(0, max(len(datum['o']) for datum in concept_examples[purpose][concept])+1))

def output_long(program, purpose, concept, *args):
    return all(5 < len(datum['o']) for datum in concept_examples[purpose][concept])

def output_short(program, purpose, concept, *args):
    return all((1 < len(datum['o']) < 6) for datum in concept_examples[purpose][concept])

def monotonic(xs):
    if xs == []:
        return True
    biggest = xs[0]
    for x in xs:
        if x < biggest:
            return False
        if x > biggest:
            biggest = x
    return True

def spacing(xs):
    return [xs[i+1]-xs[i] for i in range(len(xs)-1)]

def shared(xs, ys):
    ixs = xs[:]
    iys = ys[:]
    zs = []
    for x in ixs:
        if x in iys:
            zs.append(x)
            iys.remove(x)
    return zs

def shares_order(xs, ys):
    shared_elements = shared(xs, ys)
    if shared_elements == []:
        return False
    ps = permutations(shared_elements)
    if len(xs) < len(ys):
        short_list = xs
        long_list = ys
    else:
        short_list = ys
        long_list = xs
    return any(match_order(p, short_list) and match_order(p, long_list) for p in ps)

def match_order(query, xs):
    ix = 0
    iq = 0
    while True:
        if iq == len(query):
            return True
        elif ix == len(xs):
            return False
        elif query[iq] == xs[ix]:
            iq += 1
            ix += 1
        else:
            ix += 1

def shared_is_continuous(xs, ys):
    zs = shared(xs, ys)
    n = len(zs)
    if n == 0:
        return False
    ps = list(permutations(zs))
    for i in range(0, len(xs)-n+1):
        if tuple(xs[i:i+n]) in ps:
            return True
    return False

heuristic_features = {
    'feature_constant': is_constant,
    'feature_constant_distance': constant_distance,
    'feature_contains_GT': contains_greater,
    'feature_contains_LT': contains_less,
    'feature_contains_length': contains_length,
    'feature_contains_max': contains_max,
    'feature_contains_min': contains_min,
    'feature_counts_or_indices': counts_or_indices,
    'feature_input_repeats': input_repeats,
    'feature_monotonic_down': monotonic_o_down,
    'feature_monotonic_up': monotonic_o_up,
    'feature_output_1': output_1,
    'feature_output_EQ': output_EQ,
    'feature_output_GT': output_GT,
    'feature_output_LT': output_LT,
    'feature_output_disjoint': elements_disjoint,
    'feature_output_length_same': output_length_same,
    'feature_output_long': output_long,
    'feature_output_overlap': elements_overlapping,
    'feature_output_repeats': output_repeats,
    'feature_output_same': elements_same,
    'feature_output_short': output_short,
    'feature_output_sub': elements_sub,
    'feature_output_super': elements_super,
    'feature_range': common_spacing_1,
    'feature_repeated_element': common_spacing_0,
    'feature_reverse': reverse_heuristic,
    'feature_shared_i_continuous': shared_i_continuous,
    'feature_shared_o_continuous': shared_o_continuous,
    'feature_shared_order': shared_order,
    'feature_zero': single_sometimes_zero,
    # input begins with output
    # input contains output
    # input ends with output
    # output begins with input
    # output contains input
    # output ends with input
    # 'feature_monotonic_i_down': monotonic_i_down,
    # 'feature_monotonic_i_up': monotonic_i_up,
    # 'feature_ones_and_zeros': ones_and_zeros,
}


all_features = {}
for features in [all_primitives, grouped_features, recursive_features, pre_features, misc_features, heuristic_features]:
# for features in [heuristic_features]:
    all_features.update(features)

def add_feature(outrow, feature, value):
    if value is True:
        outrow[feature] = 'TRUE'
    elif value is False:
        outrow[feature] = 'FALSE'
    else:
        outrow[feature] = value

def generate_features(infile, outfile):
    with open(infile, 'r', newline='') as inf, open(outfile, 'w', newline='') as outf:

        reader = csv.DictReader(inf)
        writer = csv.DictWriter(outf, ['id', 'purpose', 'program', 'gloss'] + list(all_features.keys()))
        writer.writeheader()

        for inrow in reader:
            print(inrow['id'])
            outrow = {
                'id': inrow['id'],
                'purpose': inrow['purpose'],
                'program': inrow['program'],
                'gloss': inrow['gloss']
            }
            parsed = parse(inrow['program'])

            for feature in all_features:
                feat = all_features[feature](parsed, inrow['purpose'], inrow['id'], inrow['program'])
                add_feature(outrow, feature, feat)

            # HACK: exceptions
            if inrow['purpose'] == 'dataset' and inrow['id'] in ['c073', 'c111']:
                outrow['counting'] = 'n'
            if inrow['purpose'] == 'model' and inrow['id'] in ['c002', 'c004', 'c082', 'c084']:
                outrow['recursive'] = 'n'
            if inrow['purpose'] == 'dataset' and inrow['id'] in ['c017']:
                outrow['recursive'] = 'y'

            writer.writerow(outrow)


if __name__ == '__main__':
    generate_features(sys.argv[1], sys.argv[2])
