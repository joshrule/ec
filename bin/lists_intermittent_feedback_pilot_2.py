import matplotlib
matplotlib.use('Agg')

try:
    import binutil  # required to import from dreamcoder modules
except ModuleNotFoundError:
    import bin.binutil  # alt import if called as module

import glob
import itertools
import json
import math
import numpy as np
import pandas as pd
import random
import re
import subprocess
import sys
from ast import literal_eval
from dreamcoder.program import Program, Primitive, prettyProgram
from dreamcoder.type import *
from dreamcoder.grammar import Grammar
from functools import reduce
from joblib import Parallel, delayed, parallel_backend

# Define ourselves a failure mode for recursion
class RecursionDepthExceeded(Exception):
    pass

# notice that these are curried
def _reverse(x): return list(reversed(x))
def _cons(x): return lambda xs: [x] + xs
def _append(xs): return lambda x: xs + [x]
def _single(x): return [x]
def _concat(x): return lambda y: x + y
def _unique(x): return list(dict.fromkeys(x))
def _product(x): return reduce(lambda x,y: x*y, x, 1)
def _first(x): return x[0]
def _second(x): return x[1]
def _third(x): return x[2]
def _nth(i):
    if i > 0:
        return lambda x: x[i-1]
    else:
        raise IndexError
def _repeat(x): return lambda n: [x]*n
def _range(start): return lambda step: lambda stop: list(range(start, stop+1 if step > 0 else stop-1, step))
def _last(x): return x[-1]
def _drop(i): return lambda xs: xs[i:]
def _droplast(i): return lambda xs: xs[:-i] if i > 0 else xs[:]
def _take(i): return lambda xs: xs[:i]
def _takelast(i): return lambda xs: xs[-i:] if i > 0 else []
def _eq(x): return lambda y: x == y
def _is_empty(x): 
    return len(x) == 0
def _mod(x): return lambda y: x % y
def _slice(x): return lambda y: lambda l: l[(x-1):y]
def _cut_idx(i): return lambda xs: xs[:(i-1)] + xs[i:]
def _cut_slice(i):
    def helper(j):
        if i > j:
            raise IndexError
        return lambda xs: xs[:(i-1)] + xs[j:]
    return helper
def _cut_val(v):
    def helper(xs):
        result = []
        found = False
        for x in xs:
            if x != v or found:
                result.append(x)
            elif x == v:
                found = True
        return result
    return helper
def _cut_vals(v): return lambda xs: [x for x in xs if x != v]
def _replace(idx): return lambda y: lambda xs: [y if i == idx else x for i, x in enumerate(xs, 1)]
def _flatten(l): return [x for xs in l for x in xs]
def _map(f): return lambda l: list(map(f, l))
def _if(c): return lambda t: lambda f: t if c else f
def _addition(x): return lambda y: x + y
def _subtraction(x): return lambda y: x - y
def _multiplication(x): return lambda y: x * y
def _division(x):
    def helper(y):
        if y == 0:
            raise ValueError
        return x // y
    return helper
def _gt(x): return lambda y: x > y
def _lt(x): return lambda y: x < y
# not the most general form (i.e. zip-with) but it matches standard usage
def _zip(xs): return lambda ys: [list(x) for x in zip(xs, ys)]
def _mapi(f): return lambda l: list(map(lambda i_x: f(i_x[0])(i_x[1]), enumerate(l, 1)))
def _and(x): return lambda y: x and y
def _or(x): return lambda y: x or y
def _not(x): return not x
def _group(key):
    def helper(xs):
        keys = []
        groups = {}
        for x in xs:
            k = key(x)
            if k not in groups:
                keys.append(k)
                groups[k] = [x]
            else:
                groups[k].append(x)
        return [groups[k] for k in keys]
    return helper
def _is_even(x): return x % 2 == 0
def _is_odd(x): return x % 2 == 1
def _count(p): return lambda xs: sum(p(x) for x in xs)
def _filter(f): return lambda xs: list(filter(f, xs))
def _filteri(f): return lambda xs: [x for i, x in enumerate(xs, 1) if f(i)(x)]
def _fold(f): return lambda x0: lambda xs: reduce(lambda a, x: f(a)(x), xs, x0)
def _foldi(f): return lambda x0: lambda xs: reduce(lambda a, t: f(t[0])(a)(t[1]), enumerate(xs, 1), x0)
def _is_in(xs): return lambda x: x in xs
def _find(p): return lambda xs: [i for i, x in enumerate(xs, 1) if p(x)]
def _insert(x): return lambda i: lambda xs: xs[:(i-1)] + [x] + xs[(i-1):]
def _splice(x): return lambda i: lambda xs: xs[:(i-1)] +  x  + xs[(i-1):]
def _tail(xs): return xs[1:]
def _swap(i):
    def swap_helper_j(j):
        def swap_helper_xs(xs):
            fst = min(i,j)
            snd = max(i,j)
            return xs[:(fst-1)] + [xs[(snd-1)]] + xs[fst:(snd-1)] + [xs[(fst-1)]] + xs[snd:]
        return swap_helper_xs
    return swap_helper_j
def _sort(k): return lambda xs: sorted(xs, key=k)
def _fix(argument):
    def inner(body):
        recursion_limit = [50]

        def fix(x):
            def r(z):
                recursion_limit[0] -= 1
                if recursion_limit[0] <= 0:
                    raise RecursionDepthExceeded()
                else:
                    return fix(z)

            return body(r)(x)
        return fix(argument)

    return inner

# define some primitives
def primitives():
    return [Primitive(str(j), tint, j) for j in range(-2,100)] + [
        Primitive("%", arrow(tint, tint, tint), _mod),
        Primitive("*", arrow(tint, tint, tint), _multiplication),
        Primitive("+", arrow(tint, tint, tint), _addition),
        Primitive("-", arrow(tint, tint, tint), _subtraction),
        Primitive("/", arrow(tint, tint, tint), _division),
        Primitive("<", arrow(tint, tint, tbool), _lt),
        Primitive("==", arrow(t0, t0, tbool), _eq),
        Primitive(">", arrow(tint, tint, tbool), _gt),
        Primitive("abs", arrow(tint, tint), abs),
        Primitive("and", arrow(tbool, tbool, tbool), _and),
        Primitive("append", arrow(tlist(t0), t0, tlist(t0)), _append),
        Primitive("concat", arrow(tlist(t0), tlist(t0), tlist(t0)), _concat),
        Primitive("cons", arrow(t0, tlist(t0), tlist(t0)), _cons),
        Primitive("count", arrow(arrow(t0, tbool), tlist(t0), tint), _count),
        Primitive("cut_idx", arrow(tint, tlist(t0), tlist(t0)), _cut_idx),
        Primitive("cut_slice", arrow(tint, tint, tlist(t0), tlist(t0)), _cut_slice),
        Primitive("cut_val", arrow(t0, tlist(t0), tlist(t0)), _cut_val),
        Primitive("cut_vals", arrow(t0, tlist(t0), tlist(t0)), _cut_vals),
        Primitive("drop", arrow(tint, tlist(t0), tlist(t0)), _drop),
        Primitive("droplast", arrow(tint, tlist(t0), tlist(t0)), _droplast),
        Primitive("empty", tlist(t0), []),
        Primitive("false", tbool, False),
        Primitive("filter", arrow(arrow(t0, tbool), tlist(t0), tlist(t0)), _filter),
        Primitive("filteri", arrow(arrow(tint, t0, tbool), tlist(t0), tlist(t0)), _filteri),
        Primitive("flatten", arrow(tlist(tlist(t0)), tlist(t0)), _flatten),
        Primitive("fold", arrow(arrow(t1, t0, t1), t1, tlist(t0), t1), _fold),
        Primitive("foldi", arrow(arrow(tint, t1, t0, t1), t1, tlist(t0), t1), _foldi),
        Primitive("group", arrow(arrow(t0, t1), tlist(t1), tlist(tlist(t1))), _group),
        Primitive("first", arrow(tlist(t0), t0), _first),
        Primitive("second", arrow(tlist(t0), t0), _second),
        Primitive("third", arrow(tlist(t0), t0), _third),
        Primitive("if", arrow(tbool, t0, t0, t0), _if),
        Primitive("is_even", arrow(tint, tbool), _is_even),
        Primitive("is_odd", arrow(tint, tbool), _is_odd),
        Primitive("last", arrow(tlist(t0), t0), _last),
        Primitive("length", arrow(tlist(t0), tint), len),
        Primitive("map", arrow(arrow(t0, t1), tlist(t0), tlist(t1)), _map),
        Primitive("mapi", arrow(arrow(tint, t0, t1), tlist(t0), tlist(t1)), _mapi),
        Primitive("max", arrow(tlist(t0), tint), max),
        Primitive("min", arrow(tlist(t0), tint), min),
        Primitive("not", arrow(tbool, tbool), _not),
        Primitive("nth", arrow(tint, tlist(t0), t0), _nth),
        Primitive("or", arrow(tbool, tbool, tbool), _or),
        Primitive("product", arrow(tlist(tint), tint), _product),
        Primitive("range", arrow(tint, tint, tint, tlist(tint)), _range),
        Primitive("repeat", arrow(t0, tint, tlist(t0)), _repeat),
        Primitive("replace", arrow(tint, t0, tlist(t0), tlist(t0)), _replace),
        Primitive("reverse", arrow(tlist(t0), tlist(t0)), _reverse),
        Primitive("singleton", arrow(t0, tlist(t0)), _single),
        Primitive("slice", arrow(tint, tint, tlist(t0), tlist(t0)), _slice),
        Primitive("sort", arrow(arrow(t0, tint), tlist(t0), tlist(t0)), _sort),
        Primitive("sum", arrow(tlist(tint), tint), sum),
        Primitive("take", arrow(tint, tlist(t0), tlist(t0)), _take),
        Primitive("takelast", arrow(tint, tlist(t0), tlist(t0)), _takelast),
        Primitive("true", tbool, True),
        Primitive("unique", arrow(tlist(t0), tlist(t0)), _unique),
        Primitive("zip", arrow(tlist(t0), tlist(t0), tlist(tlist(t0))), _zip),
        Primitive("is_in", arrow(tlist(t0), t0, tbool), _is_in),
        Primitive("find", arrow(arrow(t0, tbool), tlist(t0), tlist(tint)), _find),
        Primitive("insert", arrow(t0, tint, tlist(t0), tlist(t0)), _insert),
        Primitive("splice", arrow(tlist(t0), tint, tlist(t0), tlist(t0)), _splice),
        Primitive("swap", arrow(tint, tint, tlist(t0), tlist(t0)), _swap),
    ]

# Example scoring library

def proportion(xs, f):
    return sum(f(i, o) for i,o in xs)/len(xs)

def proportion_set(xs, f):
    return len({f(i, o) for i,o in xs})/len(xs)

def limit(xs, accept, f):
    return max(0, sum(f(i, o) for i,o in xs) - accept)

def forbid(xs, f):
    return limit(xs, 0, f)

def center(xs, f, factor = 1/2):
    return 1 + abs(factor * len(xs) - sum(f(i,o) for i, o in xs))

def proportion_unique_elements(xs):
   return sum(len(set(i)) for i,o in xs) / sum(len(i) for i,o in xs)

#

def example_functions():
    return [
        {
            'concept': '(lambda (singleton (count (lambda (== $0 7)) $0)))',
            'adjust': lambda xs: 3 * all(len(i) >= 5 for i, o in xs) + 2 * proportion_unique_elements(xs) + 3 * proportion_set(xs, lambda i,o: o[0])
        }
        ,
        {
            'concept': '(lambda (map (lambda (+ 1 $0)) $0))',
            'adjust': lambda xs: 3 * proportion_set(xs, lambda i,o: len(i)) + 3 * proportion_unique_elements(xs)
        },
        {
            "concept": "(lambda (map sum (filteri (lambda (lambda (is_odd $1))) (zip (if (is_odd (length $0)) $0 (droplast 1 $0)) (if (is_odd (length $0)) (append (drop 1 $0 ) 0) (drop 1 $0))))))",
            'adjust': lambda xs: 3 * all(len(i) >= 6 and len(i)%2 == 0 for i, o in xs) + 3 * proportion_unique_elements(xs)
        },
        {
            'concept': '(lambda (filter (lambda (> $0 17)) $0))',
            "adjust": lambda xs: 2 * proportion_unique_elements(xs) + 2 * proportion(xs, lambda i,o: len(i) >= 7) + 2 * proportion(xs, lambda i,o: 5 >= len(i) - len(o) >= 2)
        },
    ]

# Singular Sampling algorithm

def sample_private_examples(p,adjust,n=10,n_restarts=1000,n_tries=1000,small=False,max_len=10,exclude=None):
    bests = Parallel(n_jobs = -1, verbose = 0)(delayed(greedy_set)(p, adjust, n, n_tries, small, max_len, exclude) for _ in range(n_restarts))
    return max(bests, key = lambda x: x[1])[0]

def greedy_set(p,adjust,n,n_tries,small,max_len,exclude):
    if exclude is None:
        exclude = []
    s = initialize_set(p,n,small,max_len,exclude)
    score = score_set(s, adjust)
    for i_try in range(n_tries):
        i = sample_input(small, max_len)
        if i not in list(zip(*s))[0]:
            try:
                o = p.runWithArguments([i])
            except:
                continue
            if valid_output(o, small, max_len) and ((i,o) not in exclude or exclude_exclude(i, o, small)):
                idx = random.randint(0, n-1)
                new_s = s[:]
                new_s[idx] = (i,o)
                new_score = score_set(new_s, adjust)
                if new_score > score:
                    s = new_s
                    score = new_score
    return s, score

def initialize_set(p,n,small,max_len,exclude):
    s = []
    while len(s) < n:
        i = sample_input(small, max_len)
        try:
            o = p.runWithArguments([i])
        except:
            continue
        if valid_output(o, small, max_len) and (len(s) == 0 or i not in list(zip(*s))[0]) and ((i, o) not in exclude or exclude_exclude(i, o, small)):
            s.append((i,o))
    return s

# Common Sampling Algorithm

def sample_common_examples(ps,adjusts,n=10,n_restarts=1000,n_tries=1000,small=False,max_len=10,exclude=None):
    bests = Parallel(n_jobs = -1, verbose = 0)(delayed(greedy_common_set)(ps, adjusts, n, n_tries, small, max_len, exclude) for _ in range(n_restarts))
    return max(bests, key = lambda x: x[1])[0]

def greedy_common_set(ps,adjusts,n,n_tries,small,max_len,exclude):
    if exclude is None:
        exclude = []
    s = initialize_common_set(ps,n,small,max_len,exclude)
    score = score_common_set(s, adjusts)
    for i_try in range(n_tries):
        i = sample_input(small, max_len)
        if i not in list(zip(*s))[0]:
            # Get the outputs.
            try:
                os = [p.runWithArguments([i]) for p in ps]
            except:
                continue
            if valid_common_io_pair(i, os, small, max_len, exclude):
                idx = random.randint(0, n-1)
                new_s = s[:]
                new_s[idx] = (i,os)
                new_score = score_common_set(new_s, adjusts)
                if new_score > score:
                    s = new_s
                    score = new_score
    return s, score

def valid_common_io_pair(i, os, small, max_len, exclude):
    # Ensure that we have different answers for each function.
    if len(os) != len({str(o) for o in os}):
        return False
    # Ensure that the output is valid and that there are no exclusions.
    for o in os:
        if not valid_output(o, small, max_len) or ((i, o) in exclude or exclude_exclude(i, o, small)):
            return False
    return True

def score_common_set(s, adjusts):
    # Common scores are the sum over individual function scores.
    return sum(
        score_set([(x, ys[i]) for x, ys in s], adjust)
        for i, adjust in enumerate(adjusts)
    )

def initialize_common_set(ps,n,small,max_len,exclude):
    s = []
    while len(s) < n:
        i = sample_input(small, max_len)
        try:
            os = [p.runWithArguments([i]) for p in ps]
        except:
            continue
        if (len(s) == 0 or i not in list(zip(*s))[0]) and valid_common_io_pair(i, os, small, max_len, exclude):
            s.append((i,os))
    return s

# Scoring

def valid_output(xs, small, max_len):
    return len(xs) == 0 or (len(xs) <= max_len and max(xs) < (10 if small else 100) and min(xs) >= 0)

def score_set(s, adjust):
    (inputs, outputs) = zip(*s)
    n = len(s)

    # Measure the distribution of output lengths
    out_ws = [sum(len(o) == l for o in outputs) for l in range(11)]
    foil = [len(s)//11 + (1 if x < len(s) % 11 else 0) for x in range(11)]
    out_len = simple_entropy(out_ws)/simple_entropy(foil)

    # Inputs are unique by construction.
    # Measure the proportion of unique outputs
    unique = len(list(itertools.groupby(outputs)))/n

    # Measure the proportion of non-trivial i/o pairs
    nontrivial = sum(i != o for i,o in s)/n

    # Measure the distribution of list elements.
    all_items = _flatten(_flatten(s))
    ws = [sum(i == j for i in all_items) for j in range(100)]
    foil = [len(all_items)//100 + (1 if x < len(all_items) % 100 else 0) for x in range(100)]
    span = simple_entropy(ws)/simple_entropy(foil)

    # Measure the distribution over input lengths
    in_ws = [sum(len(i) == l for i in inputs) for l in range(11)]
    foil = [len(s)//11 + (1 if x < len(s) % 11 else 0) for x in range(11)]
    in_len = simple_entropy(in_ws)/simple_entropy(foil)

    # Adjust the score if necessary.
    adjustment = 0 if adjust is None else adjust(s)

    # print(f"{out_len/5} {unique/5} {nontrivial/5} {span/5} {in_len/5} {adjustment}")
    return (out_len + unique + nontrivial + span + in_len)/5 + adjustment

# Sampling lists library

def flip(p=0.5):
    return random.random() < p

def sample_element(small):
    if small or flip(0.5):
        return random.randint(0, 9)
    return random.randint(0, 99)

def sample_input(small, max_len=10, l=None, r=None):
    length = random.randint(0, max_len) if l is None else l
    repetitions = (random.randint(0, length-1) if r is None else r) if length > 1 else 0
    xs = set()
    while len(xs) < length-repetitions:
        xs.add(sample_element(small))
    xs = list(xs)
    xs.extend([random.choice(xs) for _ in range(repetitions)])
    random.shuffle(xs)
    return xs

# Utility functions

def simple_entropy(ws):
    z = sum(ws)
    return -sum(w/z*math.log2(w/z) for w in ws if w > 0)

def sample_programs(g, type_of_sample, n=10):
    return [grammar.sample(type_of_sample, maximumDepth=10) for _ in range(n)]

def test_p_with_i(e, i):
    p = Program.parse(e)
    o = p.runWithArguments([i])
    return o

def list_primitives():
    print("Primitives:")
    for primitive in Primitive.GLOBALS:
        print(f"- {primitive}")

def make_grammar():
    Primitive.GLOBALS.clear()
    return Grammar.uniform(primitives())

def pretty_print(e):
    Primitive.GLOBALS.clear()
    grammar = Grammar.uniform(primitives())
    return(prettyProgram(Program.parse(e), Lisp=True))

# Core sampling logic functions

def generate_manual_trials(concepts, inputs, verbose=True, small=False, exclude=None, just=None):
    Primitive.GLOBALS.clear()
    grammar = Grammar.uniform(primitives())
    ps = [Program.parse(c['concept']) for c in concepts]
    tp = arrow(tlist(tint), tlist(tint))
    check_types(ps, tp, verbose)
    examples = []
    for inp in inputs:
        examples.append({'input': inp[:], 'outputs': []})
        for i, p in enumerate(ps):
            if just == None or just == i:
                examples[-1]['outputs'].append(p.runWithArguments([inp]))
            else:
                examples[-1]['outputs'].append(None)
    check_examples(examples, exclude, small)
    random.shuffle(examples)
    return examples

def generate_common_trials(concepts, n_trials=10, verbose=True, small=False, max_len=10, exclude=None):
    Primitive.GLOBALS.clear()
    grammar = Grammar.uniform(primitives())
    ps = [Program.parse(c['concept']) for c in concepts]
    tp = arrow(tlist(tint), tlist(tint))
    check_types(ps, tp, verbose)
    ads = [c['adjust'] for c in concepts]
    example_pairs = sample_common_examples(
        ps,
        ads,
        n=n_trials,
        n_restarts=2000,
        n_tries=2000,
        small=small,
        max_len=max_len,
        exclude=exclude
    )
    examples = [{'input': x[:], 'outputs': y[:]} for x, y in example_pairs]
    check_examples(examples, exclude, small)
    random.shuffle(examples)
    return examples

def generate_private_trials(concept, idx, total, n_trials=10, verbose=True, small=False, max_len=10, exclude=None):
    Primitive.GLOBALS.clear()
    grammar = Grammar.uniform(primitives())
    p = Program.parse(c['concept'])
    tp = arrow(tlist(tint), tlist(tint))
    check_types([p], tp, verbose)
    example_pairs = sample_private_examples(
        p,
        c['adjust'],
        n=n_trials,
        n_restarts=2000,
        n_tries=2000,
        small=small,
        max_len=max_len,
        exclude=exclude
    )
    examples = [{'input': x[:], 'outputs': [None] * total} for x, _ in example_pairs]
    for ex, (_, y) in zip(examples, example_pairs):
        ex['outputs'][idx] = y[:]
    check_examples(examples, exclude, small)
    random.shuffle(examples)
    return examples

def check_types(ps, tp, verbose):
    success = True
    print(f"desired type: {tp}", flush=True)
    for p in ps:
        if verbose:
            print(f"type checking `{p}`", flush=True)
        if not p.canHaveType(tp):
            success = False
            if verbose:
                print(f"    incorrect type {p.infer()}", flush=True)
    if not success:
        raise ValueError("Incorrect program types")

def check_examples(examples, exclude, small):
    for example in examples:
        print(example)
        if exclude is not None:
            for output in example['outputs']:
                if (example['input'], output) in exclude:
                    if not exclude_exclude(example['input'], output, small):
                        raise Exception(f'forbidden duplicate: {example}')
                    else:
                        print(f'exception allowed by exclude_exclude: {example}')

def blah():
    # Write files
    data = {
        'id': f"c{i:03}",
        'program': c['concept'],
        'data': [{"i": i, "o": o} for i,o in examples]
    }
    with open(f"{dirname}/c{i:03}_1.json", "w") as fd:
        fd.write(json.dumps(data))
    print(f'id: c{i:03}')
    print(f'program: {c["concept"]}')
    for inp,oup in examples:
        print(f'  {str(inp).ljust(50)} -> {oup}')

def load_big_bench_stimuli(dirname):
    records = []
    for subdirname in glob.glob(f'{dirname}/c*'):
        with open(f'{subdirname}/task.json', 'rb') as fd:
            task = json.load(fd)
        for example in task['examples']:
            records.append({
                'id': task['name'],
                'i': example['input'],
                'o': example['target'],
            })
    return records

def load_behavioral_stimuli(filename):
    return list(
        pd.read_csv(filename)[["id", "input", "output"]]
          .rename(columns={'input': 'i', 'output': 'o'})
          .to_records()
    )

def exclude_exclude(i, o, small):
    return small and len(i) <= 1 and len(o) <= 1 

def concepts():
    return [
        # headth element
        {
            'concept': '(lambda (singleton (nth (first $0) (drop 1 $0))))',
            'adjust': lambda xs: proportion(xs, lambda i,o: i[0] <= len(i)-1) + proportion_set(xs, lambda i,o: i[0]) + proportion_unique_elements(xs) + proportion_set(xs, lambda i,o: len(i)-i[0]) - 0.25 * limit(xs, 1, lambda i,o: i[0] == 1 or i[1] == len(i)-1) + proportion_set(xs, lambda i,o: o[0])
        },
        # most common element
        {
            'concept': '(lambda (singleton (fold (lambda (lambda (if (> (count (== $1) $2) (count (== $0) $2)) $1 $0))) (first (unique $0)) (drop 1 (unique $0)))))',
            'adjust': lambda xs: proportion_set(xs, lambda i,o: o[0]) + proportion_unique_elements(xs) + proportion(xs, lambda i,o: len(i) >= 7)
        },
        # last
        {
            'concept': '(lambda (takelast 1 $0))',
            'adjust': lambda xs: proportion(xs, lambda i,o: len(i) > 1) + proportion_unique_elements(xs) + proportion_set(xs, lambda i,o: len(o)) + proportion_set(xs, lambda i,o: o[0] if len(o) > 0 else -1) - limit(xs, 0, lambda i,o: len(o) == 0)
        },
        # minimum
        {
            'concept': '(lambda (singleton (min $0)))',
            'adjust': lambda xs: 2 * proportion_set(xs, lambda i,o: o[0]) + proportion_unique_elements(xs)
        },
        # nUnique
        {
            'concept': '(lambda (singleton (length (unique $0))))',
            'adjust': lambda xs: 2 * proportion_set(xs, lambda i,o: o[0]) + proportion_unique_elements(xs) + proportion(xs, lambda i,o: len(i) >= 7)
        },
    ]

if __name__ == "__main__":
    
    ## Set random seed for reproducibility.
    random.seed(123)

    ## Generate new I/O pairs.

    cs = concepts()

    # Generate 5 common trials with feedback.

    common_inputs = [
        [6,3,3,5,6,5,3],
        [5,8,4,5,6,4,4],
        [7,9,7,3,3,7,9,3,9,3],
        [2,4,2,4,2,2],
        [6,5,7,8,5,6,5,9,6,5],
    ]


    common_trials_with_feedback = generate_manual_trials(
        cs,
        common_inputs,
        verbose=True,
        small=True
    )

    print(common_trials_with_feedback)
    print()

    # We also provide 5 private trials per function.

    private_inputs = [
        # headth
        [
            [5,3,4,0,2,0,6,7,9,1],
            [4,2,8,7,6,5,1,1,9],
            [6,6,0,1,9,3,7,1],
            [1,9,8,4,3,5,3,5,6],
            [7,0,7,9,1,1,4,8,1,0],
        ],
        # most common
        [
            [9,7,4,9,1,0,6,2],
            [1,6,5,0,2,9,0,7,3],
            [4],
            [6,1,2,9,5,2,1,2,6,9],
            [0,8,1,3,5,9,8],
        ],
        # last
        [
            [1,9,7,8,0,6,6,4],
            [7,7,5,8,1,9],
            [3,0],
            [6,5,2,2,0,2,0,9,1,7],
            [2,4,0,0,6,8,1],
        ],
        # minimum
        [
            [9,8,6,7,9],
            [1,0,2],
            [4,7,6,8,3,8,5],
            [5,4,7,8,3,7,2,2,9,1],
            [7,7,8,7,9,8,9],
        ],
        # nUnique
        [
            [5,4,2,6,7,7,1],
            [],
            [7,7,7,3,2,9,4,1,6,8],
            [0,1,7,3,0,6,6,5,4],
            [2,6,4,9,6,5],
        ]
    ]

    private_trials_with_feedback = []
    for i in range(len(cs)):
        private_trials_with_feedback.append(generate_manual_trials(
            cs,
            private_inputs[i],
            verbose=True,
            small=True,
            exclude = common_trials_with_feedback,
            just = i,
        ))

    print(private_trials_with_feedback)
    print()

    # # Generate 40 common trials without feedback.

    common_trials_without_feedback = generate_common_trials(
        cs,
        n_trials=40,
        verbose=True,
        small=True,
        max_len=10,
        exclude=common_trials_with_feedback + [y for x in private_trials_with_feedback for y in x],
    )

    print(common_trials_without_feedback)
    print()

    # Then, we generate another 10 private trials per function.
    private_trials_without_feedback = []
    for i, c in enumerate(cs):
        private_trials_without_feedback.append(generate_private_trials(
            c,
            i,
            len(cs),
            n_trials=10,
            verbose=True,
            small=True,
            max_len=10,
            exclude=common_trials_with_feedback + common_trials_without_feedback + private_trials_with_feedback[i],
        ))

    print(private_trials_without_feedback)

    # Then, we stitch it all together and write the JSON files.

    data = {
        'common_trials_with_feedback': common_trials_with_feedback,
        'common_trials_without_feedback': common_trials_without_feedback,
        'private_trials_with_feedback': private_trials_with_feedback,
        'private_trials_without_feedback': private_trials_without_feedback,
        'concepts': [c['concept'] for c in cs],
    }
    with open(f"tmp/data.json", "w") as fd:
        fd.write(json.dumps(data))

    for i, c in enumerate(cs):
        examples = (common_trials_with_feedback[0:1] +
                    common_trials_without_feedback[0:10] +
                    common_trials_with_feedback[1:2] +
                    common_trials_without_feedback[10:20] +
                    common_trials_with_feedback[2:3] +
                    common_trials_without_feedback[20:30] +
                    common_trials_with_feedback[3:4] +
                    common_trials_with_feedback[4:5] +
                    common_trials_without_feedback[30:40] +
                    private_trials_with_feedback[i] +
                    private_trials_without_feedback[i])
        data = {
            'id': i,
            'program': c['concept'],
            'data': [{"i": example['input'], "o": example['outputs'][i]} for example in examples]
        }
        with open(f"tmp/{i}.json", "w") as fd:
            fd.write(json.dumps(data))
