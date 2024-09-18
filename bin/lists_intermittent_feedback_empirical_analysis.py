import matplotlib
matplotlib.use('Agg')

try:
    import binutil  # required to import from dreamcoder modules
except ModuleNotFoundError:
    import bin.binutil  # alt import if called as module

import itertools
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
def _unique(xs): 
    ys = []
    for x in xs:
        if x not in ys:
            ys += [x]
    return ys
    # return list(dict.fromkeys(x))
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

def output_entropy(xs):
    ws = dict()
    for i, o in xs:
        if str(o) in ws:
            ws[str(o)] += 1
        else:
            ws[str(o)] = 1
    flat_ws = [v for k,v in ws.items()]
    return simple_entropy(flat_ws)

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

def exclude_exclude(i, o, small):
    return small and len(i) <= 1 and len(o) <= 1 

def concepts():
    return [
        # most common element
        {
            'name': 'most_common',
            'concept': '(lambda (singleton (fold (lambda (lambda (if (> (count (== $0) $2) (count (== $1) $2)) $0 $1))) (first (unique $0)) (drop 1 (unique $0)))))',
        },
        # id 
        {
            'name': 'id',
            'concept': '(lambda $0)',
        },
        # length
        {
            'name': 'length',
            "concept": "(lambda (singleton (length $0)))",
        },
        # first
        {
            'name': 'first',
            "concept": "(lambda (take 1 $0))",
        },
        # last
        {
            'name': 'last',
            "concept": "(lambda (takelast 1 $0))",
        },
        # add_1
        {
            'name': 'add_1',
            "concept": "(lambda (map (lambda (+ 1 $0)) $0))",
        },
        # min
        {
            'name': 'min',
            "concept": "(lambda (singleton (min $0)))",
        },
        # max
        {
            'name': 'max',
            "concept": "(lambda (singleton (max $0)))",
        },
        # add consecutive pairs
        {
            'name': 'add_pairs',
            'concept': '(lambda (map (lambda (if (> (+ $0 1) (length $1)) (nth $0 $1) (+ (nth $0 $1) (nth (+ $0 1) $1)))) (range 1 2 (length $0))))',
        },
        # # unique even elements
        {
            'name': 'n_unique_even',
            "concept": "(lambda (singleton (length (filter is_even (unique $0)))))",
        },
        # # most common digit
        {
            'name': 'n_most_common_digit',
            'concept': '(lambda ((lambda (singleton (fold (lambda (lambda (if (> (count (== $0) $2) $1) (count (== $0) $2) $1))) 0 (range 0 1 9)))) (flatten (map (lambda (if (> $0 9) (cons (/ $0 10) (singleton (% $0 10))) (singleton $0))) $0))))',
        },
        # most common digit
        {
            'name': 'most_common_digit',
            'concept': '(lambda ((lambda (singleton (fold (lambda (lambda (if (> (count (== $0) $2) (count (== $1) $2)) $0 $1))) 0 (range 1 1 9)))) (flatten (map (lambda (if (> $0 9) (cons (/ $0 10) (singleton (% $0 10))) (singleton $0))) $0))))',
        },
        # < 10
        {
            'name': 'less_than_10',
            "concept": "(lambda (filter (lambda (> 10 $0)) $0))",
        },
        # > 9
        {
            'name': 'greater_than_09',
            "concept": "(lambda (filter (lambda (< 9 $0)) $0))",
        },
    ]

if __name__ == "__main__":
    
    ## Set random seed for reproducibility.
    random.seed(123)

    ## Generate new I/O pairs.

    cs = concepts()

    # Generate 10 ambiguous trials with feedback.

    inputs = [
        [20, 20, 5, 5, 79, 20, 79],              
        [49, 0, 0, 0, 49, 61, 0, 5, 0, 75],      
        [7, 9, 8, 8, 43, 17, 8, 8, 8],           
        [30, 30, 30, 30, 1, 81, 45, 1, 81],      
        [65, 3, 68, 68, 65, 68, 65, 3],          
        [44],                                    
        [6, 6, 17],                              
        [81, 76, 76, 76, 67, 76, 1],             
        [87, 4, 87, 4, 49, 4, 4, 87, 7],         
        [9, 4, 4, 9, 4, 1, 1],                   
        [2, 74, 74, 2, 1, 74, 7, 0, 40],         
        [4, 8, 0, 58, 9, 46, 67, 13, 12, 50],    
        [18, 8, 40, 40, 5, 8, 0],                
        [42, 12, 12, 5, 0, 27, 9],               
        [74, 95, 93, 69, 38, 4, 1, 93],          
        [98, 2, 8, 39, 4, 1, 15, 1, 81],         
        [6, 6, 6, 4, 6, 6, 6, 6, 6, 4],          
        [23, 23, 23, 23, 23, 23, 23, 23, 23, 23],
        [82, 82, 82, 82, 0, 82, 82, 0, 0, 82],   
        [9, 20, 88, 1, 88, 88, 50, 49, 21, 49],  
        [2, 1, 4, 1, 4, 4, 4, 2, 4, 4],          
        [45, 45, 39, 7, 25, 29, 28, 0, 2],       
        [24, 1, 0, 85, 2, 9, 72, 90, 3, 66],     
        [5, 6, 51, 5, 5, 6, 65, 5, 71],          
        [49, 49, 49, 49, 49, 49, 49, 49, 49],    
        [99, 0, 6, 5, 5, 99, 5, 99, 99, 99],     
        [2, 5, 3, 8, 18, 82, 96, 0, 6],          
        [87, 87, 87, 87, 87, 87, 87, 87],        
        [5, 16, 8, 79, 31, 31, 7, 34, 12],       
        [92, 26, 80, 31, 7, 34, 80, 9, 80],      
        [24, 6, 24, 24, 24, 4, 24, 5, 24],       
        [6, 6, 2, 6, 26, 6, 2, 26],              
        [1, 38, 1, 1, 1, 1, 38, 1, 38, 1],       
        [9, 2, 2, 2, 9, 2, 0],                   
        [2, 26, 2, 68, 26, 68, 5, 2, 2, 2],  
    ]

    examples = generate_manual_trials(
        cs,
        inputs,
        verbose=True,
        small=False,
        exclude = None,
        just = None,
    )

    # Then, we write the JSON files.

    for i, c in enumerate(cs, start = 3):
        data = {
            'id': i,
            'name': c['name'],
            'program': c['concept'],
            'data': [{"i": example['input'], "o": example['outputs'][i-3]} for example in examples]
        }
        with open(f"tmp/{i:02d}.json", "w") as fd:
            fd.write(json.dumps(data))
