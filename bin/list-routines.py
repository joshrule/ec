try:
    import binutil  # required to import from dreamcoder modules
except ModuleNotFoundError:
    import bin.binutil  # alt import if called as module

import random
import math
import sys
from dreamcoder.program import Program, Primitive
from dreamcoder.type import *
from dreamcoder.grammar import Grammar
from functools import reduce

class RecursionDepthExceeded(Exception):
    pass

def _fix(argument):
    def inner(body):
        recursion_limit = [20]

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
# Here are the definitions for the primitives. They are all curried.
def _addition(x): return lambda y: x + y
def _and(x): return lambda y: x and y
def _append(xs): return lambda x: xs + [x]
def _concat(x): return lambda y: x + y
def _cons(x): return lambda xs: [x] + xs
def _count(p): return lambda xs: sum(p(x) for x in xs)
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
def _division(x):
    def helper(y):
        if y == 0:
            raise ValueError
        return x // y
    return helper
def _drop(i): return lambda xs: xs[i:]
def _droplast(i): return lambda xs: xs[:-i]
def _eq(x): return lambda y: x == y
def _filter(f): return lambda xs: list(filter(f, xs))
def _filteri(f): return lambda xs: [x for i, x in enumerate(xs, 1) if f(i)(x)]
def _find(p): return lambda xs: [i for i, x in enumerate(xs, 1) if p(x)]
def _first(x): return x[0]
def _flatten(l): return [x for xs in l for x in xs]
def _fold(f): return lambda x0: lambda xs: reduce(lambda a, x: f(a)(x), xs, x0)
def _foldi(f): return lambda x0: lambda xs: reduce(lambda a, t: f(t[0])(a)(t[1]), enumerate(xs, 1), x0)
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
def _gt(x): return lambda y: x > y
def _if(c): return lambda t: lambda f: t if c else f
def _insert(x): return lambda i: lambda xs: xs[:(i-1)] + [x] + xs[(i-1):]
def _is_empty(xs): return len(xs) == 0
def _is_even(x): return x % 2 == 0
def _is_in(xs): return lambda x: x in xs
def _is_odd(x): return x % 2 == 1
def _last(x): return x[-1]
def _lt(x): return lambda y: x < y
def _map(f): return lambda l: list(map(f, l))
def _mapi(f): return lambda l: list(map(lambda i_x: f(i_x[0])(i_x[1]), enumerate(l, 1)))
def _mod(x): return lambda y: x % y
def _multiplication(x): return lambda y: x * y
def _not(x): return not x
def _nth(i):
    if i > 0:
        return lambda x: x[i-1]
    else:
        raise IndexError
def _or(x): return lambda y: x or y
def _product(x): return reduce(lambda x,y: x*y, x, 1)
def _range(start): return lambda step: lambda stop: list(range(start, stop+1 if step > 0 else stop-1, step))
def _repeat(x): return lambda n: [x]*n
def _replace(idx): return lambda y: lambda xs: [y if i == idx else x for i, x in enumerate(xs, 1)]
def _reverse(x): return list(reversed(x))
def _second(x): return x[1]
def _single(x): return [x]
def _slice(x): return lambda y: lambda l: l[(x-1):y]
def _splice(x): return lambda i: lambda xs: xs[:(i-1)] +  x  + xs[(i-1):]
def _subtraction(x): return lambda y: x - y
def _swap(i): return lambda j: lambda xs: xs[:(i-1)] + [xs[(j-1)]] + xs[i:(j-1)] + [xs[(i-1)]] + xs[j:]
def _tail(xs): return xs[1:]
def _take(i): return lambda xs: xs[:i]
def _takelast(i): return lambda xs: xs[-i:]
def _third(x): return x[2]
def _unique(x): return list(dict.fromkeys(x))
def _zip(xs): return lambda ys: [list(x) for x in zip(xs, ys)]

def model_comparison_primitives_9():
    return _model_comparison_primitives(9)

def model_comparison_primitives_99():
    return _model_comparison_primitives(99)

def _model_comparison_primitives(max_num):
    return [Primitive(str(j), tint, j) for j in range(0,max_num+1)] + [
        Primitive("nan", tint, math.nan),
        Primitive("true", tbool, True),
        Primitive("false", tbool, False),
        Primitive("empty", tlist(t0), []),
        Primitive("cons", arrow(t0, tlist(t0), tlist(t0)), _cons),
        Primitive("+", arrow(tint, tint, tint), _addition),
        Primitive("-", arrow(tint, tint, tint), _subtraction),
        Primitive(">", arrow(tint, tint, tbool), _gt),
        Primitive("fix", arrow(t0, arrow(arrow(t0, t1), t0, t1), t1), _fix),
        Primitive("head", arrow(tlist(t0), t0), _first),
        Primitive("if", arrow(tbool, t0, t0, t0), _if),
        Primitive("is_empty", arrow(t0, t0, tbool), _eq),
        Primitive("is_equal", arrow(t0, t0, tbool), _eq),
        # `lambda` is built into the representation.
        Primitive("tail", arrow(tlist(t0), tlist(t0)), _tail),
    ]

def human_scale_primitives():
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
        Primitive("find", arrow(arrow(t0, tbool), tlist(t0), tlist(tint)), _find),
        Primitive("first", arrow(tlist(t0), t0), _first),
        Primitive("fix1", arrow(t0, arrow(arrow(t0, t1), t0, t1), t1), _fix),
        Primitive("flatten", arrow(tlist(tlist(t0)), tlist(t0)), _flatten),
        Primitive("fold", arrow(arrow(t1, t0, t1), t1, tlist(t0), t1), _fold),
        Primitive("foldi", arrow(arrow(tint, t1, t0, t1), t1, tlist(t0), t1), _foldi),
        Primitive("group", arrow(arrow(t0, t1), tlist(t1), tlist(tlist(t1))), _group),
        Primitive("if", arrow(tbool, t0, t0, t0), _if),
        Primitive("insert", arrow(t0, tint, tlist(t0), tlist(t0)), _insert),
        Primitive("is_even", arrow(tint, tbool), _is_even),
        Primitive("is_in", arrow(tlist(t0), t0, tbool), _is_in),
        Primitive("is_odd", arrow(tint, tbool), _is_odd),
        # `lambda` is built into the representation.
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
        Primitive("second", arrow(tlist(t0), t0), _second),
        Primitive("singleton", arrow(t0, tlist(t0)), _single),
        Primitive("slice", arrow(tint, tint, tlist(t0), tlist(t0)), _slice),
        Primitive("sort", arrow(arrow(t0, tint), tlist(t0), tlist(t0)), _sort),
        Primitive("splice", arrow(tlist(t0), tint, tlist(t0), tlist(t0)), _splice),
        Primitive("sum", arrow(tlist(tint), tint), sum),
        Primitive("swap", arrow(tint, tint, tlist(t0), tlist(t0)), _swap),
        Primitive("take", arrow(tint, tlist(t0), tlist(t0)), _take),
        Primitive("takelast", arrow(tint, tlist(t0), tlist(t0)), _takelast),
        Primitive("third", arrow(tlist(t0), t0), _third),
        Primitive("true", tbool, True),
        Primitive("unique", arrow(tlist(t0), tlist(t0)), _unique),
        Primitive("zip", arrow(tlist(t0), tlist(t0), tlist(tlist(t0))), _zip),
    ]

def flip(p=0.5):
    return random.random() < p

def categorical_entropy(ws):
    z = sum(ws)
    return -sum(w/z*math.log2(w/z) for w in ws if w > 0)

def make_grammar(g):
    Primitive.GLOBALS.clear()
    return Grammar.uniform(g())

def list_primitives():
    print("Primitives:")
    for primitive in Primitive.GLOBALS:
        print(f"- {primitive}")

def sample_programs(g, type_of_sample, n=10, **kwargs):
    return [grammar.sample(type_of_sample, **kwargs) for _ in range(n)]

def sample_element(max_num):
    if max_num >= 9 and flip(0.5):
        return random.randint(0, 9)
    return random.randint(0, max_num)

def sample_input(max_num, l=None, r=None):
    length = random.randint(0, 10) if l is None else l
    repetitions = (random.randint(0, length-1) if r is None else r) if length > 1 else 0
    xs = set()
    while len(xs) < length-repetitions:
        xs.add(sample_element(max_num))
    xs = list(xs)
    xs.extend([random.choice(xs) for _ in range(repetitions)])
    random.shuffle(xs)
    return xs

def evaluate_on_input(p, i):
    return p.runWithArguments([i])

def valid_output(xs, max_num):
    return len(xs) == 0 or (len(xs) <= 15 and max(xs) < (max_num + 1))

def parse_program(expression):
    return Program.parse(expression)

# If you need to create types:
# 'tbool' = bool
# 'tint' = int
# 't0', 't1', 't2' = universally quantified type variables
# 'arrow(x, y)` = x -> y, i.e. function from x to y
# 'tlist(x)' = [x], i.e. a list of xs
#
# Example: [t0] -> (t0 -> int) -> (int -> bool) -> [bool]
# tp = arrow(tlist(t0), arrow(t0, tint), arrow(tint, tbool), tlist(tbool))

def check_type(p, tp):
    return p.canHaveType(tp)

def infer_type(p):
    return p.infer()

def usage():
    return (
        "python bin/list-routines.py <grammar> <expression> <input>\n"
        "    <grammar>: 'model-comparison-9', 'model-comparison-99', or 'human-scale'\n"
        "    <expression>: an expression in the grammar\n"
        "    <input>: a bracketed list of numbers\n"
        "\n"
        "Parses <expression> under <grammar> and prints the result of running the parsed program on <input>.\n"
        "\n"
        "Example:\n"
        "$ python bin/list-routines.py model-comparison-9 \"(lambda (cons (head \$0) empty))\" \"[1,2,3,4]\"\n"
        "[1]\n"
        "\n"
        "Note escaped \"\$\" to avoid bash string interpolation."
    )

if __name__ == "__main__":
    grammars = {
        "model-comparison-9": model_comparison_primitives_9,
        "model-comparison-99": model_comparison_primitives_99,
        "human-scale": human_scale_primitives,
    }
    if len(sys.argv) != 4:
        print(usage())
    else:
        try:
            grammar = make_grammar(grammars[sys.argv[1]])
        except KeyError:
            exit(usage())
        program = parse_program(sys.argv[2])
        inp = [int(x) for x in sys.argv[3].strip()[1:-1].split(',')]
        print(evaluate_on_input(program, inp))
