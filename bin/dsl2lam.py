try:
    import binutil  # required to import from dreamcoder modules
except ModuleNotFoundError:
    import bin.binutil  # alt import if called as module
from dreamcoder.utilities import parseSExpression as parse
from dreamcoder.program import Abstraction, Index, Application

# classes Appl, Abstr, Index modified from the parent class to implement:
#  * normal order reduction
#  * len(). the straightforward approach runs into recursion depth limit, so
#    we use generators and compute the sum only at the top level len()

class Appl(Application):

    def __init__(self, f, x):
        super().__init__(f, x)
        self.reduced = None

    def len_gen(self):
        # '(' + len(f) + len(x) +')'
        yield 2
        yield from self.f.len_gen()
        yield from self.x.len_gen()

    def __len__(self):
        return sum(self.len_gen())

    def shift(self, offset, depth=0):
        return Appl(self.f.shift(offset, depth),
                    self.x.shift(offset, depth))


    def substitute(self, old, new):
        if self == old:
            return new
        return Appl(
            self.f.substitute(
                old, new), self.x.substitute(
                old, new))

    def betaReduce(self):
        if self.reduced is not None:
            return self.reduced

        if self.f.isAbstraction:
            b = self.f.body
            v = self.x
            self.reduced = b.substitute(Index(0), v.shift(1)).shift(-1)
            return self.reduced

        f = self.f.betaReduce()
        if f is not None:
            self.reduced = Appl(f, self.x)
            return self.reduced

        x = self.x.betaReduce()
        if x is not None:
            self.reduced = Appl(self.f, x)
            return self.reduced

        return None

class Abstr(Abstraction):

    def __init__(self, body):
        super().__init__(body)
        self.reduced = None

    def len_gen(self):
        # '(' + 'λ' + len(body) + ')'
        yield 3
        yield from self.body.len_gen()

    def __len__(self):
        return sum(self.len_gen())

    def shift(self, offset, depth=0):
        return Abstr(self.body.shift(offset, depth + 1))

    def substitute(self, old, new):
        if self == old:
            return new
        old = old.shift(1)
        new = new.shift(1)
        return Abstr(self.body.substitute(old, new))

    def betaReduce(self):
        if self.reduced is not None: return self.reduced
        b = self.body.betaReduce()
        if b is None: return None
        self.reduced = Abstr(b)
        return self.reduced

def index_len_gen(self):
    yield 1
Index.len_gen = index_len_gen
Index.__len__ = lambda _: 1


class Min:
    '''Keeps track of the value with minimum key seen so far.'''

    def __init__(self, key=None, val=None):
        self.key, self.val = key, val

    def update(self, newkey, newval):
        if self.key is None or newkey < self.key:
            self.key, self.val = newkey, newval


def _encode_num(m, f, x):
    enc = x
    while m > 0:
        enc = Appl(f, enc)
        m -= 1
    return enc
def encode_num(m):
    '''Return Church encoding of m.'''
    return Abstr(Abstr(_encode_num(m, Index(1), Index(0))))


encoding = {}

def translate(expr):
    '''Translates a left-associated list representing an S-expression into a
    lambda calculus term.'''

    if type(expr) is str:
        if expr in encoding:
            return encoding[expr]
        elif expr.startswith('$'):
            return Index(int(expr[1:]))
        elif expr.isdecimal():
            return encode_num(int(expr))
        else:
            raise NameError('unknown primitive ' + expr)
    else:
        if expr[0] == 'lambda':
            return Abstr(translate(expr[1]))
        else:
            return Appl(translate(expr[0]), translate(expr[1]))

def left_associate(expr):
    '''Left-associates a nested list representing an S-expression.'''
    if type(expr) is not list:
        return expr
    elif len(expr) == 2:
        return [left_associate(expr[0]), left_associate(expr[1])]
    else:
        return [left_associate(expr[:-1]), left_associate(expr[-1])]

def make_program(expr):
    return translate(left_associate(parse(expr)))

def beta_normal_form(term, keepmin=False, maxreds=None):
    '''Repeatedly beta-reduces a term, optionally keeping track of the shortest
    intermediate reduced form of the term, optionally capping the number of
    reductions.'''
    t = term
    minform = Min()
    i = 0
    while (term is not None) and ((maxreds is None) or (i < maxreds)):
        t = term
        if keepmin: minform.update(len(term), term)
        term = term.betaReduce()
        i += 1
    return t, minform


# primitives that start with _ are not used in HL, and are only used here as
# components of more complex primitives
primitives = {
    # booleans
    'true':     '(lambda (lambda $1))',
    'false':    '(lambda (lambda $0))',
    'not':      '(lambda (lambda (lambda ($2 $0 $1))))',
    'if':       '(lambda (lambda (lambda ($2 $1 $0))))',
    'and':      '(lambda (lambda ($1 $0 $1)))',
    'or':       '(lambda (lambda ($1 $1 $0)))',

    # positive integer arithmetic
    '_pred':    '(lambda (lambda (lambda ($2 (lambda (lambda ($0 ($1 $3)))) (lambda $1) (lambda $0)))))',
    '+':        '(lambda (lambda (lambda (lambda ($3 $1 ($2 $1 $0))))))',
    '-':        '(lambda (lambda ($0 _pred $1)))',
    '*':        '(lambda (lambda (lambda ($2 ($1 $0)))))',

    '_Y':       '(lambda ((lambda ($1 ($0 $0))) (lambda ($1 ($0 $0)))))',
    '_iszero':  '(lambda ($0 (lambda false) true))',

    # division taken from the Wikipedia page
    '_div':     '(lambda (lambda (lambda (lambda (lambda ((lambda (_iszero $0 $1 ($2 ($5 $0 $3 $2 $1)))) (- $3 $2)))))))',
    '/':        '(lambda (_Y _div (lambda (lambda ($1 ($2 $1 $0))))))',

    '_<=':      '(lambda (lambda (_iszero (- $1 $0))))',
    '_>=':      '(lambda (lambda (_iszero (- $0 $1))))',
    '<':        '(lambda (lambda (not (_>= $1 $0))))',
    '>':        '(lambda (lambda (not (_<= $1 $0))))',
    '==':       '(lambda (lambda (and (_>= $1 $0) (_<= $1 $0))))',
    '_<=>':     '(lambda (lambda (lambda (and (_<= $2 $0) (_>= $1 $0)))))',

    '%':        '(_Y (lambda (lambda (lambda ((< $1 $0) $1 ($2 (- $1 $0) $0))))))',
    'is_even':  '(lambda (_iszero (% $0 2)))',
    'is_odd':   '(lambda (not (is_even $0)))',

    # lists
    # Scott-encoded for ease of pattern-matching recursion
    '[]':       '(lambda (lambda $1))',
    'empty':    '[]',
    'cons':     '(lambda (lambda (lambda (lambda ($0 $3 $2)))))',
    'singleton':  '(lambda (cons $0 []))',

    # foldr is useful for other primitives but concepts use foldl
    '_foldr':   '(_Y (lambda (lambda (lambda (lambda '
                    '($0 $1 (lambda (lambda ($4 ($5 $4 $3 $0) $1)))))))))',
    'fold':     '(_Y (lambda (lambda (lambda (lambda '
                    '($0 $1 (lambda (lambda ($5 $4 ($4 $3 $1) $0)))))))))',
    'map':      '(lambda (_foldr (lambda (lambda (cons ($2 $0) $1))) []))',
    'filter':   '(lambda (_foldr (lambda (lambda (($2 $0) (cons $0 $1) $1))) []))',
    'zip':      '(_Y (lambda (lambda (lambda ($1 [] (lambda (lambda ($2 [] '
                    '(lambda (lambda (cons (cons $3 (cons $1 [])) ($6 $2 $0))))))))))))',

    'first':    '(lambda ($0 false (lambda (lambda $1))))',
    '_tail':    '(lambda ($0 [] (lambda (lambda $0))))',
    'nth':      '(_Y (lambda (lambda (lambda ((== $1 1) (first $0) ($2 (_pred $1) (_tail $0)))))))',
    'second':   '(nth 2)',
    'third':    '(nth 3)',
    'length':   '(_foldr (lambda (lambda (+ 1 $1))) 0)',
    'last':     '(lambda (nth (length $0) $0))',

    'concat':   '(lambda (lambda (_foldr (lambda (lambda (cons $0 $1))) $0 $1)))',
    'append':   '(lambda (lambda (concat $1 (singleton $0))))',
    'count':    '(lambda (lambda (length (filter (== $1) $0))))',
    'cut_vals': '(lambda (filter (lambda (not (== $1 $0)))))',
    'is_in':    '(lambda (lambda (not (_iszero (count $0 $1)))))',
    'flatten':  '(_foldr (lambda (lambda (concat $0 $1))) [])',
    '_summary': '(lambda (lambda (lambda (_foldr (lambda (lambda ($3 ($4 $0) ($4 $1) $0 $1))) (first $0) $0))))',
    'max':      '(_summary (lambda $0) >)',
    'min':      '(_summary (lambda $0) <)',
    'product':  '(_foldr * 1)',
    'reverse':  '(fold (lambda (lambda (cons $0 $1))) [])',
    'sum':      '(_foldr + 0)',
    'unique':   '(lambda (reverse (fold (lambda (lambda (is_in $1 $0 $1 (cons $0 $1)))) [] $0)))',

    'range':    '(_Y (lambda (lambda (lambda (lambda ((< $0 $2) [] (cons $2 ($3 (+ $2 $1) $1 $0))))))))',
    'repeat':   '(lambda (lambda (map (lambda $2) (range 1 1 $0))))',

    # zips a list with the list [1, 2, ..., len]. used in most primitives that
    # have anything to do with indices
    '_zipi':    '(lambda (zip (range 1 1 (length $0)) $0))',

    '_foldri':  '(lambda (lambda (lambda (_foldr (lambda (lambda ($4 (first $0) $1 (second $0)))) $1 (_zipi $0)))))',
    'foldi':    '(lambda (lambda (lambda (fold (lambda (lambda ($4 (first $0) $1 (second $0)))) $1 (_zipi $0)))))',
    'mapi':     '(lambda (lambda (map (lambda ($2 (first $0) (second $0))) (_zipi $0))))',
    'filteri':  '(lambda (lambda (map second (filter (lambda ($2 (first $0) (second $0))) (_zipi $0)))))',

    'insert':   '(lambda (lambda (_foldri (lambda (lambda (lambda (== $2 $3 (cons $4 (cons $0 $1)) (cons $0 $1))))) [])))',
    'replace':  '(lambda (lambda (_foldri (lambda (lambda (lambda (== $2 $4 (cons $3 $1) (cons $0 $1))))) [])))',
    'cut_idx':  '(lambda (_foldri (lambda (lambda (lambda (== $2 $3 $1 (cons $0 $1))))) []))',
    'swap':     '(lambda (lambda (lambda (_foldri (lambda (lambda (lambda'
                    '(== $2 $5 (cons (nth $4 $3) $1) (== $2 $4 (cons (nth $5 $3) $1) (cons $0 $1)))))) [] $0))))',
    'cut_slice': '(lambda (lambda (_foldri (lambda (lambda (lambda (_<=> $4 $3 $2 $1 (cons $0 $1))))) [])))',
    'slice':    '(lambda (lambda (_foldri (lambda (lambda (lambda (_<=> $4 $3 $2 (cons $0 $1) $1)))) [])))',
    'drop':     '(lambda (filteri (lambda (lambda (> $1 $2)))))',
    'take':     '(lambda (filteri (lambda (lambda (_<= $1 $2)))))',
    'droplast': '(lambda (lambda (take (- (length $0) $1) $0)))',
    'takelast': '(lambda (lambda (drop (- (length $0) $1) $0)))',
    'splice':   '(lambda (lambda (lambda (concat (concat (take (_pred $1) $0) $2) (drop (_pred $1) $0)))))',

    'find':     '(lambda (_foldri (lambda (lambda (lambda ($3 $0 (cons $2 $1) $1)))) []))',
    'cut_val':  '(lambda (lambda (cut_idx (first (find (== $1) $0)) $0)))',

    'group':    '(lambda (lambda (map (lambda (filter (lambda (== $1 ($3 $0))) $1)) (unique (map $1 $0)))))',

    '_isnil':   '(lambda ($0 true (lambda (lambda false))))',
    'sort':     '(_Y (lambda (lambda (lambda (_isnil $0 []'
                    '((lambda (concat (repeat $0 (count $0 $1)) ($3 $2 (cut_vals $0 $1)))) (_summary $1 < $0)))))))'
}

for prim in primitives:
    encoding[prim] = make_program(primitives[prim])

alt_defns = {
    '_Y': [
        '(lambda ((lambda ($0 $0)) (lambda ($1 ($0 $0)))))',
        '((lambda (lambda ($1 $0 $1))) (lambda (lambda ($1 ($0 $1 $0)))))',
        '((lambda (lambda ($0 ($1 $1 $0)))) (lambda (lambda ($0 ($1 $1 $0)))))',
        '((lambda ($0 $0)) (lambda (lambda ($0 ($1 $1 $0)))))'
    ],

    '==': ['(_Y (lambda (lambda (lambda (_iszero $1 (_iszero $0 true false) (_iszero $0 false '
        '($2 (_pred $1) (_pred $0))))))))'],

    'is_odd': ['(lambda (is_even (+ 1 $0)))'],

    'second': ['(lambda (first (_tail $0)))'],
    'third': ['(lambda (first (_tail (_tail $0))))'],
    'nth': ['(lambda (lambda (first ((_pred $1) _tail $0))))'],
    'repeat': [
        '(_Y (lambda (lambda (lambda (_iszero $0 [] (cons $1 ($2 $1 (_pred $0))))))))',
        '(lambda (lambda ($0 (cons $1) [])))'
    ],

    #'map':      ['(lambda (fold (lambda (lambda (append $1 ($2 $0)))) []))'],
    #'filter':   ['(lambda (fold (lambda (lambda (($2 $0) (append $1 $0) $1))) []))'],
    #'length':   ['(fold (lambda (lambda (+ 1 $1))) 0)'],
    #'flatten':  ['(fold (lambda (lambda (concat $1 $0))) [])'],
    #'_summary': ['(lambda (lambda (lambda (fold (lambda (lambda ($3 ($4 $0) ($4 $1) $0 $1))) (first $0) $0))))'],
    #'product':  ['(fold * 1)'],
    #'reverse':  ['(_foldr (lambda (lambda (append $1 $0))) [])'],
    #'sum':      ['(fold + 0)'],
    #'unique':   ['(lambda (fold (lambda (lambda (is_in $1 $0 $1 (append $1 $0)))) [] $0))'],

    '_<=': [
        '(lambda (lambda (_iszero (- $1 $0))))',
        '(lambda (lambda (_>= $0 $1)))',
        '(lambda (lambda (< $1 (+1 $0))))',
        '(lambda (lambda (> (+1 $0) $1)))',
        '(lambda (lambda (not (< $0 $1))))',
        '(lambda (lambda (not (> $1 $0))))'
    ],
    '_>=': [
        '(lambda (lambda (_iszero (- $0 $1))))',
        '(lambda (lambda (_<= $0 $1)))',
        '(lambda (lambda (> $1 (+1 $0))))',
        '(lambda (lambda (< (+1 $0) $1)))',
        '(lambda (lambda (not (< $1 $0))))',
        '(lambda (lambda (not (> $0 $1))))'
    ],
    '<': [
        '(lambda (lambda (_iszero (- (+ 1 $1) $0))))',
        '(lambda (lambda (_<= (+ 1 $1) $0)))',
        '(lambda (lambda (_>= $0 (+ 1 $1))))',
        '(lambda (lambda (not (_<= $0 $1))))',
        '(lambda (lambda (not (_>= $1 $0))))',
        '(lambda (lambda (> $0 $1)))'
    ],
    '>': [
        '(lambda (lambda (_iszero (- (+ 1 $0) $1))))',
        '(lambda (lambda (_>= (+ 1 $1) $0)))',
        '(lambda (lambda (_<= $0 (+ 1 $1))))',
        '(lambda (lambda (not (_>= $0 $1))))',
        '(lambda (lambda (not (_<= $1 $0))))',
        '(lambda (lambda (< $0 $1)))'
    ],

    'insert': [
        '(lambda (lambda (lambda (concat (concat (take (_pred $1) $0) (singleton $2)) (drop (_pred $1) $0)))))',
        '(lambda (lambda (lambda (concat (append (take (_pred $1) $0) $2) (drop (_pred $1) $0)))))',
        '(lambda (lambda (lambda (concat (take (_pred $1) $0) (cons $2 (drop (_pred $1) $0))))))'
    ],
    'replace': [
        '(lambda (lambda (lambda (concat (concat (take (_pred $2) $0) (singleton $1)) (drop $2 $0)))))',
        '(lambda (lambda (lambda (concat (append (take (_pred $2) $0) $1) (drop $2 $0)))))',
        '(lambda (lambda (lambda (concat (take (_pred $2) $0) (cons $1 (drop $2 $0))))))'
    ],
    'cut_idx': ['(lambda (lambda (concat (take (_pred $1) $0) (drop $1 $0))))'],
    'swap': [
        '(lambda (lambda (lambda (concat (concat (concat (concat '
            '(take (_pred $2) $0) (singleton (nth $1 $0))) (drop $2 (take (_pred $1) $0))) (singleton (nth $2 $0))) (drop $1 $0)))))',
        '(lambda (lambda (lambda (concat (append (concat (append '
            '(take (_pred $2) $0) (nth $1 $0)) (drop $2 (take (_pred $1) $0))) (nth $2 $0)) (drop $1 $0)))))',
        '(lambda (lambda (lambda (concat (concat '
            '(take (_pred $2) $0) (cons (nth $1 $0) (drop $2 (take (_pred $1) $0)))) (cons (nth $2 $0) (drop $1 $0))))))'
    ],
    'cut_slice': ['(lambda (lambda (lambda (concat (take (_pred $2) $0) (drop $1 $0)))))'],
    'slice': ['(lambda (lambda (lambda (drop (_pred $2) (take $1 $0)))))'],
    'drop': [
        '(lambda (lambda ($1 _tail $0)))',
        '(_Y (lambda (lambda (lambda (_iszero $1 $0 ($2 (_pred $1) (_tail $0)))))))'
    ],
    'take': ['(_Y (lambda (lambda (lambda (_iszero $1 [] (cons (first $0) ($2 (_pred $1) (_tail $0))))))))'],
    'droplast': ['(_Y (lambda (lambda (lambda (== (length $0) $1 [] (cons (first $0) ($2 (+ 1 $1) (_tail $0))))))))'],
    'takelast': ['(lambda (lambda ((- (length $0) $1) _tail $0)))'],

    'cut_val': ['(lambda (lambda (second (fold (lambda (lambda '
        '((first $1) (cons true (singleton (append (second $1) $0))) '
        '(== $3 $0 (cons true (singleton (second $1))) (cons false (singleton (append (second $1) $0))))))) '
        '(cons false (singleton [])) $0))))']
}
