from dreamcoder.program import *


"""NOTE: in lambda calculus represented as sequence from left to right, e.g., (lambda (l 2 (C (d 1 $0))) means
go left 2, then circle then down 1. This is represented as a binary tree starting from top-left to bottom right.
To evaluate, does something like: apply l2 to initial hand state. this outputs a function that takes in the stuff in the
parantheses to the right of l2 - i.e,., (C ( ...)). This applies the function circle to the current state, and then
outputs another function which represents something that takes in a function to apply to the new state. This 
takes in (d 1), which applies down 1 to the current state, and again outputs a function. This takes in $0, for which we
use _empty_sketch, which outputs the state itself (not another fucntion). So now we have applied l, C, d in order.
This is useful to make trees ordered, and easy to understand."""

class SketchState:
    def __init__(self, hand=(0,0), history=None, canvassize=(6,6)):
        self.history = history
        self.hand = hand
        self.canvassize = canvassize  # (w, h), centered at 0,0
    def __str__(self): return f"handpos={self.hand}"
    def __repr__(self): return str(self)
    def left(self, n):
        return SketchState(hand=(self.hand[0]-n*1, self.hand[1]), history=self.history if self.history is None else self.history + [self])
    def right(self, n):
        return SketchState(hand=(self.hand[0]+n*1, self.hand[1]), history=self.history if self.history is None else self.history + [self])
    def up(self, n):
        return SketchState(hand=(self.hand[0], self.hand[1]+n*1), history=self.history if self.history is None else self.history + [self])
    def down(self, n):
        return SketchState(hand=(self.hand[0], self.hand[1]-n*1), history=self.history if self.history is None else self.history + [self])

    def draw(self, b):
        """draws something at current pen location"""
        if self.history is None: return self
        return SketchState(hand=self.hand, history=self.history + [b])
    # def left(self, n):
    #     return SketchState(hand=(self.hand[0]-n*1, self.hand[1]), history=[self] if self.history is None else self.history + [self])
    # def right(self, n):
    #     return SketchState(hand=(self.hand[0]+n*1, self.hand[1]), history=self.history if self.history is None else self.history + [self])
    # def up(self):
    #     return SketchState(hand=(self.hand[0], self.hand[1]+1), history=self.history if self.history is None else self.history + [self])
    # def down(self):
    #     return SketchState(hand=(self.hand[0], self.hand[1]-1), history=self.history if self.history is None else self.history + [self])
    # def draw(self, b):
    #     """draws something at current pen location"""
    #     if self.history is None: return self
    #     return SketchState(hand=self.hand, history=self.history + [b])

def _empty_sketch(h): 
    """just takes in a sketch object and returns it. Is used as the last step 
    once the seqeunce is done"""
    return (h, [])

def _left(d):
    """ takes in current satte, does left to it, and outputs osmething that takes in 
    the next function to apply to the new state. if this new functino is _empty_sketch thetn this will
    output a sketch object and things will end"""
    return lambda k: lambda s: k(s.left(d))
def _right(d):
    return lambda k: lambda s: k(s.right(d))
def _up(d):
    return lambda k: lambda s: k(s.up(d))
def _down(d):
    return lambda k: lambda s: k(s.down(d))

def _simpleLoop(n):
    def f(start, body, k):
        if start >= n: return k
        return body(start)(f(start + 1, body, k))
    return lambda b: lambda k: f(0,b,k)
def _embed(body):
    def f(k):
        def g(hand):
            bodyHand, bodyActions = body(_empty_sketch)(hand)
            # Record history if we are doing that
            if hand.history is not None:
                hand = SketchState(hand=hand.hand,
                                  history=bodyHand.history)
            hand, laterActions = k(hand)
            return hand, bodyActions + laterActions
        return g
    return f

class SketchContinuation(object):
    def __init__(self, part):
        self.part = part
    def __call__(self, k):
        def f(sketch):
            thisAction = [(sketch.hand, self.part)]
            sketch = sketch.draw(thisAction[0])
            sketch, rest = k(sketch)
            return sketch, thisAction + rest
        return f

parts = {
    "C":"C",
    "L":"L"
}


tsketch = baseType("sketch")

primitives = [
Primitive(name, arrow(tsketch,tsketch), SketchContinuation(part)) for name, part in parts.items()] + [
Primitive(str(j), tint, j) for j in range(1,5)] + [
Primitive("l", arrow(tint, tsketch, tsketch), _left),
Primitive("r", arrow(tint, tsketch, tsketch), _right),
Primitive("u", arrow(tint, tsketch, tsketch), _up),
Primitive("d", arrow(tint, tsketch, tsketch), _down)]

primitives.append(Primitive("loop", arrow(tint, arrow(tint, tsketch, tsketch), tsketch, tsketch), _simpleLoop))
# primitives.append(Primitive("embed", arrow(arrow(tsketch,tsketch), tsketch, tsketch), _embed))

def parseSketch(s):
    """s is a language useful for humans to write down programs. i.e., not using lambda calcuclus.
    this converts to a dreamcoder program. Also useful to ensure that this is a real program given
    our primtiives."""
    # go from string to program object (similar to Program.parse())
    # allows to have abbrviated string

    _circle = Program.parse("C")
    _line = Program.parse("L")
    _r = Program.parse("r")
    _l = Program.parse("l")
    _u = Program.parse("u")
    _d = Program.parse("d")
 
    from sexpdata import loads, Symbol
    s = loads(s)
    def command(k, environment, continuation):
        print(k)
        print(len(k))
        if k == Symbol("C"):
            return Application(_circle, continuation)
        if k == Symbol("L"):
            return Application(_line, continuation)

        assert isinstance(k,list)
        if k[0] == Symbol("C"): return Application(Application(_circle, expression(k[1],environment)),continuation)
        if k[0] == Symbol("L"): return Application(Application(_line, expression(k[1],environment)),continuation)
        if k[0] == Symbol("r"): return Application(Application(_r, expression(k[1],environment)),continuation)
        if k[0] == Symbol("l"): return Application(Application(_l, expression(k[1],environment)),continuation)
        if k[0] == Symbol("u"): return Application(Application(_u, expression(k[1],environment)),continuation)
        if k[0] == Symbol("d"): return Application(Application(_d, expression(k[1],environment)),continuation)
        # if k[0] == Symbol("for"):
        #     v = k[1]
        #     b = expression(k[2], environment)
        #     newEnvironment = [None, v] + environment
        #     body = block(k[3:], newEnvironment, Index(0))
        #     return Application(Application(Application(_lp,b),
        #                                    Abstraction(Abstraction(body))),
        #                        continuation)
        # if k[0] == Symbol("embed"):
        #     body = block(k[1:], [None] + environment, Index(0))
        #     return Application(Application(_e,Abstraction(body)),continuation)
            
        assert False
    def expression(e, environment):
        for n, v in enumerate(environment):
            if e == v: return Index(n)

        if isinstance(e,int): return Program.parse(str(e))

        assert isinstance(e,list)
        # if e[0] == Symbol('+'): return Application(Application(_addition, expression(e[1], environment)),
        #                                            expression(e[2], environment))
        # if e[0] == Symbol('-'): return Application(Application(_subtraction, expression(e[1], environment)),
        #                                            expression(e[2], environment))
        assert False
        
    def block(b, environment, continuation):
        if len(b) == 0: return continuation
        return command(b[0], environment, block(b[1:], environment, continuation))

    try: return Abstraction(command(s, [], Index(0)))
    except: return Abstraction(block(s, [], Index(0)))


def executeSketch(p, timeout=None):
    """given a propgram object, evaluates it. the first arguemnt emptysketch is required for 
    all programs - this terminates the sequence (see above). The second argument is the state
    to start with. think of this as: stuff to the left defines a function that goes from 
    sketch to sketch, so it needs one arguemnt (a sketch)."""
    # go from program object to action sequence and plan
    try:
        return runWithTimeout(lambda : p.evaluate([])(_empty_sketch)(SketchState(history=[]))[1], 
            timeout=timeout)
    except:
        assert False


def renderPlan():
    pass
    # go from plan (e.g, ((0,0), circle)...) to rendering (pixels)

###################################
if False:
    # 1) make program from string
    p = Program.parse("")

    # 2) render that program somehow
    def renderPlan(p):
        pass

    def dSLDemo():
        DSL = {}

        bricks = Program.parse("(lambda (lambda (tower_loopM $0 (lambda (lambda (moveHand 3 (reverseHand (tower_loopM $3 (lambda (lambda (moveHand 6 (3x1 $0)))) $0))))))))")
        DSL["bricks"] = [ [bricks.runWithArguments([x,y + 4,_empty_tower,TowerState()])[1]
                           for y in range(6, 6 + 3*4, 3) ]
                          for x in [3,8] ]
        dimensionality = {}
        dimensionality["bricks"] = 2


        images = {}
        for k,v in DSL.items():
            d = dimensionality.get(k,1)
            if d == 1:
                i = montageMatrix([[renderPlan(p, pretty=True, Lego=True) for p in v]])
            elif d == 2:
                i = montageMatrix([[renderPlan(p, pretty=True, Lego=True) for p in ps] for ps in v] )
            else: assert False

            images[k] = i

        return images