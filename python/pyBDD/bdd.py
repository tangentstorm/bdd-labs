# coding=utf-8
"""
bdd = binary decision diagram.
This module defines a bdd 'base' for the reduced, ordered variety.
"""
o,l = 0,-1
VAR, NOT, AND, XOR, CH, MAJ = 'vnaxcm'

def pos(x): return x if x>0 else ~x

class BDD(object):

    def __and__(self, other):
        return self.base.ite(self.nid, other.nid, 0)

    def __xor__(self, other):
        return self.base.ite(self.nid, ~other.nid, other.nid)

    def __or__(self, other):
        return self.base.ite(self.nid, l, other.nid)

    def ch(self, x, y):
        return self.base.ite(self.nid, x.nid, y.nid)

    def as_ite(self):
        return (self.var, self.hi, self.lo)

    def maj(self, x, y):
        return self.base.ite(self.nid,
                             self.base.ite(x.nid, l, y.nid),
                             self.base.ite(x.nid, y.nid, o))


class Not(BDD):

    def __init__(self, what):
        self.what = what

    def __cmp__(self, other):
        if type(other)==int: return cmp(self.what, other)
        elif isinstance(other, Not): return cmp(self.what, other.what)
        else: return cmp(self.what, other)

    def __invert__(self):
        return self.what

    def __repr__(self):
        return "~%r" % self.what

    @property
    def base(self):
        return self.what.base

    @property
    def lo(self):
        return ~self.what.lo

    @property
    def hi(self):
        return ~self.what.hi

    @property
    def nid(self):
        return ~self.what.nid

    @property
    def var(self):
        return pos(self.what.var)

    @property
    def depth(self):
        return self.what.depth

    def whenLo(self, x):
        return ~(self.what.whenLo(x))

    def whenHi(self, x):
        return ~(self.what.whenHi(x))

    def whenIs(self, v, n):
        return ~(self.what.whenIs(v,n))

    def when(self, kv):
        return ~(self.what.when(kv))

class Node(BDD):

    def __init__(self, base, depth, nid, var, hi, lo):
        self.base = base
        self.depth = depth
        self.nid = nid; assert type(nid)==int and nid >= 0
        self.var = var; assert type(var)==int
        self.hi = hi
        self.lo = lo

    def __repr__(self):
        return 'N%s(%s ? %s : %s)' % (self.nid, self.var, self.hi, self.lo)

    def __invert__(self):
        return Not(self)

    def __eq__(self, other):
        if type(other) == int: return self.nid == other
        elif type(other) == Not: return False
        else: return all(getattr(self,k)==getattr(other,k)
                         for k in ['nid','var','lo','hi'])

    def __cmp__(self, other):
        if type(other)==int: other = self.base[other]
        if isinstance(other, Not): other = other.what
        assert isinstance(other, Node), 'cmp(%s, %s)' % (self, other)
        sv, ov = pos(self.var), pos(other.var)
        if sv == 0: return cmp(ov, 0)
        if ov == 0: return -1
        return cmp(sv, ov) or cmp(pos(self.nid), pos(other.nid))


    def whenHi(self, v):
        """vnid -> nid"""
        if self.var == l or v < self.var: return self.nid
        elif v == self.var: return self.hi
        elif v > self.var:
            base = self.base
            return base.ite(self.var, base[self.hi].whenHi(v), base[self.lo].whenHi(v))
        else: raise 'inconceivable.'

    def whenLo(self, v):
        """vnid -> nid"""
        if self.var == l or v < self.var: return self.nid
        elif v == self.var: return self.lo
        elif v > self.var:
            base = self.base
            return base.ite(self.var, base[self.hi].whenLo(v), base[self.lo].whenLo(v))
        else: raise 'inconceivable.'

    def whenIs(self, v, n):
        """vnid -> nid -> nid"""
        base = self.base; bdd = base[n]
        if self.var == l or v < self.var: return self.nid
        elif v == self.var:
            return base.ite(bdd, self.hi, self.lo)
        elif v > self.var:
            return base.ite(self.var, base[self.hi].whenIs(v, n), base[self.lo].whenIs(v, n))
        else: raise 'inconceivable.'

    def when(self, kv):
        """{ vnid : nid } -> nid"""
        base = self.base; vs={n.var:kv[n] for n in kv.keys()}; minv=min(vs); maxv=max(vs)
        if self.var == l or maxv < self.var: return self.nid
        elif self.var in vs:
            return base.ite(base[vs[self.var]], base[self.hi].when(kv), base[self.lo].when(kv))
        elif maxv > self.var: # but not actually in kv
            return base.ite(self.var, base[self.hi].when(kv), base[self.lo].when(kv))
        else: raise 'inconceivable'

class Base(object):
    """
    This stores a collection of related BDD nodes as giant
    list of tuples.
    """
    def __init__(self):
        self.nodes = [Node(base=self, depth=0, nid=0, var=l, hi=o, lo=o)]
        self.memos = {(l, o, o):o, (l, l, l):l}
        self._vars = {}

    @property
    def count(self):
        return len(self.nodes)

    def __getitem__(self, i):
        """nid -> Node|Not"""
        if isinstance(i, BDD): return i.nid
        return ~self.nodes[~i] if i < 0 else self.nodes[i]

    def var(self, name):
        res = self._vars.get(name, None)
        if res is None:
            var = nid = len(self.nodes)
            res = Node(base=self, depth=1, nid=nid, var=var, hi=l, lo=o)
            self.nodes.append(res)
            self.memos[(var, l, o)] = nid  # if var then l else o
            self._vars[name] = res
        return res

    def vars(self, *names):
        return [self.var(name) for name in names]

    def get_nid(self, v, hi, lo):
        memo = self.memos.get((v, hi, lo))
        if memo: return memo
        else:
            nid = len(self.nodes)
            self.memos[(v, hi, lo)] = nid
            depth = max(self[v].depth, self[hi].depth, self[lo].depth) + 1
            self.nodes.append(Node(self, depth=depth, nid=nid, var=v, hi=hi, lo=lo))
            return nid



    # -- Base methods for if/then/else lookups

    def ite_norm(self, f, g, h):
        """
        -- normalize if/then/else triples
        :: (nid, nid, nid) -> (nid|(Node,Node,Node)) | {'~':(nid|(Node,Node,Node))}
        """
        assert type(f)==type(g)==type(h)==int, 'ite expects 3 ints. got: %s' % str((f,g,h))
        # print 'ite(%s, %s, %s)' % (f,g,h)
        fgh = (f, g, h)
        if fgh == (l,  g,  h): return g
        if fgh == (o,  g,  h): return h
        if fgh == (f,  g,  g): return g
        if fgh == (f,  l,  o): return f
        if fgh == (f,  o,  l): return ~f
        if fgh == (f,  f,  o): return f
        if fgh == (f,  f,  l): return l
        if fgh == (f,  f,  h): return self.ite_norm(f, l, h)
        if fgh == (f,  g,  f): return self.ite_norm(f, g, o)
        if fgh == (f,  g, ~f): return self.ite_norm(f, g, l)
        if fgh == (f, ~f,  h): return self.ite_norm(f, o, h)

        # extract the if/then/else form:
        fn, gn, hn = [self[nid] for nid in [f, g, h]]

        # -- choose standard triple --
        if (g, h) == (l, h) and hn < fn: return self.ite_norm( h,  l,  f)  # c0
        if (g, h) == (g, o) and gn < fn: return self.ite_norm( g,  f,  o)  # c1
        if (g, h) == (g, l) and gn < fn: return self.ite_norm(~g, ~f,  l)  # c2
        if (g, h) == (o, h) and hn < fn: return self.ite_norm(~h,  o, ~f)  # c3
        if (g, h) == (g,~g) and gn < fn: return self.ite_norm( g,  f, ~f)  # c4

        # -- flip the signs to choose between four equivalent forms.
        # forms: 0: f,g,h | 1: (¬f,h,g) | 2: ¬(f,¬g,¬h) | 3: ¬(¬f,¬g,¬h)'
        # (the f and g links will always be un-negated in exactly one of them)
        if f < 0: return self.ite_norm(~f,  h,  g)
        if g < 0:
            result = self.ite_norm( f, ~g, ~h)
            return ~result if type(result) is int else {'~': result}

        # at this point, we should have a completely normalized triple.
        # if it's in the cache, return it, else return the full nodes.
        return self.memos.get((f, g, h), (fn, gn, hn))



    def ite(self, f, g, h):
        """:: (nid, nid, nid) -> nid  -- if/then/else"""
        norm = self.ite_norm(f, g, h)
        invert = type(norm) is dict
        if invert: norm = norm['~']
        result = self.ite_memo(*norm) if type(norm) == tuple else norm
        return ~result if invert else result


    def ite_memo(self, fn, gn, hn):
        """:: (Node, Node, Node) -> nid -- find or build normalized bdd tuple"""
        key = (fn.nid, gn.nid, hn.nid)
        res = self.memos.get(key)
        if res is None:
            # print key, 'not found, so build it!'
            # print 'nodes:', self.nodes
            # print 'memos:', self.memos
            v = min([v for v in [fn.var, gn.var, hn.var] if v > 0])
            # print "v:", v, 'f[v]:', fn.whenHi(v), 'g[v]:', gn.whenHi(v), 'h[v]:', hn.whenHi(v)
            th = self.ite(fn.whenHi(v), gn.whenHi(v), hn.whenHi(v))
            el = self.ite(fn.whenLo(v), gn.whenLo(v), hn.whenLo(v))
            res = th if th == el else self.get_nid(v, th, el)
            self.memos[key] = res
        return res
