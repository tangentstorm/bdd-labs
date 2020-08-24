# coding: utf-8
"""
Test cases for the bdd base.
"""
from bdd import o, l, NOT, AND, XOR, CH, MAJ, Base
import unittest

class BDDTest(unittest.TestCase):

    def setUp(self):
        self.base = Base()

    def test_base(self):
        # there should be one node at first:
        # o, which represents false. (think 'zero')
        # (true, or 'l', is just ~o)
        self.assertEquals(1, self.base.count)
        self.assertEquals(o, self.base[0])
        self.assertEquals(l, self.base[~0])

    def test_vars(self):
        a, b = self.base.vars('a','b')
        self.assertEquals(3, self.base.count)
        self.assertEquals(a, self.base[1])
        self.assertEquals(b, self.base[2])
        self.assertEquals(o, a.lo); self.assertEquals(o, b.lo)
        self.assertEquals(l, a.hi); self.assertEquals(l, b.hi)
        self.assertEquals(1, a.nid)

    def test_not(self):
        a = self.base.var('a'); na = ~a
        self.assertEquals(~(a.nid), na.nid)
        self.assertEquals(na, self.base[~(a.nid)])
        self.assertEquals(l, na.lo)
        self.assertEquals(o, na.hi)
        self.assertTrue(a is ~na)

    def test_cmp_not(self):
        a, b = self.base.vars('a', 'b')
        assert  a <  o  # because o goes on the bottom
        assert  a <  l  # because l goes on the bottom
        assert  a <  b
        assert  a < ~b
        assert ~a <  b
        assert ~a < ~b

    def test_consts(self):
        a = self.base.var('a')
        self.assertEquals(o, self.base[o].whenHi(a.nid), 'o=o when a is hi')
        self.assertEquals(o, self.base[o].whenLo(a.nid), 'o=o when a is lo')
        self.assertEquals(l, self.base[l].whenHi(a.nid), 'l=l when a is hi')
        self.assertEquals(l, self.base[l].whenLo(a.nid), 'l=l when a is lo')

    def test_whenHiLo(self):
        a = self.base.var('a'); na = ~a
        b = self.base.var('b'); nb = ~b
        self.assertEquals(l, a.whenHi(a.nid), 'l=a when a is hi')
        self.assertEquals(o, a.whenLo(a.nid), 'o=a when a is lo')
        self.assertEquals(b, b.whenHi(a.nid), 'b=b when a is hi')
        self.assertEquals(b, b.whenLo(a.nid), 'b=b when a is lo')

        self.assertEquals(a, a.whenHi(b.nid), 'a=a when b is hi')
        self.assertEquals(a, a.whenLo(b.nid), 'a=a when b is lo')
        self.assertEquals(l, b.whenHi(b.nid), 'l=b when b is hi')
        self.assertEquals(o, b.whenLo(b.nid), 'o=b when b is lo')

    def test_and(self):
        a, b = self.base.vars('a','b')
        f = a & b; g = b & a
        self.assertEqual(f, g, 'a∧b = b∧a')

        fn = self.base[f]
        self.assertEqual(fn.var, a, 'a goes on top because 1 < 2')
        self.assertEqual(fn.whenHi(a), b,  ' a →  (a∧b) = b')
        self.assertEqual(fn.whenLo(a), o,  '¬a →  (a∧b) = ⊥')
        self.assertEqual(fn.whenHi(b), a,  ' b →  (a∧b) = a')
        self.assertEqual(fn.whenLo(b), o,  '¬b →  (a∧b) = ⊥')
        self.assertEqual((~fn).whenHi(a), ~b, ' a → ¬(a∧b) = ¬b')
        self.assertEqual((~fn).whenLo(a), l,  '¬a → ¬(a∧b) = ⊤')
        self.assertEqual((~fn).whenHi(b), ~a, ' b → ¬(a∧b) = ¬a')
        self.assertEqual((~fn).whenLo(b), l,  '¬b → ¬(a∧b) = ⊤')

    def test_and_simple(self):
        a = self.base.var('a')
        self.assertEqual(a, a&a)
        self.assertEqual(o, a&~a)

    def test_or(self):
        a, b = self.base.vars('a','b')
        fn = self.base[a|b]
        self.assertEqual(fn.whenHi(a), l,  ' a →  (a∨b) = ⊤')
        self.assertEqual(fn.whenLo(a), b,  '¬a →  (a∨b) = b')
        self.assertEqual(fn.whenHi(b), l,  ' b →  (a∨b) = ⊤')
        self.assertEqual(fn.whenLo(b), a,  '¬b →  (a∨b) = a')

    def test_xor_norm(self):
        a, b = self.base.vars('a','b')
        self.assertEqual((a,b,~b), (a.nid, b.nid, ~b.nid))
        self.assertEqual((a,b,~b), self.base.ite_norm(a.nid, b.nid, ~b.nid))

    def test_xor(self):
        a, b = self.base.vars('a','b')
        f = a ^ b; g = b ^ a
        self.assertEqual(f, g, 'a≠b = b≠a')

        fn = self.base[f]
        self.assertEqual(fn.hi, ~b)
        self.assertEqual(fn.lo, b)

        self.assertEqual(fn.var, a, 'a goes on top because 1 < 2')
        self.assertEqual(fn.whenHi(a), ~b, ' a →  (a≠b) = ¬b')
        self.assertEqual(fn.whenLo(a), b,  '¬a →  (a≠b) =  b')
        self.assertEqual(fn.whenHi(b), ~a, ' b →  (a≠b) = ¬a')
        self.assertEqual(fn.whenLo(b), a,  '¬b →  (a≠b) =  a')
        self.assertEqual((~fn).whenHi(a),  b, ' a → ¬(a≠b) =  b')
        self.assertEqual((~fn).whenLo(a), ~b, '¬a → ¬(a≠b) = ¬b')
        self.assertEqual((~fn).whenHi(b),  a, ' b → ¬(a≠b) =  a')
        self.assertEqual((~fn).whenLo(b), ~a, '¬b → ¬(a≠b) = ¬a')

    def test_xor_simple(self):
        a = self.base.var('a')
        self.assertEqual(o, a ^  a)
        self.assertEqual(l, a ^ ~a)

    def test_xor_nots(self):
        a, b = self.base.vars('a','b')
        f = (~a) ^ b

        fn = self.base[f]
        self.assertEqual(fn.lo, ~b)
        self.assertEqual(fn.hi, b)

        self.assertEqual(fn.var, a.nid, 'a goes on top because 1 < 2')
        self.assertEqual(fn.whenHi(a),  b,  ' a →  (¬a≠b) =   b')
        self.assertEqual(fn.whenLo(a), ~b,  '¬a →  (¬a≠b) =  ¬b')
        self.assertEqual(fn.whenHi(b),  a,  '¬b →  (¬a≠b) =   a')
        self.assertEqual(fn.whenLo(b), ~a,  '¬b →  (¬a≠b) =  ¬a')

        self.assertEqual((~fn).whenHi(a), ~b, ' a → ¬(¬a≠b) = ¬b')
        self.assertEqual((~fn).whenLo(a),  b, ' a → ¬(¬a≠b) =  b')
        self.assertEqual((~fn).whenHi(b), ~a, '¬b → ¬(¬a≠b) = ¬a')
        self.assertEqual((~fn).whenLo(b),  a, ' b → ¬(¬a≠b) =  a')

    def test_nor(self):
        """regression test for max recursion error"""
        a, b = self.base.vars('a', 'b')
        nor = (~a & ~b)

    def test_adder(self):
        a0, b0, a1, b1, a2, b2 = self.base.vars('a0','b0','a1','b1','a2','b2')
        a = [a0, a1]#, a2]
        b = [b0, b1]#, b2]

        # result and carry bits:
        r = [self.base[x ^ y] for (x, y) in zip(a, b)]
        c = [self.base[x ^ y] for (x, y) in zip(a, b)]

        c.pop(0); c.append(self.base[0])  # << 1
        t = r                             # temp copy of result
        r = [self.base[x ^ y] for (x, y) in zip(t, c)]

        # this step was causing a maximum recursion depth error
        # (it was a specific case of the 'nor' error)
        c = [self.base[x & y] for (x, y) in zip(t, c)]

    def test_maj(self):
        """majority function"""
        a,b,c = self.base.vars('a','b','c')
        f = self.base[a.maj(b,c)]
        self.assertEquals((b&c), f.whenLo(a))
        self.assertEquals((a&c), f.whenLo(b))
        self.assertEquals((a&b), f.whenLo(c))

        self.assertEquals((b|c), f.whenHi(a))
        self.assertEquals((a|c), f.whenHi(b))
        self.assertEquals((a|b), f.whenHi(c))

    def test_depth(self):
        a, b = self.base.vars('a', 'b')
        self.assertEqual(0, self.base[o].depth)
        self.assertEqual(0, self.base[l].depth)
        self.assertEqual(1, a.depth)
        self.assertEqual(1, b.depth)
        self.assertEqual(2, self.base[a&b].depth)
        self.assertEqual(2, self.base[a&b].depth)


    def test_whenIs(self):
        sb = lambda x: self.base[x]
        a,b,c,d,e = self.base.vars('a','b','c','d','e')
        abc = sb(a.maj(b,c))
        cde = sb(c.maj(d,e))

        fn0 = sb(c.maj(abc,e))
        fn1 = sb(cde.whenIs(d, abc))
        self.assertEqual(fn0, fn1)

    def test_when(self):
        sb = lambda x: self.base[x]
        a,b,c,x,y,z = self.base.vars('a','b','c','x','y','z')
        abc = sb(a.maj(b,c))
        xyz = sb(x.maj(y,z))

        tmp = sb(xyz.whenIs(x,a))
        tmp = sb(tmp.whenIs(y,b))
        tmp = sb(tmp.whenIs(z,c))
        self.assertEqual(tmp, abc)

        fn0 = sb(xyz.when({x:c, y:b, z:a}))
        self.assertEqual(fn0, abc)

        # make sure we can substitute even with the variables we're already using
        fn1 = sb(abc.when({a:c, b:a, c:b}))
        self.assertEqual(fn1, abc)

if __name__ == "__main__":
    unittest.main()
