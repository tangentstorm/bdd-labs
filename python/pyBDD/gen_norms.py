# encoding: utf-8
"""
This program generates the result of ite_norm for every 
possible triple taken from two constants and three variables.
It is intended to be used for comparision with other implementations.
"""
import bdd

base = bdd.Base()
a,b,c = base.vars('a','b','c')

toNid = lambda x: x if type(x) is int else x.nid
def toStr(n):
    if type(n) is int: return str(n)
    elif type(n) is dict: return "¬%s" % toStr(n['~'])
    else: return str(tuple([node.nid for node in n]))

each = map(toNid, [bdd.o, bdd.l, a, ~a, b, ~b, c, ~c])
for f in each:
    for g in each:
        for h in each:
            print (f,g,h), '→', toStr(base.ite_norm(f,g,h))
