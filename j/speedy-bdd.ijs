Note''
┌──────────────────────────────────────────────────────────────┐
│                         Speedy BDD                           │
└──────────────────────────────────────────────────────────────┘

                      a J module for
           Reduced Order Binary Decision Diagrams


Copyright © 2015 Michal J. Wallace <http://tangentstorm.com/>
Avaliable for use under the MIT/X11 License.

────────────────────────────────────────────────────────────────

Much of the structure of this module is based on:

  [EIOBP] K.Brace, R.Rudell, and R.Byrant,
  Efficient Implementation of a BDD Package
  http://www.cs.cmu.edu/~emc/15817-f08/bryant-bdd-1991.pdf

Knuth‘s writing on the subject was also quite illuminating:

  [TAOCP] Donald Knuth,
  The Art of Computer Programming, Vol 4, Fascicle 1
  Bitwise Tricks and Techniques / Binary Decision Diagrams

See also his literate programs BDD14 and BDD15 here:

  http://www-cs-faculty.stanford.edu/~uno/programs.html

(BDD15 actually deals with a related structure called a ZDD).

Knuth‘s Christmas Tree lecture on "Bayesian Trees and BDDs" covers
much of his same material and provides a very nice orientation:

  https://www.youtube.com/watch?v=axUgEAgrSB8

────────────────────────────────────────────────────────────────
)


NB. ┌──────────────────────────────────────────────────────────┐
NB. │ constructor                                              │
NB. └──────────────────────────────────────────────────────────┘
coclass 'BDD'

'o l' =: 0 _1       NB. false and true
null =: #.1,31#0

create =: monad define
  NB. usage: (nvars conew 'BDD') or just (BDD nvars)
  nvar =:  y              NB. total number of variables.
  bddvars =: 1 + i. nvar
  bvar =: 'nid of bdd for var y is just y' ] ]
  init_bdds''
  init_index''
)
BDD_z_ =: conew&'BDD'


NB. ┌──────────────────────────────────────────────────────────┐
NB. │ data tables                                              │
NB. └──────────────────────────────────────────────────────────┘

NB. ─ BDD table ────────────────────────────────────────────────
NB. Stores the (if:var,then:nid,else:nid) triples, as well as
NB. refcounts for each node. (Each column is its own variable.)
NB. ────────────────────────────────────────────────────────────
init_bdds =: verb define
  NB. IF: input var on which to branch.
  BDD_IF =: l, bddvars

  NB. TH: (IF e. bddvars) → nid of value when IF=l.
  BDD_TH =: o, nvar # l

  NB. EL: (IF e. bddvars) → nid of value when IF=o.
  BDD_EL =: o, nvar # o

  NB. RC: reference count column (for garbage collection)
  BDD_RC =: 1 #~# BDD_IF   NB. initial values are all 1
)


NB. ┌──────────────────────────────────────────────────────────┐
NB. │ unique value index                      (if,th,el) → nid │
NB. └──────────────────────────────────────────────────────────┘
NB.   To prevent duplicate nodes from appearing in the BDD, we
NB. will use a rank 3 sparse array to remember the nid of each
NB. (if,th,el) triple that we add:
init_index =: verb define
  BDD_INDEX =: 1 $. ((nvar+1), 2 # 2^31); 0 1 2; null
)

NB. The sparse fill value (null) indicates that the given triple
NB. is not yet in the system.

get_memo =: verb define
  NB. f,g,h → nid
  (<y) { BDD_INDEX
)

NB. The 'nid' verb lets us read and write node ids to the index:
nid =: verb define
  NB. nid y=.(if,th,el): fetch id of this triple (create if necessary)
  r=.get_memo y
  if. r=null do. NB. -- store new triple ---
    'IF TH EL' =. y
    BDD_IF =: BDD_IF, IF
    BDD_TH =: BDD_TH, TH
    BDD_EL =: BDD_EL, EL
    BDD_RC =: BDD_RC, 1    NB. add reference by default.
    (<: # BDD_IF) nid y    NB. index and return the new nid.
  end.
:
  NB. x nid y=.if,th,el: store x as nid for this triple.
  x [ BDD_INDEX =: x (<y) } BDD_INDEX
)


NB. ┌──────────────────────────────────────────────────────────┐
NB. │ operations on bdd nodes                                  │
NB. └──────────────────────────────────────────────────────────┘

not =: [: - 1 + ]

bdd =: verb define "0 1 0
  NB. bdd y=.nid → (if,th,el) from the BDD table
  NB. when | y = null → error (null marks bigrefs, so use big
  NB.      | y <:_1 → not y{BDD
  NB.      | y >: 0 → y{BDD
  if. (sign =. *y)=_1 do. y=. not y end.
  r =. (y { BDD_IF), (y { BDD_TH), (y { BDD_EL)
  if. sign = _1 do. ({., not@}.) r else. r end.
)

NB. hi and lo are each mutually recursive with the ite routine,
NB. defined below. (they get called from ite_build)
hi =: dyad define
  NB. evaluate a triple as if x=l
  NB. x hi y=.nid →  nid of (y when bvar x = 1)
  'yv yt ye' =. bdd y
  if.      x = yv do. yt     NB. x ∧ if(x,th,_) → th
  elseif. yv = _1 do. y      NB. y constant, so no change
  elseif.  x < yv do. y      NB. y independent of x, so no change.
  elseif.  x > yv do.        NB. y depends on x, so recurse.
    ite yv, (x hi yt), (x hi ye)
  end.
)

lo =: dyad define
  NB. evaluate a triple as if x=0
  NB. x hi y=.nid →  nid of (y when bvar x = 0)
  'yv yt ye' =. bdd y
  if.      x = yv do. ye     NB. ¬x ∧ if(x,_,el) → el
  elseif. yv = _1 do. y      NB. y constant, so no change
  elseif.  x < yv do. y      NB. y independent of x, so no change.
  elseif.  x > yv do.        NB. y depends on x, so recurse.
    ite yv, (x lo yt), (x lo ye)
  end.
)



NB. ┌──────────────────────────────────────────────────────────┐
NB. │ normalization, part 1                      (f,g,h) → nid │
NB. └──────────────────────────────────────────────────────────┘
NB.   While there is exactly one reduced BDD representation of
NB. a given boolean expression (per ordering of input bits),
NB. there are an infinite number of expressions which reduce
NB. to that same BDD.
NB.
NB.   As a trivial example, "A *. B" has the same truth table
NB. as "B *. A", and there are an infinite number of equivalent
NB. encodings. (Simple proof: you can keep appending phrases
NB. like '*. 1', '*. A', or '+. 0' indefinitely.)
NB.
NB.   Further, we are treating negative nodes as complements,
NB. and while there are 8=2^3 patterns of not signs for each
NB. triple, it turns out that (f,g,h)=-.(f,(-.g),-.h). We follow
NB. [EIOBP] here, and chose the version where g is a normal edge.
NB.
NB.   The following routines make it easier to normalize the
NB. work of computing BDD combinations. It is based on the
NB. algorithms from [EIOBP]. The main difference is that since J
NB. provides the caching feature for us through the M. adverb.
NB.
NB.   I broke it into two verbs because M. acts on all inputs,
NB. and there‘s no need to memoize the simple base cases.

ite_norm =: verb define
  NB. if/then/else normalizer (f,g,h:nid) → nid | (f′,g′,h′) | <(f′,g′,h′)
  NB. (boxed result indicates the whole triple should be inverted.)
  'f g h' =. y   NB. but first, normalize the signs:
  select. f,  g,  h [ nf=. not f
  case.   l,  g,  h do. g
  case.   o,  g,  h do. h
  case.   f,  g,  g do. g
  case.   f,  l,  o do. f
  case.   f,  o,  l do. nf
  case.   f,  f,  o do. f
  case.   f,  f,  l do. l
  case.   f,  f,  h do. ite_norm f, l, h
  case.   f,  g,  f do. ite_norm f, g, o
  case.   f,  g, nf do. ite_norm f, g, l
  case.   f, nf,  h do. ite_norm f, o, h
  case. do. ite_norm2 f, g, h end.
)


NB. ┌──────────────────────────────────────────────────────────┐
NB. │ normalization, part 2                      (f,g,h) → nid │
NB. └──────────────────────────────────────────────────────────┘
NB.   The second major normalization step is to choose between
NB. equivalent triples. For example, (f,1,h)=(h,1,f). Again we
NB. follow a rule from [EIOBP], and chose the version whose first
NB. node has the smaller branching variable, falling back to the
NB. nid as a tiebreaker.

(log =: verb :'if. DEBUG do. echo y else. end.') DEBUG=:0
pos =: ]`not @.(<1:)"0
cmp =: dyad define
  if. (0{x)<(0{y) do. 1 else. (0{x)=(0{y) *. (1{x)<(1{y) end.
)

ite_norm2 =: verb define
  NB. (f,g,h:nid) → nid | (f′,g′,h′) | <(f′,g′,h′)
  NB. (boxed result indicates the whole triple should be inverted.)
  NB. Do not call this directly -- just call ite_norm.
  'fv ft fe   gv gt ge   hv ht he'=. , bdd 'f g h'=.y
  'nf ng nh' =. not y [ 'pf pg ph'=. pos y NB. flp and strip -. sign
  select.  g, h  NB. -- chose standard triple --
  case. l, h do. if. (hv,ph) cmp (fv,pf) do. ite_norm  h, l, f [log'c0'return. end.
  case. g, o do. if. (gv,pg) cmp (fv,pf) do. ite_norm  g, f, o [log'c1'return. end.
  case. g, l do. if. (gv,pg) cmp (fv,pf) do. ite_norm ng,nf, l [log'c2'return. end.
  case. o, h do. if. (hv,ph) cmp (fv,pf) do. ite_norm nh, o,nf [log'c3'return. end.
  case. g,ng do. if. (gv,pg) cmp (fv,pf) do. ite_norm  g, f,nf [log'c4'return. end.
  end.
  NB. (f,g,h:nid) → nid memoized helper for ite.
  NB. choose form:   0: f,g,h | 1: (¬f,h,g) | 2: ¬(f,¬g,¬h) | 3: ¬(¬f,¬g,¬h)
  NB. (we pick the one where the first two slots are NOT inverted)
  if. f<0 do.     ite_norm nf,  h,  g return. end.
  if. g<0 do. r=. ite_norm  f, ng, nh if. 1=#r do. not r else. <r end. return. end.
  NB. at this point, we should have a completely normalized
  NB. triple, and we are ready to build a new node... But first
  NB. check whether we already have a memo for it:
  if. a:= m =. get_memo f,g,h do. f,g,h else. m end.
)


NB. ┌──────────────────────────────────────────────────────────┐
NB. │ node construction                          (f,g,h) → nid │
NB. └──────────────────────────────────────────────────────────┘
ite =: verb define
  NB. (f,g,h:nid) → nid  -- if/then/else
  log 'ite ',":y
  norm =. ite_norm y
  invert =. 'boxed' -: datatype norm
  if. invert do. norm =. > norm end.
  if. 1=#norm do. res =. norm else. res =. ite_build norm end.
  if. invert do. not res else. res end.
)

ite_build =: verb define M.
  log 'ite_build ', ": y
  'fv ft fe   gv gt ge   hv ht he'=. , bdd 'f g h'=.y
  v =. <./ fv,gv,hv
  th =. ite (v hi f),(v hi g),(v hi h)
  el =. ite (v lo f),(v lo g),(v lo h)
  if. th = el do. th else. nid v,th,el end.
)


NB. ┌──────────────────────────────────────────────────────────┐
NB. │ normalization, part 3              (f,op,g) → (if,th,el) │
NB. └──────────────────────────────────────────────────────────┘
NB.   The final normalization is to rewrite all other boolean
NB. operations in if/then/else form. Again, This technique comes
NB. from the [EIOBP] paper. All of these routine take and return nids.

          bd0000 =: (                    o        )"0  NB.     ⊥
bdAND  =: bd0001 =: (dyad : 'ite  x,     y,     o')"0  NB.   x ∧ y
bdGT   =: bd0010 =: (dyad : 'ite  x,(not y),    o')"0  NB.   x > y
          bd0011 =: (dyad : 'ite  x,     x,     x')"0  NB.   x
bdLT   =: bd0100 =: (dyad : 'ite  x,     o,     y')"0  NB.   x < y
          bd0101 =: (dyad : '            y       ')"0  NB.       y
bdXOR  =: bd0110 =: (dyad : 'ite  x,(not y),    y')"0  NB.   x ≠ y
bdVEL  =: bd0111 =: (dyad : 'ite  x,     l,     y')"0  NB.   x ∨ y
bdNOR  =: bd1000 =: (dyad : 'ite  x,     o, not y')"0  NB. ¬(x ∨ y)
bdEQ   =: bd1001 =: (dyad : 'ite  x,     y, not y')"0  NB.   x = y
bdNOT  =: bd1010 =: (                not :  not@] )"0  NB.      ¬y   ambivalent!
bdGTE  =: bd1011 =: (dyad : 'ite  x,     l, not y')"0  NB.   x ≥ y   |  fx ← fy
          bd1100 =: (dyad : 'ite  x,     o,     l')"0  NB.  ¬x
bdLTE  =: bd1101 =: (dyad : 'ite  x,     y,     l')"0  NB.   x ≤ y   |  fx → fy
bdNAND =: bd1110 =: (dyad : 'ite  x,(not y),    l')"0  NB. ¬(x ∧ y)
          bd1111 =: (                    l        )"0  NB.     ⊤

ops =:     bd0000`bd0001`bd0010`bd0011`bd0100`bd0101`bd0110`bd0111
ops =: ops,bd1000`bd1001`bd1010`bd1011`bd1100`bd1101`bd1110`bd1111
opnum =: adverb : '#. 0 0 1 1 u 0 1 0 1'
bddop =: adverb : '(ops@.(u opnum))'        NB. for bdd nodes



NB. ┌──────────────────────────────────────────────────────────┐
NB. │ test cases:normalization                                 │
NB. └──────────────────────────────────────────────────────────┘
NB. this is a manual test. uncomment the bottom line to
NB. generate a text file that shows the normal form for each
NB. possible triple drawn from three variables, their complements,
NB. and the constants o and l. The intent is that this output can
NB. be compared to the output of other implementations.
tuplize =: verb define
  '(', (', ' joinstring <@":"0 y), ')'
)

norm_str =: verb define
  n =. ite_norm y
  invert =. 'boxed' -: datatype n
  if. invert do. n =. > n end.
  if. 1=#n do. s =. ":n else. s=. tuplize n end.
  if. invert do. s =. '¬',s end.
  ('_';'-') stringreplace (tuplize y), ' → ', s return.
)

gen_norms =: verb define
  if. y-:'' do. print =. echo else.
    '' fwrite y
    print =. [: (fappend & y) LF ,~ ]
  end.
  create 3
  each =. 0 _1, 1 _2, 2 _3, 3 _4
  for_f. each do.
    for_g. each do.
      for_h. each do.
        print norm_str f,g,h
      end.
    end.
  end.
)
NB. gen_norms'norms.txt'


NB. ┌──────────────────────────────────────────────────────────┐
NB. │ test cases                                               │
NB. └──────────────────────────────────────────────────────────┘
create 32 NB. just so the tests work.

'crc' assert  _3702406160 -: crc 0 binrep i. 16 16
'bvar0' assert (l = 9 hi bvar 9)  *. o = 7 lo bvar 7
'bvar1' assert (1,l,o) -: bdd bvar 1

'l23' assert  2 = ite  l, 2, 3
'o23' assert  3 = ite  o, 2, 3
'2lo' assert  2 = ite  2, l, o
'2ol' assert _3 = ite  2, o, l  NB. -.2
'222' assert  2 = ite  2, 2, 2
'22o' assert  2 = ite  2, 2, o

'nf ng nh' =: -. 'f g h' =: bvar 1 2 3

'ffg' assert (ite f, f, g) -: (ite_norm f, l, g)
'fgf' assert (ite f, g, f) -: (ite f, g, o)
'fgnf'assert (ite f, g,nf) -: (ite f, g, l)
'fnfg'assert (ite f,nf, g) -: (ite f, o, g)


'aAb=bAa'  assert (bdAND/ bvar 1 2) -: (bdAND/ bvar 2 1)
'v0=v0Av0' assert (bdAND/ bvar 1 1) -: bvar 1
'aXb=bXa'  assert (bdXOR/ bvar 1 2) -: (bdXOR/ bvar 2 1)
erase'nf f g h'



NB. echo 'loaded speedy-bdd!'

check_nid =: noun define NB.  TODO: add this as sanity checker.
  NB. this would be nice to have for debugging.
  'first item must be bddvar or _1' assert (v e. _1,bddvars)
  if. IF=_1 do.
  'hi and lo values must be valid nids' assert hi, lo < # BDD_IF
)
