{$mode delphi}{$i xpc}
unit ubdd;
interface uses xpc, sysutils;

type
  tNID = uINT32;
  tVAR = uINT32;
  TDefNode = record end; // definitions (combinators)
  TDefNodes = record
    max_var : tVAR;
    defs: array of TDefNode;
  end;
  { TBitOp = function (a,b:boolean):boolean; }
  TBddNode = class; // forward
  TBddBase = class
    root: TBddNode; max_var: tVAR;
    nodes : array of TBddNode;
    constructor create;
    function replace_max(old, new:TBDDNode):TBDDNode;
    function get_var(v: tVar): TBddNode;
    function ite(v, hi, lo:TBddNode): TBddNode;
    function from_def(var TDefNode): TBddNode;
    { function meld(a,b : TBDD; op:TBitOp):TBDD; }
  end;
  TBddNode = class // BDD (lookup table)
    base : TBddBase;
    v, max: tVAR;
    lo, hi: TBddNode;
    rc: uINT32;
    constructor create(base: TBddBase; v : tVar; hi, lo:TBddNode);
    function when_hi(v: tVar): TBddNode;
    function when_lo(v: tVar): TBddNode;
  end;

implementation

// -- TBddBase --

constructor TBddBase.Create;
  begin self.root := TBddNode.Create(self, 0, nil, nil);
  end;


function TBddBase.get_var(v: tVar): TBddNode;
  begin result := TBddNode.Create(self, 0, nil, nil);
  end;

function TBddBase.ite(v, hi, lo:TBDDNode):TBDDNode;
  begin result := TBddNode.Create(self, v.v, hi, lo);  writeln('todo: ite')
  end;


function TBddBase.replace_max(old, new:TBDDNode):TBDDNode;
  var rlo, rhi : TBddNode;
  begin
    if old.max < max_var then result := old // no replacement needed
    else if old.max > max_var then raise Exception.Create('error: found node.max > max_var. what?!')
    else if old.v = max_var then raise Exception.Create('error: reached node.v=max_var. what?!')
    else if old.v < new.v then result := ite(self.get_var(old.v), replace_max(old.hi, new), replace_max(old.lo, new))
    else if old.v > new.v then begin
      rhi := old.when_hi(max_var); rlo := old.when_lo(max_var);
      result := ite(self.get_var(new.v),
		    ite(new.hi, rhi, rlo),
		    ite(new.lo, rhi, rlo))
    end
    else if old.v = new.v then raise Exception.Create('todo: old.v = new.v')
  end;

function TBddBase.from_def(var TDefNode): TBddNode;
  begin result := TBddNode.Create(self, 0, nil, nil); writeln('todo: from_def')
  end;


// -- TBddNode ---

constructor TBddNode.Create(base: TBddBase; v : tVar; hi, lo:TBDDNode);
  begin self.base := base; self.v := v; self.hi := hi; self.lo := lo; self.rc := 0
  end;

function TBddNode.when_hi(v: tVar): TBddNode;
  begin
    if (self.v = 0) or (v < self.v) then result := self
    else if v = self.v then result := self.hi
    else {v > self.v} result := self.base.ite(self.base.get_var(self.v),
					      self.hi.when_hi(v), self.lo.when_hi(v))
  end;

function TBddNode.when_lo(v: tVar): TBddNode;
  begin
    if (self.v = 0) or (v < self.v) then result := self
    else if (v = self.v) then result := self.lo
    else {v > self.v} result := self.base.ite(self.base.get_var(self.v),
					      self.hi.when_lo(v), self.lo.when_lo(v));
  end;


{
function meld(a,b : TBDDRec; op:TBitOp):TBDD;
  var vn: cardinal; lo,hi:TBDD;
  begin
    if (a.vn in [0,1]) and (b.vn in [0,1]) then result := op(a,b)
    else if a.vn = b.vn then
      result := bdd(a.vn, meld(a.lo,b.lo,op), meld(a.hi,b.hi,op))
    else if a.vn < b.vn then
      result := bdd(a.vn, meld(a.lo,b,op), meld(a.hi,b,op))
    else // a.vn > b.vn
      result := bdd(a.vn, meld(a,b.lo,op), meld(a,b.lo,op))
  end;
}

begin
end.
