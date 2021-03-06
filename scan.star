it.scan{
  import star.
  import it.expr.

  public foldIns:(cons[ins])=>expr.
  foldIns(Ins) where H^=head(scan(Ins,[])) => H.

  scan:(cons[ins],cons[expr])=>cons[expr].
  scan([],Stk) => Stk.
  scan([letLocal(Nm,Tp,Code),..Cs],[El,..Stk]) where
      [Exp] .= scan(Code,[]) =>
    scan(Cs,[letExp(Nm,Tp,El,Exp),..Stk]).
  scan([getLocl(Nm),..Cs],Stk) => scan(Cs,[single(getLocl(Nm)),..Stk]).
  scan([call(Nm,Ar),..Cs],Stk) where (Top,Stk1) ^= pop(Stk,Ar) =>
    scan(Cs,[expr([single(call(Nm,Ar)),..Top]),..Stk1]).
  scan([.I32FromS32,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr([single(.I32FromS32),Top]),..Stk]).
  scan([.I32FromS32,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr([single(.I32FromS32),Top]),..Stk]).
  scan([.S32FromI32,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr([single(.S32FromI32),Top]),..Stk]).
  scan([block(In),..Is],Stk) =>
    scan(Is,scan(In,Stk)).
  scan([own(Nm,Tp,Ins),..Is],[O,..Stk]) =>
    scan(Is,[expr([single(own(Nm,Tp,Ins)),O]),..Stk]).
  scan([.owned_access,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr([single(.owned_access),Top]),..Stk]).
  scan([.owned_release,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr([single(.owned_release),Top]),..Stk]).
  scan([.string_size,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr([single(.string_size),Top]),..Stk]).
  scan([.string_from,..Cs],[Len,Base,..Stk]) =>
    scan(Cs,[expr([single(.string_from),Base,Len]),..Stk]).
  scan([.from_string,..Cs],[Tgt,Src,..Stk]) =>
    scan(Cs,[expr([single(.from_string),Src,Tgt]),..Stk]).
  scan([In,..Ins],Stk) => scan(Ins,[single(In),..Stk]).

  pop(Stk,Ar) => let{
    pp:(cons[expr],cons[expr],integer)=>option[(cons[expr],cons[expr])].
    pp(S,So,0) => some((So,S)).
    pp([],_,_) => .none.
    pp([E,..Ss],So,Cx) => pp(Ss,[E,..So],Cx-1).
  } in pp(Stk,[],Ar).

  public implementation coercion[ins,expr] => {.
    _coerce(I) => foldIns([I])
  .}

  public implementation coercion[expr,cons[ins]] => {.
    _coerce(E) => case (E::ins) in {
      block(Ins) => Ins.
      In => [In]
    }
  .}

  public implementation coercion[expr,ins] => let{
    flattn:(expr)=>cons[ins].
    flattn(single(I))=>[I].
    flattn(expr([])) => [].
    flattn(expr([A,..As])) => multicat(As//flattn)++flattn(A).
    flattn(letExp(Nm,Tp,Vl,B)) => flattn(Vl)++[letLocal(Nm,Tp,flattn(B))].
  } in {.
    _coerce(E) => case flattn(E) in {
      [I] => I.
      Ix => block(Ix)
    }
  .}
}
