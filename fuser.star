it.fuser{
  import star.
  import star.script.

  public it ::= .s32 | .u32 | .i32 | .str | owned(it) .

  implementation equality[it] => let{
    eq(.s32,.s32) => .true.
    eq(.u32,.u32) => .true.
    eq(.i32,.i32) => .true.
    eq(.str,.str) => .true.
    eq(owned(T1),owned(T2)) => eq(T1,T2).
    eq(_,_) default => .false.
  } in {.
    (==) = eq
  .}

  public ins ::= getLocl(string)
    | call(string,integer)
    | .I32FromS32
    | .S32FromI32
    | block(cons[ins])
    | letLocal(string,it,cons[ins])
    | own(cons[it],cons[ins])
    | .owned_access
    | .owned_release
    | .string_size
    | .string_from
    | .from_string
    | .memory_copy.

  implementation hash[ins] => let{
    hsh(getLocl(_)) => hash("get.local").
    hsh(call(_,_)) => hash("call").
    hsh(.I32FromS32) => hash("i32.from.s32").
    hsh(.S32FromI32) => hash("s32.from.i32").
    hsh(block(_)) => hash("block").
    hsh(letLocal(_,_,_)) => hash("let.local").
    hsh(own(_,_)) => hash("own").
    hsh(.owned_access) => hash("own.access").
    hsh(.owned_release) => hash("own.release").
    hsh(.string_size) => hash("string.size").
    hsh(.string_from) => hash("string.from").
    hsh(.from_string) => hash("from.string").
    hsh(.memory_copy) => hash("memory.copy").
  } in {.
    hash = hsh
  .}

  implementation equality[ins] => let{
    eq(getLocl(N1),getLocl(N2)) => N1==N2.
    eq(call(N1,A1),call(N2,A2)) => N1==N2 && A1==A2.
    eq(.I32FromS32,.I32FromS32) => .true.
    eq(.S32FromI32,.S32FromI32) => .true.
    eq(block(I1),block(I2)) => eqL(I1,I2).
    eq(letLocal(N1,T1,I1),letLocal(N2,T2,I2)) => N1==N2 && T1==T2 && eqL(I1,I2).
    eq(own(T1,I1),own(T2,I2)) => T1==T2 && eqL(I1,I2).
    eq(.owned_access,.owned_access) => .true.
    eq(.owned_release,.owned_release) => .true.
    eq(.string_size,.string_size) => .true.
    eq(.string_from,.string_from) => .true.
    eq(.from_string,.from_string) => .true.
    eq(_,_) default => .false.

    eqL:(cons[ins],cons[ins])=>boolean.
    eqL([],[]) => .true.
    eqL([E1,..L1],[E2,..L2]) => eq(E1,E2) && eqL(L1,L2).
    eqL(_,_) default => .false.
  } in {.
      (==) = eq
  .}

  isCoercion(.I32FromS32) => .true.
  isCoercion(.S32FromI32) => .true.
  isCoercion(.string_from) => .true.
  isCoercion(.from_string) => .true.
  isCoercion(_) default => .false.

  public expr ::= single(ins)
    | expr(ins,cons[expr])
    | letExp(string,it,expr,expr).

  public fun ::= fun(string,cons[(string,it)],cons[it],map[string,it],expr).

  public env ~> map[string,fun].

  public implementation display[it] => let{
    dispIT(.s32) => ss("s32").
    dispIT(.u32) => ss("u32").
    dispIT(.i32) => ss("i32").
    dispIT(.str) => ss("string").
    dispIT(owned(T)) => ssSeq([ss("( owned "),dispIT(T),ss(")")])
  } in {.
    disp = dispIT
  .}
  
  public implementation display[ins] => let{
    dispIns(getLocl(Nm)) => ssSeq([ss("get.local "),disp(Nm)]).
    dispIns(letLocal(Nm,Tp,Code)) =>
      ssSeq([ss("let "),disp(Nm),ss(":"),disp(Tp),ss(" in "),ssSeq(Code//dispIns),ss("end")]).
    dispIns(.I32FromS32) => ss("i32.from.s32").
    dispIns(.S32FromI32) => ss("s32.from.i32").
    dispIns(.string_size) => ss("string.size").
    dispIns(.string_from) => ss("string.from.utf8").
    dispIns(.from_string) => ss("utf8.from.string").
    dispIns(call(Nm,Ar)) => ssSeq([ss("call "),disp(Nm),ss("/"),disp(Ar)]).
    dispIns(block(Ins)) => ssSeq([ss("block "),ssSeq(Ins//dispIns),ss(" end")]).
    dispIns(own(Tps,Ins)) => ssSeq([ss("own ("),
	ssSeq(interleave(Tps//disp,ss(","))),ss(")"),
	ssSeq(Ins//dispIns),ss(" end")]).
    dispIns(.owned_access) => ss("owned.access").
    dispIns(.owned_release) => ss("owned.release").
  } in {.
    disp = dispIns
  .}

  public implementation display[expr] => let{
    dispExp(single(Ins),Depth) => disp(Ins).
    dispExp(expr(Ins,Args),Depth) =>
      ssSeq([ss("("),disp(Ins),ssSeq(Args//(A)=>
	      ssSeq([ss(","),dispExp(A,Depth+2)])),ss(")")]).
    dispExp(letExp(Nm,Tp,V,Bnd),Depth) =>
      ssSeq([ss("[ let "),ss(Nm),ss(":"),disp(Tp),ss(" = "),dispExp(V,Depth),
	  ss(" in "),dispExp(Bnd,Depth+2),ss("]")]).
  } in {.
    disp(E) => dispExp(E,0)
  .}

  public implementation display[fun] => {.
    disp(fun(Nm,Params,Res,_,Code)) => ssSeq([ss("function "),ss(Nm),
	ss("("),ssSeq(interleave(Params//disp,ss(", "))),ss(")"),
	ss("\n"),
	disp(Code)])
  .}

  public contract all t ~~ inline[t] ::= {
    inline:(t,map[string,fun])=>t.
  }

  public foldIns:(cons[ins])=>expr.
  foldIns(Ins) where H^=head(scan(Ins,[])) => H.

  scan:(cons[ins],cons[expr])=>cons[expr].
  scan([],Stk) => Stk.
  scan([letLocal(Nm,Tp,Code),..Cs],[El,..Stk]) where
      [Exp] .= scan(Code,[]) =>
    scan(Cs,[letExp(Nm,Tp,El,Exp),..Stk]).
  scan([getLocl(Nm),..Cs],Stk) => scan(Cs,[single(getLocl(Nm)),..Stk]).
  scan([call(Nm,Ar),..Cs],Stk) where (Top,Stk1) ^= pop(Stk,Ar) =>
    scan(Cs,[expr(call(Nm,Ar),Top),..Stk1]).
  scan([.I32FromS32,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr(.I32FromS32,[Top]),..Stk]).
  scan([.I32FromS32,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr(.I32FromS32,[Top]),..Stk]).
  scan([.S32FromI32,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr(.S32FromI32,[Top]),..Stk]).
  scan([block(In),..Is],Stk) =>
    scan(Is,scan(In,Stk)).
  scan([own(Tps,Ins),..Is],Stk) where (Els,_) ^= pop(Stk,size(Tps)) =>
    scan(Is,[expr(own(Tps,Ins),Els),..Stk]).
  scan([.owned_access,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr(.owned_access,[Top]),..Stk]).
  scan([.owned_release,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr(.owned_release,[Top]),..Stk]).
  scan([.string_size,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr(.string_size,[Top]),..Stk]).
  scan([.string_from,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr(.string_from,[Top]),..Stk]).
  scan([.from_string,..Cs],[Top,..Stk]) =>
    scan(Cs,[expr(.from_string,[Top]),..Stk]).
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

  public implementation coercion[expr,ins] => let{
    flattn:(expr)=>cons[ins].
    flattn(single(I))=>[I].
    flattn(expr(I,As)) => multicat(As//flattn)++[I].
    flattn(letExp(Nm,Tp,Vl,B)) => flattn(Vl)++[letLocal(Nm,Tp,flattn(B))].
  } in {.
    _coerce(E) => case flattn(E) in {
      [I] => I.
      Ix => block(Ix)
    }
  .}

  unfold:(expr,map[string,fun],map[string,expr])=>expr.
  unfold(single(getLocl(Nm)),Dict,Env) where E^=Env[Nm] => E.
  unfold(expr(call(Nm,Ar),Args),Dict,Env) where
      fun(_,ATs,RTs,Lcls,Repl)^=Dict[Nm] =>
    unfold(foldLeft((((VNm,VTp),Ex),Bnd)=>letExp(VNm,VTp,Ex,Bnd),Repl,zip(ATs,Args)),Dict,Env).
  unfold(expr(Ins,Els),Dict,Env) => expr(Ins,Els//(E)=>unfold(E,Dict,Env)).
  unfold(letExp(Nm,Tp,V,Bnd),Dict,Env) =>
    unfold(Bnd,Dict,Env[Nm->unfold(V,Dict,Env)]).
  unfold(Ex,_,_) default => Ex.

  public implementation inline[expr] => {.
    inline(E,D) => unfold(E,D,[])
  .}

  inlineFun:(fun,map[string,fun]) => fun.
  inlineFun(fun(Nm,ArgTps,ReTp,Lcls,Repl),Dict) =>
    fun(Nm,ArgTps,ReTp,Lcls,
      unfold(Repl,Dict[!Nm],[])).
--      annihilate(pushCoercions(unfold(Repl,Dict[!Nm],[])))).

  public implementation inline[fun] => {.
    inline = inlineFun
  .}

  pushCoercions:(expr)=>expr.
  pushCoercions(expr(Cx,[letExp(N,Tp,V,B)])) where isCoercion(Cx) =>
    letExp(N,Tp,pushCoercions(V),pushCoercions(expr(Cx,[B]))).
  pushCoercions(expr(Ins,Args)) => expr(Ins,Args//pushCoercions).
  pushCoercions(letExp(N,Tp,V,B))=> 
    letExp(N,Tp,pushCoercions(V),pushCoercions(B)).
  pushCoercions(Ex) default => Ex.

  annihilate:(expr)=>expr.
  annihilate(expr(Cx,Args)) where T^=tools[Cx] && R ^= T(expr(Cx,Args)) => R.
  annihilate(expr(Cx,Args)) => expr(Cx,Args//annihilate).
  annihilate(single(I)) => single(I).
  annihilate(letExp(Nm,Tp,Val,Bnd)) =>
    letExp(Nm,Tp,annihilate(Val),annihilate(Bnd)).

  -- Specific transformation tools

  rewrite ~> (expr)=>option[expr].
  
  tools : map[ins,rewrite].
  tools = [.I32FromS32 -> moveInt,
    .from_string -> moveString].
  
  moveInt(expr(.I32FromS32,[expr(.S32FromI32,[E])])) => some(E).

  moveString(expr(.from_string,[T,expr(.string_from,[S,L])])) =>
    some(expr(.memory_copy,[T,S,L])).
}
  
