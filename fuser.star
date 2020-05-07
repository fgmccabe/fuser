it.fuser{
  import star.
  import star.script.

  public import it.expr.
  public import it.scan.

  isCoercion(.I32FromS32) => .true.
  isCoercion(.S32FromI32) => .true.
  isCoercion(.string_from) => .true.
  isCoercion(.from_string) => .true.
  isCoercion(_) default => .false.

  public contract all t ~~ inline[t] ::= {
    inline:(t,map[string,fun])=>t.
  }

  public unfold:(expr,map[string,fun],map[string,expr])=>expr.
  unfold(single(getLocl(Nm)),Dict,Env) => (E^=Env[Nm] ? E || single(getLocl(Nm))).
  unfold(expr(call(Nm,Ar),Args),Dict,Env) where
      fun(_,ATs,RTs,Lcls,Repl)^=Dict[Nm] =>
    unfold(
      foldLeft((((VNm,VTp),Ex),Bnd)=>letExp(VNm,VTp,Ex,Bnd),
	Repl,zip(ATs,Args)),Dict,Env).
  unfold(expr(Ins,Els),Dict,Env) => expr(Ins,Els//(E)=>unfold(E,Dict,Env)).
  unfold(letExp(Nm,Tp,V,Bnd),Dict,Env) =>
    unfold(Bnd,Dict,Env[Nm->unfold(V,Dict,Env)]).
  unfold(Ex,_,_) default => trace("cannot unfold ",Ex).

  public implementation inline[expr] => {.
    inline(E,D) => unfold(E,D,[])
  .}

  inlineFun:(fun,map[string,fun]) => fun.
  inlineFun(fun(Nm,ArgTps,ReTp,Lcls,Repl),Dict) =>
    fun(Nm,ArgTps,ReTp,Lcls,
      annihilate(unfold(Repl,Dict[!Nm],[]))).

  public implementation inline[fun] => {.
    inline = inlineFun
  .}

  annihilate:(expr)=>expr.
  annihilate(expr(Cx,Args)) => applyTool(expr(Cx,Args//annihilate)).
  annihilate(single(I)) => single(I).
  annihilate(letExp(Nm,Tp,Val,Bnd)) =>
    letExp(Nm,Tp,annihilate(Val),annihilate(Bnd)).

  applyTool(expr(Cx,Args)) where T^=tools[Cx] &&
      R ^= T(expr(Cx,Args)) => R.
  applyTool(E) default => E.

  -- Specific transformation tools

  rewrite ~> (expr)=>option[expr].
  
  tools : map[ins,rewrite].
  tools = [.I32FromS32 -> moveInt,
    .from_string -> moveString,
    .string_size -> sizeString].
  
  moveInt(expr(.I32FromS32,[expr(.S32FromI32,[E])])) => some(E).
  moveInt(_) => .none.

  moveString(expr(.from_string,[T,expr(.string_from,[S,L])])) =>
    some(expr(.memory_copy,[T,S,L])).
  moveString(_) default => .none.

  sizeString(expr(.string_size,[expr(.string_from,[_,Len])])) => some(Len).
  sizeString(_) default => .none.
  
}
  
