it.fuser{
  import star.

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
  unfold(expr([single(call(Nm,Ar)),..Args]),Dict,Env) where
      fun(_,ATs,RTs,Lcls,Repl)^=Dict[Nm] =>
    unfold(
      foldLeft((((VNm,VTp),Ex),Bnd)=>letExp(VNm,VTp,Ex,Bnd),
	block(Repl)::expr,zip(ATs,Args)),Dict,Env).
  unfold(expr(Els),Dict,Env) => expr(Els//(E)=>unfold(E,Dict,Env)).
  unfold(letExp(Nm,Tp,V,Bnd),Dict,Env) =>
    unfold(Bnd,Dict,Env[Nm->unfold(V,Dict,Env)]).
  unfold(single(E),_,_) => single(E).
  unfold(Ex,_,_) default => trace("cannot unfold ",Ex).

  public implementation inline[expr] => {.
    inline(E,D) => unfold(E,D,[])
  .}

  collectTokens:(expr,map[string,ins]) => map[string,ins].
  collectTokens(single(I),Toks) => Toks.
  collectTokens(expr([single(own(Nm,Tp,Ins)),..Els]),Toks) =>
    Toks[Nm->own(Nm,Tp,Ins)].
  collectTokens(expr(Args),Map) =>
    foldLeft(collectTokens,Map,Args).
  collectTokens(letExp(Nm,Tp,Bn,Vl),Toks) => 
    collectTokens(Vl,collectTokens(Bn,Toks)).

  consumeToken:(expr,cons[integer],string) => option[(cons[integer],cons[integer])].
  consumeToken(expr([single(call(_,_)),..Args]),Path,Tok) where
      Sub^=lookInExps(Args,1,[],Tok) => some((Path,Sub)).
  consumeToken(expr(Els),Path,Tok) =>
    consumeInExps(reverse(Els),size(Els)-1,Path,Tok).
  consumeToken(_,_,_) default => .none.

  consumeInExps([],_,_,_) => .none.
  consumeInExps([E,.._],Ix,Path,Tok) where
      Succ ^= consumeToken(E,[Ix,..Path],Tok) => some(Succ).
  consumeInExps([_,..Es],Ix,Path,Tok) =>
    consumeInExps(Es,Ix-1,Path,Tok).

  lookInExp(expr([single(.owned_access),expr([single(own(Tok,_,_)),.._])]),
    Path,Tok) => some(Path).
  lookInExp(expr(Args),Path,Tok) =>
    lookInExps(Args,0,Path,Tok).
  lookInExp(_,_,_) default => .none.
  
  lookInExps([],_,_,_) => .none.
  lookInExps([E,..Es],Ix,Path,Tok) where Sub^= lookInExp(E,[Ix,..Path],Tok) => some(Sub).
  lookInExps([_,..Es],Ix,Path,Tok) =>
    lookInExps(Es,Ix+1,Path,Tok).

  updateWithPath:(expr,cons[integer],expr)=>expr.
  updateWithPath(E,[],Rel) => expr([Rel,E]).
  updateWithPath(expr(Els),[Ix,..Pth],Rel) where Sub^=Els[Ix] =>
    expr(Els[Ix->updateWithPath(trace("sub, $(Ix)->$(Pth)",Sub),Pth,Rel)]).

  pickupRelease(own(K,_,Ins)) => single(block([getLocl(K),Ins])).
  
  inlineFun:(fun,map[string,fun]) => fun.
  inlineFun(fun(Nm,ArgTps,ReTp,Lcls,Repl),Dict) => valof action{
    U .= ref unfold(block(Repl)::expr,Dict[!Nm],[]);
    logMsg("unfolded $(U!!)");
    NM .= collectTokens(U!!,[]);
    logMsg("Tokens: $(NM)");
    for K -> O in NM do{
      if (Path,Sub) ^= consumeToken(U!!,[],K) then{
	logMsg("Found Path = $(Path), sub path = $(Sub)");
	U := updateWithPath(U!!,reverse(Path),pickupRelease(O))
      } else {
	U := updateWithPath(U!!,[],pickupRelease(O))
      }
    };
    logMsg("after adding releases $(U!!)");
    valis fun(Nm,ArgTps,ReTp,addLocals(Lcls,NM),annihilate(U!!)::cons[ins])
  }

  addLocals:(cons[(string,it)],map[string,ins])=>cons[(string,it)].
  addLocals(Lcls,MM) =>
    ixRight((_,own(Nm,Tp,_),L) => [(Nm,Tp),..L],Lcls,MM).

  public implementation inline[fun] => {.
    inline = inlineFun
  .}

  annihilate:(expr)=>expr.
  annihilate(expr(Args)) => applyTool(expr(Args//annihilate)).
  annihilate(single(I)) => single(I).
  annihilate(letExp(Nm,Tp,Val,Bnd)) =>
    letExp(Nm,Tp,annihilate(Val),annihilate(Bnd)).

  -- Specific transformation tools

  applyTool(expr([single(.I32FromS32),expr([single(.S32FromI32),E])])) => E.
  applyTool(expr([single(.from_string),T,expr([single(.string_from),S,L])])) =>
    expr([single(.memory_copy),S,T,L]).
  applyTool(expr([single(.string_size),expr([single(.string_from),_,Len])])) => Len.
  applyTool(expr([single(.owned_access),E])) => E.
  applyTool(expr([single(own(Lbl,It,_)),E])) =>
    expr([single(teeLocal(Lbl)),E]).
  applyTool(E) default => E.
}
  
