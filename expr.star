it.expr{
  import star.

  public it ::= .s32 | .u32 | .i32 | .str | owned(it) .

  public implementation equality[it] => let{
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

  public expr ::= single(ins)
    | expr(ins,cons[expr])
    | letExp(string,it,expr,expr).

  public fun ::= fun(string,cons[(string,it)],cons[it],map[string,it],expr).

  public implementation hash[ins] => let{
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

  public implementation equality[ins] => let{
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
    eq(.memory_copy,.memory_copy) => .true.
    eq(_,_) default => .false.

    eqL:(cons[ins],cons[ins])=>boolean.
    eqL([],[]) => .true.
    eqL([E1,..L1],[E2,..L2]) => eq(E1,E2) && eqL(L1,L2).
    eqL(_,_) default => .false.
  } in {.
      (==) = eq
  .}

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
    dispIns(letLocal(Nm,Tp,Ins)) =>
      ssSeq([ss("let "),disp(Nm),ss(" in "),
	  dispBlock(Ins),ss("end")]).
    dispIns(.I32FromS32) => ss("i32.from.s32").
    dispIns(.S32FromI32) => ss("s32.from.i32").
    dispIns(.string_size) => ss("string.size").
    dispIns(.string_from) => ss("string.from.utf8").
    dispIns(.from_string) => ss("utf8.from.string").
    dispIns(call(Nm,Ar)) => ssSeq([ss("call "),disp(Nm),ss("/"),disp(Ar)]).
    dispIns(block(Ins)) => ssSeq([ss("block "),dispBlock(Ins),ss(" end")]).
    dispIns(own(Tps,Ins)) => ssSeq([ss("own ("),
	ssSeq(interleave(Tps//disp,ss(","))),ss(")"),
	dispBlock(Ins),ss(" end")]).
    dispIns(.owned_access) => ss("owned.access").
    dispIns(.owned_release) => ss("owned.release").
    dispIns(.memory_copy) => ss("memory.copy").

    dispBlock(Ins) => ssSeq(interleave(Ins//dispIns,ss("\n"))).
  } in {.
    disp = dispIns
  .}

  public implementation display[expr] => let{
    dispExp(single(Ins)) => disp(Ins).
    dispExp(expr(Ins,Args)) =>
      ssSeq([disp(Ins),ss("("),ssSeq(interleave(Args//dispExp,ss(" "))),
	  ss(")")]).
    dispExp(letExp(Nm,Tp,V,Bnd)) =>
      ssSeq([ss("[ let "),ss(Nm),ss(" = "),dispExp(V),
	  ss("\nin "),dispExp(Bnd),ss("]")]).
  } in {.
    disp(E) => dispExp(E)
  .}

  public implementation display[fun] => {.
    disp(fun(Nm,Params,Res,_,Code)) => ssSeq([ss("function "),ss(Nm),
	ss("("),ssSeq(interleave(Params//disp,ss(", "))),ss(")"),
	ss("\n"),
	disp(Code)])
  .}

}
