it.twizzle{
  import star.
  import star.script.
  import it.fuser.


  twizzleExport = fun("twizzle",[("a1",.s32),("a2",.s32)],[.s32],
    ["a1"->.s32,"a2"->.s32],
    foldIns([getLocl("a1"),
      .I32FromS32,
      getLocl("a2"),
      .I32FromS32,
      call("twizzle_",2),
	.S32FromI32])).
      
  twizzleImport = fun("twozzle",[("b1",.i32),("b2",.i32)],[.i32],
    ["b1"->.i32,"b2"->.i32],
    foldIns([getLocl("b1"),
      .S32FromI32,
      getLocl("b2"),
      .S32FromI32,
      call("twizzle",2),
	.I32FromS32])).


  main:()=>action[(),()].
  main()=>do{
/*    L1 .= [getLocl("a"),getLocl("b"),getLocl("c"),call("plus",2),call("min",2)];
    show L1;

    P1 .= block(L1)::expr;

    show P1;

    show P1::ins;
*/

    show twizzleExport;

    show twizzleImport;

    Prog .= ["twizzle"->twizzleExport,"twozzle"->twizzleImport];

    show inline(twizzleImport,Prog)
  }
}
