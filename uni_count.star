it.count{
  import star.
  import star.script.

  import it.fuser.

  -- Unicode counter

  countExport = fun("countCodes",[("str",.str)],[.s32],
    ["str"->.str],
    foldIns([getLocl("str"),
	.string_size,
	call("malloc",1),
	own([.i32],[call("free",1)]),
	letLocal("tgt",owned(.i32),[
	    getLocl("str"),
	    getLocl("tgt"),
	    .owned_access,
	    .from_string,
	    call("countCodesImpl",1),
	    .S32FromI32])])).

  countImport = fun("countCodes_",[("ptr",.i32),("len",.i32)],[.i32],[],
    foldIns([getLocl("ptr"),
	getLocl("len"),
	.string_from,
	call("countCodes",1),
	.I32FromS32])).

  main:()=>action[(),()].
  main()=>do{
    show countExport;

    show countImport;

    Prog .= ["countCodes"->countExport,"countCodes_"->countImport];

    show inline(countImport,Prog)
  }
}
  
