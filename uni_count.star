it.count{
  import star.
  import star.script.

  import it.fuser.

  -- Unicode counter

  countExport = fun("countCodes",[("str",.str)],[.s32],[],
    [getLocl("str"),
	.string_size,
	call("malloc",1),
	own("s1",.i32,call("free",1)),
	letLocal("tgt",owned(.i32),[
	    getLocl("str"),
	    getLocl("tgt"),
	    .owned_access,
	    .from_string,
	    getLocl("str"),
	    .string_size,
	    call("countCodesImpl",2),
	    .S32FromI32])]).

  countImport = fun("countCodes_",[("ptr",.i32),("len",.i32)],[.i32],[],
    [getLocl("ptr"),
	getLocl("len"),
	.string_from,
	call("countCodes",1),
      .I32FromS32]).

  main:()=>action[(),()].
  main()=>do{
    show countExport;
    show countImport;

    Prog .= ["countCodes"->countExport,"countCodes_"->countImport];

    show inline(countImport,Prog)
  }
}
  
