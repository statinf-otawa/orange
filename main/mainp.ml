(* 
 *	$Id: mainp.ml,v 1.1 2008/07/18 11:45:19 michiel Exp $
 *	Copyright (c) 2003, Hugues Cassé <hugues.casse@laposte.net>
 *
 *	Pretty printer of XML document.
 *)

open Frontc
open Orange



(* Options *)
let banner =
	"ctoxml V1.0 (02/14/04)\n" ^
	"Copyright (c) 2004, Hugues Cassé <hugues.casse@laposte.net>\n\n" ^
	"SYNTAX:\tctoxml [options] files...\n" ^
	"\tctoxml [options] --\n"

let files: string list ref = ref []
let out_file = ref ""
let from_stdin = ref false

let args: Frontc.parsing_arg list ref = ref []
let args2: Frontc.parsing_arg list ref = ref []

let add_file filename =
	files := List.append !files [filename]

let opts = [
	("-o", Arg.Set_string out_file,
		"Output to the given file.");
	("-pp", Arg.Unit (fun _ -> args := USE_CPP :: !args),
		"Preprocess the input files.");
	("-nogcc", Arg.Unit (fun _ -> args := (GCC_SUPPORT false) :: !args),
		"Do not use the GCC extensions.");
	("-proc", Arg.String (fun cpp -> args := (PREPROC cpp) :: !args),
		"Use the given preprocessor");
	("-i", Arg.String (fun file -> args := (INCLUDE file) :: !args),
		"Include the given file.");
	("-I", Arg.String (fun dir -> args := (INCLUDE_DIR dir) :: !args),
		"Include retrieval directory");
	("-D", Arg.String (fun def -> args := (DEF def) :: !args),
		"Pass this definition to the preprocessor.");
	("-U", Arg.String (fun undef -> args := (UNDEF undef) :: !args),
		"Pass this undefinition to the preprocessor.");
	("-l", Arg.Unit (fun _ -> args := (Frontc.LINE_RECORD true)::!args),
		"Generate #line directive.");
	("--", Arg.Set from_stdin,
		"Takes input from standard input.");
]

(* Main Program *)
let _ =
	(*Calipso.process*)


	(* Get the output *)
	let (output, close) =
		if !out_file = "" then (stdout,false)
		else ((open_out !out_file), true) in
	

	(* Process the input *)


	(*let filesmem = !files in*)
	Arg.parse opts add_file banner;
	let a1 = !args in
				
	let a2 = List.filter (fun e ->  match e with LINE_RECORD _-> false |_-> true) a1 in			
				 
				let firstParse =
						(match (Frontc.parse  ((FROM_FILE (List.hd !files)) :: a1)) with 
							PARSING_ERROR ->  []
							| PARSING_OK f2 -> 
							Rename.go (Frontc.trans_old_fun_defs  f2 )

								
							 ) in
				

				
		 		Orange.initref stdout firstParse;
		
				(*Cprint.print stdout firstParse ; (*plante avec l'option -l*)*)
				 
				let secondParse =
						(match Frontc.parse  ((FROM_FILE (List.hd !files)) :: a2) with 
							PARSING_ERROR ->  []
							| PARSING_OK f2 -> 

							Rename.go(Frontc.trans_old_fun_defs  f2 )  ) in

				
				(*Orange.initref stdout secondParse;*)
				Orange.printFile  stdout secondParse;



	(* Close the output if needed *)
	if close then close_out output

	

