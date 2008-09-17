(* 
 *	$Id: main.ml,v 1.2 2008/07/18 11:36:31 michiel Exp $
 *	Copyright (c) 2003, Hugues Cass� <hugues.casse@laposte.net>
 *
 *	Pretty printer of XML document.
 *)

open Frontc
open Orange
open Cextraireboucle

let rec printlist li= match li with 
	[] -> output_string stdout ""
	|e::l -> begin output_string stdout e; output_string stdout "\n" ; printlist l end

let rec printlistref li= match li with 
	[] -> output_string stdout ""
	|e::l -> begin output_string stdout !e; output_string stdout "\n" ; printlistref l end

(* Options *)
let banner =
	"ctoxml V1.0 (02/14/04)\n" ^
	"Copyright (c) 2004, Hugues Cass� <hugues.casse@laposte.net>\n\n" ^
	"SYNTAX:\tctoxml [options] files...\n" ^
	"\tctoxml [options] --\n"

let list_file_and_name: string list ref = ref []

let out_file = ref ""
let from_stdin = ref false

let args: Frontc.parsing_arg list ref = ref []
let args2: Frontc.parsing_arg list ref = ref []


let add_file_and_name filename =
	list_file_and_name := List.append !list_file_and_name [filename]

type myArgs_t = COMP of string
type compInfo = int list

let myArgs: myArgs_t list ref = ref []


let myComps: (string * compInfo) list ref = ref []


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
	("-c", Arg.String (fun def -> myArgs := (COMP def) :: !myArgs),
		"Declare a function as a component to do partial analysis.");
	("-U", Arg.String (fun undef -> args := (UNDEF undef) :: !args),
		"Pass this undefinition to the preprocessor.");
	("-l", Arg.Unit (fun _ -> args := (Frontc.LINE_RECORD true)::!args),
		"Generate #line directive.");
	("--", Arg.Set from_stdin,
		"Takes input from standard input.");
]

let isComponent comp = 
  let rec aux = function
     [] -> false
    | (COMP comp2)::r -> if (comp = comp2) then (true) else (aux r)
  in aux !myArgs
  
  
let rec getComps = function
   [] -> []
  |t::r -> let fname = ((snd t).nom) and reste = (getComps r) in
           if (isComponent fname) then (fname, [])::reste else reste

let analysePartielle file = 
 analyse_defs file;
 myComps := (getComps !doc.laListeDesFonctions);
 print_string "OK\n"
  
(* Main Program *)
let _ =
	(*Calipso.process*)


	(* Get the output *)
	let (output, close) =
		if !out_file = "" then (stdout,false)
		else ((open_out !out_file), true) in
	

	(* Process the input *)
(*	let process opts =
		(match Frontc.parse opts with
		  PARSING_ERROR ->  ()
		| PARSING_OK file -> 
			(*Frontc.convert_to_c file in*)
 
			let safe_file = Frontc.trans_old_fun_defs  file in
 
			let safe_fileaux = Rename.go safe_file in
 
			Orange.printFile stdout safe_fileaux safe_fileaux;
	) in*)

	(*let filesmem = !files in*)
	Arg.parse opts add_file_and_name banner;
	(*printlist !list_file_and_name ;*)
	Cextraireboucle.sort_list_file_and_name !list_file_and_name;
	let hd=(! (List.hd (!Cextraireboucle.names))) and tl =(List.tl (!Cextraireboucle.names)) in
	Cextraireboucle.maj hd tl;
	let a1 = !args in
				
				
	let a2 = List.filter (fun e ->  match e with LINE_RECORD _-> false |_-> true) a1 in			
				 
				let firstParse =
						(match (Frontc.parse  ((FROM_FILE (List.hd !Cextraireboucle.files)) :: a1)) with 
							PARSING_ERROR ->  []
							| PARSING_OK f2 -> 
							Rename.go (Frontc.trans_old_fun_defs  f2 )

								
							 ) in
				

				
		 		Orange.initref stdout firstParse;
		
				(*Cprint.print stdout firstParse ; (*plante avec l'option -l*)*)
				let secondParse =
						(match Frontc.parse  ((FROM_FILE (List.hd !Cextraireboucle.files)) :: a2) with 
							PARSING_ERROR ->  []
							| PARSING_OK f2 -> 

							Rename.go(Frontc.trans_old_fun_defs  f2 )  ) in

				
				(*Orange.initref stdout secondParse;*)
				(* analysePartielle secondParse; *)
				Orange.printFile stdout secondParse;



                              (* Close the output if needed *)
                              if close then close_out output
                               