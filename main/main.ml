(* 
 *	$Id: main.ml,v 1.2 2008/07/18 11:36:31 michiel Exp $
 *	Copyright (c) 2003, Hugues Cass� <hugues.casse@laposte.net>
 *
 *	Tool to compute loop bounds
 *)

open Printf
open Frontc

open Cextraireboucle
open Cvarabs
open Cabs
open Coutput
open Orange



module TreeList = struct
  type intOuNocomp = Int of int | Nocomp
  type tree = Doc of tree list
         | Function of (string * bool * bool * bool) * tree list (* function name, inloop, executed, extern *)
         | Call of (string * int * int * string * bool * bool * bool) * tree list (* function name, relative call ID, line num, source file, inlopo, executed, extern *)
         | Loop of (int * int * string * bool * intOuNocomp * intOuNocomp * string * string) * tree list (* loop id, line, source file, exact, max, toatl, exp max, exp total *)

 
  
  type t = tree * tree list  (* current, ancestor stack *)
  let null = (Doc [], [])
  exception TreeBuildException
  
  let addChild node : tree -> tree = function
     (Doc children) -> (Doc (node::children)) 
    |Function (x, children) -> Function (x, (node::children))
    |Call (x, children) -> Call (x, (node::children))
    |Loop (x, children) -> Loop (x, (node::children))
    
    
  let extractExp = function
          (ConstInt(valeur)) -> Int (int_of_string valeur)
          |(ConstFloat(valeur)) -> Int (int_of_float (float_of_string  valeur))
          | _ -> Nocomp
    
  let onBegin = function
      (Doc [], [] ) as x -> x
      | _ -> raise TreeBuildException
        

  let onEnd = function
      (Doc _, []) as x -> x
      | _ -> raise TreeBuildException
  
  let onFunction res name inloop executed extern = match res with
      (current, stack) -> 
        let newCurrent = Function ((name,inloop,executed,extern), []) in
	(newCurrent, current::stack)      

  let onLoop res loopID line source exact maxcount totalcount maxexp totalexp = match res with
      (current, stack) -> 
        let newCurrent = 
	   Loop ((loopID, line, source, exact, (extractExp maxcount), (extractExp totalcount), (string_from_expr maxexp),(string_from_expr totalexp)), []) in
	(newCurrent, current::stack)   
     
  
  let onCall res name numCall line source inloop executed extern = match res  with
      (current, stack) -> 
        let newCurrent = Call ((name, numCall, line, source, inloop, executed, extern), []) in
	(newCurrent, current::stack)   

  let onFunctionEnd = function
      (current, item::stack) -> (addChild current item), stack
      |(_, []) -> raise TreeBuildException
        	
  let onReturn = onFunctionEnd
  let onLoopEnd = onFunctionEnd 


end ;;


let rec printlist li= match li with 
	[] -> output_string stdout ""
	|e::l -> begin output_string stdout e; output_string stdout "\n" ; printlist l end

let rec printlistref li= match li with 
	[] -> output_string stdout ""
	|e::l -> begin output_string stdout !e; output_string stdout "\n" ; printlistref l end
	

	


(* module XMLOrange = Orange.Maker(MonList) *)

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
type compInfo = {name:string; absStore: typeListeAS; compES:listeDesES; expBornes:TreeList.tree}


let myArgs: myArgs_t list ref = ref []


let myComps: compInfo list ref = ref []

let partial = ref false

let existsPartialResult _ = false

module PartialAdapter = 
  functor (Listener : LISTENER) ->
  struct
    type t = Listener.t
    let null = Listener.null
    let onBegin = Listener.onBegin
    let onEnd = Listener.onEnd
    let onFunction = Listener.onFunction
    let onFunctionEnd = Listener.onFunctionEnd
    let onCall res name numCall line source inloop executed extern = 
      if (extern) then
        let partialResult = getPartialResult name in
	applyPartialResult partialResult res
       else
        Listener.onCall res name numCall line source inloop executed extern
      
    let onReturn = Listener.onReturn
    let onLoop = Listener.onLoop
    let onLoopEnd = Listener.onLoopEnd
    
  end;;


module TO = Orange.Maker(PartialAdapter(TreeList))
module XO = Orange.Maker(PartialAdapter(Orange.MonList))

(* open TO   *)


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
	("-c", Arg.String (fun def -> (myArgs := (COMP def) :: !myArgs ; partial := true)),
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
  

(**
 * Build the partial results for functions which are marked as component.
 * @param fctList The list of functions of the program
 * @return The list of computed partial results (in the same order)
 *)  



 
let rec getComps  = function
   [] -> ()
  |(_,fn)::r -> getComps r;
           if (isComponent fn.nom) 
           then
             begin
               printf "Evalue le resultat partiel pour: %s\n" fn.nom;
       
               globalesVar := !alreadyAffectedGlobales;
               let typeE = TO.TFONCTION(fn.nom,!TO.numAppel, fn.lesAffectations, [], [], [], [],  [], true, false) in
               TO.dernierAppelFct := typeE;
               TO.predDernierAppelFct := typeE;
               let (_,_) = TO.evaluerFonction (fn.nom) fn !listeASCourant  (EXP(NOTHING))   [typeE]  typeE true in () ;
               let compAS: abstractStore list = evalStore (new_instBEGIN fn.lesAffectations) [] in
               printf "..l'abstractStore fait %u entrees, affichage: \n"(List.length(compAS));
               afficherListeAS compAS;
               printf "\n";
               printf "..affichage des info. de boucles parametriques: \n";
               mainFonc := ref fn.nom;
               let (result, _) = TO.afficherInfoFonctionDuDocUML !TO.docEvalue.TO.maListeEval in
	       let fName = (fn.nom)^".rpo" in
	       printf "Stockage dans %s\n" fName;	       
	       let chan = Unix.out_channel_of_descr (Unix.openfile fName [Unix.O_WRONLY;Unix.O_TRUNC;Unix.O_CREAT] 0o644) in
	       let partialResult = {name=fn.nom; absStore=compAS; compES=(fn.listeES); expBornes=result} in
	       Marshal.to_channel chan partialResult [];
	       close_out chan 	       
(*	       to_channel {name=fn.nom; absStore=compAS; compES=(fn.listeES)}::reste *)
(*               print_string ("\nDEBUT\n"^result^"\nFIN\n");  *)
               
             end
           

let analysePartielle file =
 printf "Lance analyse_defs ...\n";
 TO.numAppel := 0;
 idBoucle := 0;
 idAppel:=0;
 nbImbrications := 0;
 TO.enTETE :=  false;
 TO.estNulEng :=  false;
 TO.estDansBoucle :=  false;	 
 analyse_defs file;
 printf "analyse_defs OK, maintenant lance evaluation des composants.\n";
 getComps !doc.laListeDesFonctions;
 print_string "OK, fini.\n"
  
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
 
			Analyser.printFile stdout safe_fileaux safe_fileaux;
	) in*)

	(*let filesmem = !files in*)
	Arg.parse opts add_file_and_name banner;
	(*printlist !list_file_and_name ;*)
	
	Cextraireboucle.sort_list_file_and_name !list_file_and_name;
	
	if (not !partial) then (
	  let hd=(! (List.hd (!Cextraireboucle.names))) and tl =(List.tl (!Cextraireboucle.names)) in
	  Cextraireboucle.maj hd tl
	);
	let a1 = !args in
				
				
	let a2 = List.filter (fun e ->  match e with LINE_RECORD _-> false |_-> true) a1 in			
				 
				let firstParse =
						(match (Frontc.parse  ((FROM_FILE (List.hd !Cextraireboucle.files)) :: a1)) with 
							PARSING_ERROR ->  []
							| PARSING_OK f2 -> 
							Rename.go (Frontc.trans_old_fun_defs  f2 )

								
							 ) in
				

				if (!partial) then (
		 		  TO.initref stdout firstParse
				) else (
				  XO.initref stdout firstParse
				);
		
				(*Cprint.print stdout firstParse ; (*plante avec l'option -l*)*)
				let secondParse =
						(match Frontc.parse  ((FROM_FILE (List.hd !Cextraireboucle.files)) :: a2) with 
							PARSING_ERROR ->  []
							| PARSING_OK f2 -> 

							Rename.go(Frontc.trans_old_fun_defs  f2 )  ) in

				
				(*Analyser.initref stdout secondParse;*)
				(* analysePartielle secondParse; *)
				if (!partial) then 
				begin
				  analysePartielle secondParse
				end				
				else
				begin
				  print_string (XO.printFile stdout secondParse)
				end;
				



                              (* Close the output if needed *)
                              if close then close_out output
