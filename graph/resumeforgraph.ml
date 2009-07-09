(* resumeforgraph -- dot file for graph drawing
**
** Project:	O_Range
** File:	resumeforgraph.ml
** Version:	1.1
** Date:	11.7.2008
** Author:	Marianne de Michiel
*)

open Cextraireboucle 
open Cvarabs
open Printf
(*open Cevalexpression*)
 

 
let callsList = ref []


(* body ifnumber loopnumber callnumber assignmentnumber calllist *)
let rec getFunctionNumbers  body ifn ln cl an clist onlyonecall=
if body = [] then (ifn, ln, cl, an ,clist, onlyonecall) 
else
begin
	let (first, next) = (List.hd body, List.tl body) in
	match first with 
		VAR (_, exp) 
		| TAB (_, _, exp) 
		|  MEMASSIGN ( _, _, exp)	->	 (*+1 but it aslo may be a struct*)
			let (nextifn, nnextln, nnextcl,nnextan, nnextclist, nnextonlyonecall ) = getFunctionNumbers  next 0 0 0 0 clist onlyonecall in

			(ifn + nextifn, ln + nnextln, cl +nnextcl , an+1+nnextan ,nnextclist, nnextonlyonecall) 

		| BEGIN liste -> 
			let (n1ifn, n1ln, n1cl,n1an, n1clist, n1onlyonecall ) = getFunctionNumbers  liste 0 0 0 0 clist onlyonecall in
			let (nextifn, nnextln, nnextcl,nnextan, nnextclist, nnextonlyonecall ) = getFunctionNumbers  next 0 0 0 0 n1clist n1onlyonecall in
			(ifn+n1ifn+nextifn, ln+n1ln+nnextln, n1cl+cl+nnextcl, an+n1an+nnextan, nnextclist, nnextonlyonecall)
		| IFVF (_, i1, i2) ->			
			let (n1ifn, n1ln, n1cl, n1an, n1clist, n1onlyonecall ) = getFunctionNumbers  [i1] 0 0 0 0 clist onlyonecall in
			let (n2ifn, n2ln, n2cl, n2an, n2clist , n2onlyonecall ) = getFunctionNumbers  [i2] 0 0 0 0  n1clist n1onlyonecall in
			let (nextifn, nnextln, nnextcl,nnextan, nnextclist, nnextonlyonecall ) = getFunctionNumbers  next 0 0 0 0 n2clist n2onlyonecall in
			(ifn + n1ifn +n2ifn +1+nextifn, ln + n1ln + n2ln+nnextln, cl + n1cl + n2cl +nnextcl, an+n1an +n2an+nnextan,  nnextclist, nnextonlyonecall) 	 
					
		| IFV ( _, i1) 		->(*Printf.printf "evalStore if TRUE \n"; *)
			let (n1ifn, n1ln, n1cl,n1an, n1clist, n1onlyonecall ) = getFunctionNumbers  [i1] 0 0 0 0 clist onlyonecall in
			let (nextifn, nnextln, nnextcl,nnextan, nnextclist, nnextonlyonecall ) = getFunctionNumbers  next 0 0 0 0 n1clist n1onlyonecall in
			(ifn+n1ifn+1+nextifn, ln+n1ln+nnextln, n1cl+cl +nnextcl, an+n1an+nnextan, nnextclist, nnextonlyonecall)	 
					
		| FORV (_,_, _, _, _, _, inst)	-> 
			let (n1ifn, n1ln, n1cl,n1an, n1clist, n1onlyonecall ) = getFunctionNumbers  [inst] 0 0 0 0 clist onlyonecall in
			let (nextifn, nnextln, nnextcl,nnextan, nnextclist, nnextonlyonecall ) = getFunctionNumbers  next 0 0 0 0 n1clist n1onlyonecall in
			(ifn+n1ifn+nextifn, ln+n1ln +1+nnextln, n1cl+cl +nnextcl, an+n1an+nnextan, nnextclist, nnextonlyonecall)
	 
		| APPEL (n,e,nomFonc,s,corpsAbs,varB,rename)->

		let (nextifn, nnextln, nnextcl,nnextan, nnextclist, nnextonlyonecall ) = getFunctionNumbers  next 0 0 0 0 clist onlyonecall in
		(ifn+nextifn, ln+nnextln, cl + 1 +nnextcl, an +nnextan, List.append [nomFonc] nnextclist , if List.mem nomFonc nnextonlyonecall then nnextonlyonecall else List.append [nomFonc] nnextonlyonecall)
end	
 

let rec getnb name clist =
if clist = [] then 0
else if List.mem name clist = false then 0
	 else 
	 	if name = List.hd clist then 1 + getnb name (List.tl clist) else getnb name (List.tl clist)

let consnbCallList n1clist n1onlyonecall =
List.map (fun name -> (name, getnb name n1clist))n1onlyonecall 


let  getInfoFunctions  docu	= (* from each function or only from an entry point ?? for the moment for each *)
List.iter(fun (_,info) -> 
		let (name,assign) = (info.nom, info.lesAffectations) in
		let (n1ifn, n1ln, n1cl,n1an, n1clist, n1onlyonecall ) = getFunctionNumbers  assign 0 0 0 0 [] [] in
  		if assign = [] then Printf.printf "%s corps vide \n" name;
 
  		callsList := List.append [(name, n1ifn, n1ln, n1cl,n1an, consnbCallList n1clist n1onlyonecall )]  !callsList

)!docu.laListeDesFonctions

let rec printcallslist namecalling l =
List.iter(fun (name, number)->
Printf.printf "%s->%s [label=\"%d\"]\n" namecalling name number
(*Printf.printf "\t->\t%d calls of %s\n" number name ;*)
)l



let existFunction name l  =  List.exists(fun (n, _, _, _, _, _ ) -> n = name)l

let getFunction name l = List.find(fun (n, _, _, _, _, _ ) -> n = name)l


let listAlreadyNodeFunction = ref []




let rec getPartialgraph name l=
   if existFunction name l then
   begin
		let (name, n1ifn, n1ln, n1cl,n1an, n1assignFuncNameNbCalls ) = getFunction name l in
		 listAlreadyNodeFunction := List.append [name] !listAlreadyNodeFunction;
	 	 Printf.printf "%s [shape=box, label=\"%s (if=%d loops=%d functionCalls=%d assign=%d)\"]\n" name name n1ifn n1ln n1cl n1an;
		 (*Printf.printf "Function : %s ( %d if, %d loops, %d function calls, %d assignments)\n" name n1ifn n1ln n1cl n1an;*)
		 if n1assignFuncNameNbCalls != [] then
		 begin
            completeSubGraph n1assignFuncNameNbCalls  l ;
			(*[subgraph name] { statement‐list }*)
			(*Printf.printf "[subgraph %s] {\n" name ;*)
			printcallslist name n1assignFuncNameNbCalls;
			(*Printf.printf "}\n" *)
		end
  end
and  completeSubGraph subgraph l =
	List.iter (fun (name, _)->
	if List.mem name !listAlreadyNodeFunction = false && existFunction name l then
	begin
			let (name, n1ifn, n1ln, n1cl,n1an, n1assignFuncNameNbCalls ) = getFunction name l in
			Printf.printf "%s [shape=box, label=\"%s (if=%d loops=%d functionCalls=%d assign=%d)\"]\n" name name n1ifn n1ln n1cl n1an;
			listAlreadyNodeFunction := List.append [name] !listAlreadyNodeFunction;
			completeSubGraph n1assignFuncNameNbCalls  l ;
			(*[subgraph name] { statement‐list }*)
			(*Printf.printf "[subgraph %s] {\n" name ;*)
			printcallslist name n1assignFuncNameNbCalls;
	end
) subgraph

let getAllgraph l=
  List.iter (fun (name, n1ifn, n1ln, n1cl,n1an, n1assignFuncNameNbCalls ) -> 
		 
	 	Printf.printf "%s [shape=box, label=\"%s (if=%d loops=%d functionCalls=%d assign=%d)\"]\n" name name n1ifn n1ln n1cl n1an;
		(*Printf.printf "Function : %s ( %d if, %d loops, %d function calls, %d assignments)\n" name n1ifn n1ln n1cl n1an;*)
		if n1assignFuncNameNbCalls != [] then
		begin
			(*[subgraph name] { statement‐list }*)
			(*Printf.printf "[subgraph %s] {\n" name ;*)
			printcallslist name n1assignFuncNameNbCalls;
			(*Printf.printf "}\n" *)
		end
	)l

let resume secondParse complet=
analyse_defs secondParse;
  getInfoFunctions doc;
 
Printf.printf "digraph \"\" {\ncenter=1;\n{\n\t node [shape=plaintext, fontsize=12];\n}\n";
if complet then getAllgraph !callsList else (listAlreadyNodeFunction := []; getPartialgraph !(!mainFonc) !callsList);
(*  List.iter (fun (name, n1ifn, n1ln, n1cl,n1an, n1assignFuncNameNbCalls ) -> 
		 
	 	Printf.printf "%s [shape=box, label=\"%s (if=%d loops=%d functionCalls=%d assign=%d)\"]\n" name name n1ifn n1ln n1cl n1an;
		(*Printf.printf "Function : %s ( %d if, %d loops, %d function calls, %d assignments)\n" name n1ifn n1ln n1cl n1an;*)
		if n1assignFuncNameNbCalls != [] then
		begin
			(*[subgraph name] { statement‐list }*)
			(*Printf.printf "[subgraph %s] {\n" name ;*)
			printcallslist name n1assignFuncNameNbCalls;
			(*Printf.printf "}\n" *)
		end


	)!callsList;*)

	
Printf.printf "\n}";
   ;;
