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
open Tod
(*open Cevalexpression*)
 


(* node box are 
	  GREEN when function containt only assign but no loop no call and no if type ONLYASSIGN
	| BLUE when function containt only assign and if but no loop no call  type ONLYASSIGNANDIF
	| RED when function containt LOOPWITHCALL 
	| BLACK in all the others cases
note font is BLACK but when the function contain loop without call it become RED
edges are labeled with 3 numbers total number of calls, nomber of calls into a loop, number of calls into a if
edges are BLACK but when the number of calls into if is not 0 it became RED


the assign number od loop is affected by a fixedPointCoef coefficient not  good defined
*)

let fixedPointCoef = 2
let undifinedFunctioncost = 1



let listAlreadyNodeFunction = ref []
let listOfFunctionWithLoop = ref []


let graph = ref (Digraph("", false, []))

type typeFunction =
	  ONLYASSIGN
	| ONLYASSIGNANDIF
	| LOOPWITHCALL 
	| OTHERCALLORLOOP 

type politic =
	ALLFUNCTION
	| ONLYNOTPESSIMISTIC
	| WITHVALUE of int


type colors =
	  GREEN
	| BLUE
	| RED 
	| BLACK

let getColorValue color =
match color with
	GREEN   ->   "#00ff00"
	| BLUE  ->   "#0000ff"
	| RED   ->   "#ff0000"
	| BLACK ->   "#000000"


let callsList = ref  []
let callsListEval = ref []
let callsListNumbers = ref []


let getTypeAndBoxColor ifn ln cn an lVide=
if lVide  then
	if cn = 0 && ln =0 then 
		if ifn = 0 then  (ONLYASSIGN, getColorValue GREEN)
		else (ONLYASSIGNANDIF, getColorValue BLUE)
	else (OTHERCALLORLOOP,  getColorValue BLACK)
else (LOOPWITHCALL,  getColorValue RED)


let dot_sizes = ref []
(* Write the .size file *)
let append_to_dot_size fun_name size has_loop =
    let filename = Filename.concat (!Cextraireboucle.out_dir) ".size" in
    let chan = (if  not (Sys.file_exists filename)
        then open_out filename
        else open_out_gen [Open_append] 0 filename) in
    let _ = Printf.fprintf chan "%s\t\t%d\t\t%B\n" fun_name size has_loop in
    close_out chan

(* Read the .size file *)
let read_dot_size = fun _ ->
    let filename = Filename.concat (!Cextraireboucle.out_dir) ".size" in
    let sizes = ref [] in
    let chan = open_in filename in
    try
        while true; do
            sizes := (Scanf.sscanf (input_line chan) "%s %d %B"
                        (fun name size loop -> (name, size, loop))
                    ) :: !sizes
        done; []
    with End_of_file ->
        close_in chan; !sizes

(* get (size, has_loop) from the .size file
    Return size = -1 if not found in the file
*)
let rec get_dot_size sizes fun_name =
    match sizes with
        | (name, size, loop) :: t ->
            if (name = fun_name)
                then (size, loop)
                else get_dot_size t fun_name
        | [] -> (-1, false)


(* body ifnumber loopnumber callnumber assignmentnumber calllist isintoloop isintiif callsintoloop callsintoif *)
let rec getFunctionNumbers  body ifn ln cl an clist onlyonecall   inloop inif callsinloop callsinif=
if body = [] then (ifn, ln, cl, an ,clist, onlyonecall, inloop, inif, callsinloop, callsinif) 
else
begin
	let (first, next) = (List.hd body, List.tl body) in
	match first with 
		VAR (_, exp) 
		| TAB (_, _, exp) 
		|  MEMASSIGN ( _, _, exp)	->	 (*+1 but it aslo may be a struct*)
			let (nextifn, nnextln, nnextcl,nnextan, nnextclist, nnextonlyonecall, _, _, ncallsinloop, ncallsinif ) = getFunctionNumbers  next 0 0 0 0 clist onlyonecall inloop inif callsinloop callsinif in

			(ifn + nextifn, ln + nnextln, cl +nnextcl , an+1+nnextan ,nnextclist, nnextonlyonecall, inloop, inif, ncallsinloop, ncallsinif) 

		| BEGIN liste -> 
			let (n1ifn, n1ln, n1cl,n1an, n1clist, n1onlyonecall,_, _, n1callsinloop, n1callsinif ) = getFunctionNumbers  liste 0 0 0 0 clist onlyonecall  inloop inif callsinloop callsinif in
			let (nextifn, nnextln, nnextcl,nnextan, nnextclist, nnextonlyonecall,_, _, n2callsinloop, n2callsinif ) = getFunctionNumbers  next 0 0 0 0 n1clist n1onlyonecall inloop inif n1callsinloop n1callsinif  in
			(ifn+n1ifn+nextifn, ln+n1ln+nnextln, n1cl+cl+nnextcl, an+n1an+nnextan, nnextclist, nnextonlyonecall,inloop, inif, n2callsinloop, n2callsinif)
		| IFVF (_, i1, i2) ->			
			let (n1ifn, n1ln, n1cl, n1an, n1clist, n1onlyonecall, _, _, n1callsinloop, n1callsinif  ) = getFunctionNumbers  [i1] 0 0 0 0 clist onlyonecall inloop true callsinloop callsinif in
			let (n2ifn, n2ln, n2cl, n2an, n2clist , n2onlyonecall,_, _, n2callsinloop, n2callsinif  ) = getFunctionNumbers  [i2] 0 0 0 0  n1clist n1onlyonecall inloop true n1callsinloop n1callsinif in
			let (nextifn, nnextln, nnextcl,nnextan, nnextclist, nnextonlyonecall, _,_, nextcallsinloop, nextcallsinif) = getFunctionNumbers next 0 0 0 0 n2clist n2onlyonecall inloop inif n2callsinloop n2callsinif in
			(ifn + n1ifn +n2ifn +1+nextifn, ln + n1ln + n2ln+nnextln, cl + n1cl + n2cl +nnextcl, an+n1an +n2an+nnextan,  nnextclist, nnextonlyonecall,inloop,inif, nextcallsinloop, nextcallsinif) 	 
					
		| IFV ( _, i1) 		->(*Printf.printf "evalStore if TRUE \n"; *)
			let (n1ifn, n1ln, n1cl,n1an, n1clist, n1onlyonecall,_, _, n1callsinloop, n1callsinif ) = getFunctionNumbers  [i1] 0 0 0 0 clist onlyonecall  inloop true callsinloop callsinif in
			let (nextifn, nnextln, nnextcl,nnextan, nnextclist, nnextonlyonecall, _,_, nextcallsinloop, nextcallsinif ) = getFunctionNumbers next 0 0 0 0 n1clist n1onlyonecall inloop inif n1callsinloop n1callsinif in
			(ifn+n1ifn+1+nextifn, ln+n1ln+nnextln, n1cl+cl +nnextcl, an+n1an+nnextan, nnextclist, nnextonlyonecall,inloop,inif, nextcallsinloop, nextcallsinif)	 
					
		| FORV (_,_, _, _, _, _, inst)	-> 
			let (n1ifn, n1ln, n1cl,n1an, n1clist, n1onlyonecall, _, _, n1callsinloop, n1callsinif ) = getFunctionNumbers  [inst] 0 0 0 0 clist onlyonecall  true inif callsinloop callsinif in
			let (nextifn, nnextln, nnextcl,nnextan, nnextclist, nnextonlyonecall,_, _, nextcallsinloop, nextcallsinif ) = getFunctionNumbers  next 0 0 0 0 n1clist n1onlyonecall  inloop inif n1callsinloop n1callsinif in
			(ifn+n1ifn+nextifn, ln+n1ln +1+nnextln, n1cl+cl +nnextcl, an+n1an*fixedPointCoef+nnextan, nnextclist, nnextonlyonecall,inloop, inif, nextcallsinloop, nextcallsinif )
	 
		| APPEL (n,e,nomFonc,s,corpsAbs,varB,rename)->

		let (nextifn, nnextln, nnextcl,nnextan, nnextclist, nnextonlyonecall,_,_ ,nextcallsinloop, nextcallsinif  ) = getFunctionNumbers  next 0 0 0 0 clist onlyonecall inloop inif callsinloop callsinif in
		(ifn+nextifn, ln+nnextln, cl + 1 +nnextcl, an +nnextan, List.append [nomFonc] nnextclist , (if List.mem nomFonc nnextonlyonecall then nnextonlyonecall else List.append [nomFonc] nnextonlyonecall),
		  inloop, inif, 
		  ( if inloop then List.append [nomFonc] nextcallsinloop else nextcallsinloop),
		  (if inif then List.append [nomFonc] nextcallsinif else nextcallsinif) )
end	
 

let rec getnb name clist =
if clist = [] then 0
else if List.mem name clist = false then 0
	 else 
	 	if name = List.hd clist then 1 + getnb name (List.tl clist) else getnb name (List.tl clist)


let consnbCallList clist onlyonecall cinl cini=
List.map (fun name -> (name, (getnb name clist, getnb name cinl, getnb name cini )))onlyonecall 


let  getInfoFunctions  docu	= (* from each function or only from an entry point ?? for the moment for each *)
List.iter(fun (_,info) -> 
		let (name,assign) = (info.nom, info.lesAffectations) in
		let (n1ifn, n1ln, n1cl,n1an, n1clist, n1onlyonecall,_,_, cinl,cini ) = getFunctionNumbers  assign 0 0 0 0 [] [] false false [] [] in
  		if assign = [] then Printf.printf "%s corps vide \n" name;
 		let (typeF, color ) = getTypeAndBoxColor n1ifn n1ln n1cl n1an (cinl=[]) in
		let fontColor =  if typeF = OTHERCALLORLOOP && n1ln != 0 then  ( if List.mem name !listOfFunctionWithLoop = false then listOfFunctionWithLoop := List.append [name] !listOfFunctionWithLoop; getColorValue RED )
						 else getColorValue BLACK in (*NFontColor*)
		 
  		callsList := List.append [ name, n1ifn, n1ln, n1cl,n1an, consnbCallList n1clist n1onlyonecall cinl cini, color, fontColor, typeF, n1onlyonecall]  !callsList
(*callsList := List.append [ name, n1ifn, n1ln, n1cl,n1an, consnbCallList n1clist n1onlyonecall cinl cini, color]  !callsList*)


)!docu.laListeDesFonctions

let existFunction name l  =  List.exists(fun (n, _, _, _, _, _ ,_,_,_,_) -> n = name)l

let getFunction name l = List.find(fun (n, _, _, _, _, _ ,_,_,_,_) -> n = name)l

let existFunctionEval name l  =  List.mem_assoc  name l

let getFunctionAssosSize name l = List.assoc name l

let partialised = ref []
let getFunctionSize name l = 	if existFunctionEval name  l then 
								if List.mem name !partialised then ((getFunctionAssosSize name l)*3/100) else getFunctionAssosSize name l 
							else undifinedFunctioncost







let rec alldef fl =
if fl = [] then true else if existFunction (List.hd fl) !callsList = false  then  alldef (List.tl fl) else existFunctionEval (List.hd fl)  !callsListEval && alldef (List.tl fl)


let existFunctionEvalNumbers name l  =  List.exists(fun (n, _, _,_,_) -> n = name)l

let getFunctionAssosNumbers name l = List.find (fun (n, _, _,_,_) -> n = name)l


let getFunctionNumbersaux name l = if existFunctionEvalNumbers name  l then getFunctionAssosNumbers name l else (name, 0,0,0, false)

let getFunctionCallFromTo calling call  = 
let (_, _, _, _,_, clist, _, _,_,_ ) = getFunction calling !callsList in
List.assoc call clist 



let rec getSizeEachcall  funcNameNbCalls =
if funcNameNbCalls = [] then 0
else
begin
	let   ((name,(numberTotal, nbinloop,nbinif)), next) = (List.hd funcNameNbCalls, List.tl funcNameNbCalls) in
	let initSize = getFunctionSize name !callsListEval in
	 getSizeEachcall next + nbinloop*fixedPointCoef*initSize + (numberTotal - nbinloop)*initSize
	
end


let newcurrentcallslist = ref []
let newcurrentNumberlist = ref []



let rec evalCallList currentcallslist =
if currentcallslist != [] then
begin
	 let (first, next) =(List.hd currentcallslist , List.tl currentcallslist ) in
		(match first with
			
		   (name, ifn, ln, cl,an, funcNameNbCalls, x, y ,typeF,fl) -> 
			if existFunctionEval name !callsListEval = false then
			begin
				(
					match typeF with 
							ONLYASSIGN -> callsListEval := List.append [(name,an)] !callsListEval ; 
						| 	ONLYASSIGNANDIF -> callsListEval := List.append [(name,an + ifn)] !callsListEval ; 
						| 	LOOPWITHCALL ->
							    if List.mem name !listOfFunctionWithLoop = false then listOfFunctionWithLoop := List.append [name] !listOfFunctionWithLoop; 			
								if alldef fl then 
									callsListEval := List.append [(name,an + ifn + (getSizeEachcall  funcNameNbCalls) )] !callsListEval 
								else (newcurrentcallslist := List.append [first] !newcurrentcallslist;)

						| 	OTHERCALLORLOOP ->
								if alldef fl then 
									callsListEval := List.append [(name,an + ifn + (getSizeEachcall  funcNameNbCalls) )] !callsListEval 
								else (newcurrentcallslist := List.append [first] !newcurrentcallslist;)
								
				)	 
			end);
		evalCallList next;
		let functionnoteval = !newcurrentcallslist in
		newcurrentcallslist := [];
(*Printf.printf "number of function %d \n" !numberofFunctionEval;*)
		evalCallList functionnoteval;

end





let listAssosFonctioNameNBCalls = ref []



let rec evalCallListNumbers  partial listAssosFonctioNameNBCalls=
(* listAlreadyNodeFunction *)
if listAssosFonctioNameNBCalls != [] then
begin
	 let (first, next) =(List.hd listAssosFonctioNameNBCalls , List.tl listAssosFonctioNameNBCalls ) in
		(match first with
			
		   (name, (_,_,fl,endofred)) -> 
		    let tofind =	 partial && List.mem name !listAlreadyNodeFunction || partial = false in
			if tofind && existFunctionEvalNumbers name !callsListNumbers = false  then
			begin
				(
								if alldefNumbers  fl partial then 
								(   let (numberTotal, nbinloop,add,e) = getTotalCallsNumbers fl name  in
									callsListNumbers := List.append [name,numberTotal, nbinloop,add,endofred||e] !callsListNumbers 
								)
								else (newcurrentNumberlist := List.append [first] !newcurrentNumberlist;)
								
				)	 
			end);
		evalCallListNumbers  partial next;
		let functionnoteval = !newcurrentNumberlist in
		newcurrentNumberlist := []; 
		evalCallListNumbers  partial functionnoteval;

end




and getTotalCallsNumbers fl name  =
if fl = [] then (0,0,0,false)
else
begin
	let (id, next) = (List.hd fl, List.tl fl) in
	let (numberTotal, nbinloop,_) = getFunctionCallFromTo id name   in
	let (_,idCallNumber, idloopCallNumber, add,endofred) = getFunctionNumbersaux id !callsListNumbers in
	let (nexttotal, nextloop,nextall,redpred) = getTotalCallsNumbers next name  in
	(idCallNumber*numberTotal+nexttotal, (idCallNumber - idloopCallNumber)*nbinloop + idloopCallNumber *numberTotal +nextloop,idloopCallNumber*nbinloop + add *(idCallNumber - idloopCallNumber)+add*2* nbinloop+nextall,endofred||redpred)
end
and alldefNumbers fl partial =

if fl = [] then true 
else 
	if partial = false then 
		if existFunction (List.hd fl) !callsList = false  then alldefNumbers (List.tl fl) partial

		else existFunctionEvalNumbers (List.hd fl)  !callsListNumbers && alldefNumbers (List.tl fl) partial
	else
	begin
		if existFunction (List.hd fl) !callsList = false  || List.mem (List.hd fl) !listAlreadyNodeFunction  = false then   alldefNumbers (List.tl fl) partial

		else existFunctionEvalNumbers (List.hd fl)  !callsListNumbers && alldefNumbers (List.tl fl) partial
	end



let rec printcallslist namecalling l =
List.iter(fun (name,(numberTotal, nbinloop,nbinif))->
let (edgeColor,isendofrededge) = if nbinif != 0 then (getColorValue RED,true) else (getColorValue BLACK, false) in (*EColor*)
if List.mem_assoc name !listAssosFonctioNameNBCalls then
begin
	let (nbcall,nbloopcall,listcalls,er)=List.assoc name !listAssosFonctioNameNBCalls in
	if List.mem namecalling listcalls = false then
		listAssosFonctioNameNBCalls := List.map(fun x->
												 let (n,(nbcall,nbloopcall, listcalls,endofrededge))  = x in
												 if n = name then (name,(numberTotal+nbcall,nbinloop+nbloopcall, List.append [namecalling] listcalls, isendofrededge ||endofrededge||er )) else x) !listAssosFonctioNameNBCalls
end
else listAssosFonctioNameNBCalls := List.append [(name,(numberTotal,nbinloop,[namecalling],isendofrededge))] !listAssosFonctioNameNBCalls;

graph := Tod.add_edge_lc !graph namecalling name ((string_of_int numberTotal)^","^(string_of_int nbinloop)^","^(string_of_int nbinif)) edgeColor
)l


 



let rec getPartialgraph name l =
   if existFunction name l then
   begin
		let (name, n1ifn, n1ln, n1cl,n1an, n1assignFuncNameNbCalls, color, fontColor,_,_ ) = getFunction name l in
		 
		 listAlreadyNodeFunction := List.append [name] !listAlreadyNodeFunction;
		 callsListNumbers :=  [ name,  1, 0 ,0,false] ;
		 let comment = Printf.sprintf "(if=%d loop=%d call=%d assign=%d size=%d)"  n1ifn n1ln n1cl n1an (getFunctionSize name !callsListEval) in
		 graph := (Tod.add_node_a (!graph) name [NShape("box"); NLabel( name^" "^comment);NColor color ; NFontColor fontColor]);
		 if n1assignFuncNameNbCalls != [] then
		 begin
            completeSubGraph n1assignFuncNameNbCalls  l ;
			printcallslist name n1assignFuncNameNbCalls;
		end
  end
and  completeSubGraph subgraph l =
	List.iter (fun (name, _)->
	if List.mem name !listAlreadyNodeFunction = false && existFunction name l then
	begin

			let (name, n1ifn, n1ln, n1cl,n1an, n1assignFuncNameNbCalls, color , fontColor,_,_ ) = getFunction name l in
			let comment = Printf.sprintf "(if=%d loop=%d call=%d assign=%d size=%d)"  n1ifn n1ln n1cl n1an (getFunctionSize name !callsListEval) in
			let (p_size, p_has_loop) = get_dot_size !dot_sizes name in
			let comment = (if (p_size = -1)
		 		then comment
		 		else comment ^ Printf.sprintf " (partialization: size=%d has loops=%B)" p_size p_has_loop) in

			graph := Tod.add_node_a !graph name [NShape("box"); NLabel(name^" "^comment);NColor color; NFontColor fontColor];

(*			(*graph := Tod.add_node_a !graph name [NShape("box"); NLabel(Printf.sprintf "%s (if=%d loops=%d functionCalls=%d assign=%d)" name n1ifn n1ln n1cl n1an);NColor color; NFontColor fontColor];*)
			graph := Tod.add_node_a !graph name [NShape("box"); NLabel(Printf.sprintf "%s" name); NComment(Printf.sprintf "if=%d loops=%d functionCalls=%d assign=%d)"  n1ifn n1ln n1cl n1an);NColor color; NFontColor fontColor];*)

			listAlreadyNodeFunction := List.append [name] !listAlreadyNodeFunction;
			completeSubGraph n1assignFuncNameNbCalls  l ;
			printcallslist name n1assignFuncNameNbCalls;
	end
) subgraph

let getAllgraph l=

callsListNumbers :=  [ !(!mainFonc),  1, 0 ,0 ,false] ;
  List.iter (fun (name, n1ifn, n1ln, n1cl,n1an, n1assignFuncNameNbCalls, color, fontColor,_,_ ) -> 
		let comment = Printf.sprintf "(if=%d loop=%d call=%d assign=%d size=%d)"  n1ifn n1ln n1cl n1an (getFunctionSize name !callsListEval) in
		graph := Tod.add_node_a (!graph) name [NShape("box"); NLabel(name^"\n"^comment);NColor color; NFontColor fontColor];

		if n1assignFuncNameNbCalls != [] then
		begin
			printcallslist name n1assignFuncNameNbCalls;
		end
	)l

let resumeString =ref ""

let biggesteString =ref ""
let currentChoosenNode = ref []
let nextChoosenNode = ref []


let rec allNotChosen allChoosen onecall =
if onecall = [] then true else  List.mem_assoc (List.hd onecall) allChoosen = false &&  allNotChosen allChoosen (List.tl onecall) 

let rec allClassifiedSubFunction allChoosen onecall classifiedFunction =
if onecall = [] then true else  
	if List.mem_assoc (List.hd onecall) allChoosen = false then allClassifiedSubFunction allChoosen  (List.tl onecall) classifiedFunction
	else if List.mem (List.hd onecall) classifiedFunction then allClassifiedSubFunction allChoosen  (List.tl onecall) classifiedFunction else false


(* to be call when allClassifiedSubFunction is true *)
let rec getclass allChoosen onecall classNumber =
if onecall = [] then classNumber 
else  
	if List.mem_assoc (List.hd onecall) allChoosen = false then getclass allChoosen (List.tl onecall) classNumber
	else
		max (List.assoc  (List.hd onecall)  !nextChoosenNode)  (getclass allChoosen (List.tl onecall) classNumber)



let mayBeClassified name oneCall classifiedList allChoosen classifiedFunction =
if allNotChosen allChoosen oneCall then (true, -1)
else if allClassifiedSubFunction allChoosen oneCall classifiedFunction then (true, getclass allChoosen oneCall 0)
	 else (false,0) 




let rec classified allChoosen notClassified (classifiedList:(int * string list) list) cl classifiedFunction l=
if notClassified = [] then (classifiedList, notClassified, classifiedFunction)
else
begin
	let (first, next) = (List.hd notClassified, List.tl notClassified) in
	let (name,totalSize) = first in
	let (_, _, _, _,_, _, _ , _,_,onecall) = getFunction name cl in
			(*biggesteString:=!biggesteString^Printf.sprintf "%s   totalsize %d\n" name  totalSize; *)
	let (mayBe, maxClassNumberOfSubFunction) = mayBeClassified name onecall classifiedList allChoosen classifiedFunction in
	let (newclassifiedList, newnotClassified, newclassifiedFunction) =
		if mayBe then 
		(
			let newNb =  maxClassNumberOfSubFunction +1 in
			nextChoosenNode := List.append [(name,newNb )] !nextChoosenNode;
			
			let nextClassifiedList = if List.mem_assoc newNb classifiedList then 
				(List.map(fun (n,l)-> if n = newNb then (n, List.append [name] l) else (n,l) )classifiedList) 
				else List.append [newNb,[name]] classifiedList in
			classified allChoosen next nextClassifiedList cl (List.append [name] classifiedFunction) l

		)
		else classified allChoosen next classifiedList cl   classifiedFunction l
	in
	if mayBe then classified allChoosen newnotClassified newclassifiedList cl newclassifiedFunction l
	else classified allChoosen (List.append [first] newnotClassified) newclassifiedList cl newclassifiedFunction l			
end




let getNewEval n (classifiedList:(int * string list) list) cl currentClassifiedOfLevel=

List.iter(fun name ->partialised := List.append [name] !partialised) currentClassifiedOfLevel ;
if List.mem_assoc n classifiedList then
begin
	let listLeval = List.assoc n classifiedList in
	List.map(fun (name,value)-> 
		if List.mem name  listLeval then 
		begin
  		 
			let (_, ifn, _, _,an, funcNameNbCalls,_, _ ,_,_) = getFunction name cl in
			(name, an + ifn + (getSizeEachcall  funcNameNbCalls) ) 
		end
		else (name,value)

	)!callsListEval
end
else !callsListEval


let currentLevelChoosenNode = ref []
let maybepessimisticloopcall = ref []

(* may are the node of n level source of pessimism and for with functions *)
let rec  getPessimisList  listLeval listpessimistic cl =
	if listLeval = [] || listpessimistic = [] then []
	else
	begin
		let (name, next) = (List.hd listLeval, List.tl listLeval) in
		if existFunction name cl then
		begin
			 let (_, _, _, _,_, funcNameNbCalls,_, _ ,_,_) = getFunction name cl in
		 	 if funcNameNbCalls != [] then
			 begin
				let nextList = getNextCalls cl funcNameNbCalls [] false in
			 	let inter = getInter nextList listpessimistic in
	             (* biggesteString:=!biggesteString^Printf.sprintf "\nnext of %s\n" name; (* sauf si pas d'arcs rouge entre les deux *)
								 
									  List.iter(fun (n,b)->  biggesteString:=!biggesteString^Printf.sprintf "\t\t%s\n" n)nextList  ;  *)    
								 
			 	if inter = [] then getPessimisList next listpessimistic cl 
			 	else List.append [name, inter] (getPessimisList next listpessimistic cl)
			 end 
			else	getPessimisList next listpessimistic cl 
		end
		else getPessimisList next listpessimistic cl 
	end


and getNextCalls cl fc res intoif=
if fc = [] then res
else
begin
	let (first, next) = (List.hd fc, List.tl fc) in
	let (nameSucc,(_, _,ifn)) = first in
	let isintoIf = ifn>0 || intoif in
	if existFunction nameSucc cl then
	begin
		let (_, _, _, _,_, nfc,_, _ ,_,_) = getFunction nameSucc cl in

		
		let getfirstbranchres = (getNextCalls cl nfc [nameSucc, intoif] isintoIf)  in
		getUnion( getUnion getfirstbranchres (getNextCalls  cl next [] intoif)) res
	end
	else getUnion( getUnion [nameSucc, isintoIf] (getNextCalls  cl next [] intoif)) res
end
and getInter l1 l2  =
	if l1 = [] || l2 = [] then []
	else
	begin
		let (first, next) = (List.hd l1, List.tl l1) in
		let (name, ini) = first in
		if List.mem name l2 then List.append [first] (getInter next l2) else (getInter next l2)
	end 
and getUnion l1 l2  =
	if l1 = [] then l2
	else if l2 = [] then l1
	else
	begin
		let (first, next) = (List.hd l1, List.tl l1) in
		let (name,isinoifinl) = first in
		if List.mem_assoc name l2 then 
			if isinoifinl = false then (getUnion next l2) else getUnion next (List.map(fun (n,b)-> if n =name then (n, true) else (n,b)) l2) 
		else List.append [first]  (getUnion next l2)
	end 


let  mayHaveListLevelNPessimisticnext  listpessimistic cl  currentLevelChoosen =
if listpessimistic = [] then []
else
	if currentLevelChoosen != [] then getPessimisList currentLevelChoosen listpessimistic cl
	else []

let rec chooseClassified n (classifiedList:(int * string list) list) cl l currentLevelChoosen pessimistic typeOfPartialisation=
let newCost = getNewEval (n+1) classifiedList cl currentLevelChoosen in
currentLevelChoosenNode:=[];
if List.mem_assoc (n+1) classifiedList then
begin
	biggesteString:=!biggesteString^Printf.sprintf "select level %d\n" (n+1); 
	List.iter (fun name ->
		let initsize = List.assoc name newCost in
		let (_,nbc,nbcil,fixed,endofred) = getFunctionAssosNumbers name l  in  
		let totalSize = ( nbcil*fixedPointCoef*initsize + (nbc - nbcil)*initsize + initsize *2 *fixed) in
		let mayBePessimistic = if List.mem name !listOfFunctionWithLoop && endofred then 
									(if List.mem name !maybepessimisticloopcall =false then  maybepessimisticloopcall:= List.append [name] !maybepessimisticloopcall; true) 
							   else false in
		(match typeOfPartialisation with
			ALLFUNCTION ->
				 
					
				if  (totalSize > 2500 || (mayBePessimistic && totalSize >1000)) 
				then (biggesteString:=!biggesteString^Printf.sprintf "\t%s   totalsize %d\n" name  totalSize ; currentLevelChoosenNode := List.append [name] !currentLevelChoosenNode)
						

		| ONLYNOTPESSIMISTIC ->
						
						let respess =    mayHaveListLevelNPessimisticnext  pessimistic cl   [name]    in
						let hasGoodSize =  totalSize > 2500 || (mayBePessimistic && totalSize >1000) in
						let nopessimistic = allarenotPessimistic name respess in
						if (respess = [] (*|| nopessimistic*)) && hasGoodSize  then  
						(
								biggesteString:=!biggesteString^Printf.sprintf "\nLevel %d No pessimism for %s function size %d\n" (n+1) name totalSize;
								biggesteString:=!biggesteString^Printf.sprintf "\t%s   totalsize %d\n" name  totalSize ; currentLevelChoosenNode := List.append [name] !currentLevelChoosenNode
						)
						else 
							if respess != [] && hasGoodSize then
							(

						
									biggesteString:=!biggesteString^Printf.sprintf "\nLevel %d not selected possible pessimism size %d for:\n"  (n+1) totalSize;  
									List.iter(fun (name, suiv)->      
										biggesteString:=!biggesteString^Printf.sprintf "\t%s\n" name  ; 
										List.iter(fun (n,_)-> (*if b = true then *)biggesteString:=!biggesteString^Printf.sprintf "\t\t%s\n" n 
											(*else biggesteString:=!biggesteString^Printf.sprintf "\t\tno pessimistic for%s\n" n*))suiv        
									)respess;
			
							) ;
						 
						 
		| WITHVALUE value ->

						let respess =    mayHaveListLevelNPessimisticnext  pessimistic cl   [name]    in
						let hasGoodSize =  totalSize > 2500 || (mayBePessimistic && totalSize >1000) in
						let nopessimistic = allarenotPessimistic name respess in
						if (respess = []  (*|| nopessimistic*))  && hasGoodSize  then  
						(  
		  					  	biggesteString:=!biggesteString^Printf.sprintf "\nLevel %d No pessimism for %s function or law size size : %d \n" (n+1) name totalSize;
								biggesteString:=!biggesteString^Printf.sprintf "\t%s   totalsize %d\n" name  totalSize ; currentLevelChoosenNode := List.append [name] !currentLevelChoosenNode
						)
						else 
							if respess != [] && hasGoodSize then
							(
									biggesteString:=!biggesteString^Printf.sprintf "\nLevel %d possible pessimism size %d for:\n"  (n+1) totalSize;  
									List.iter(fun (name, suiv)->    
										biggesteString:=!biggesteString^Printf.sprintf "\t%s\n" name  ; 
										List.iter(fun (n,_)-> (*if b = true then *)biggesteString:=!biggesteString^Printf.sprintf "\t\t%s\n" n 
											(*else biggesteString:=!biggesteString^Printf.sprintf "\t\tno pessimistic for%s\n" n*))suiv    
									)respess;
									if totalSize <= value	then  biggesteString:=!biggesteString^Printf.sprintf "it is not selected\n"
									else
										(biggesteString:=!biggesteString^Printf.sprintf "\t%s   totalsize %d\n" name  totalSize ; currentLevelChoosenNode := List.append [name] !currentLevelChoosenNode)

			
							) ;
						 
		)
		
		)(List.assoc (n+1) classifiedList);

	chooseClassified (n+1) classifiedList cl l !currentLevelChoosenNode	 pessimistic typeOfPartialisation
end
and allarenotPessimistic  name respess = 
if respess = [] || List.mem_assoc name respess = false then true
else
allarenotPessimisticaux (List.assoc name respess)
and allarenotPessimisticaux l =
if l  = [] then true
else
begin
	let (first, next) = (List.hd l,List.tl l) in
	let (n,b) = first in
	if b then false else allarenotPessimisticaux next
end




let listCurrent = ref []




let resumeForPartial l cl=
	resumeString := Printf.sprintf "/*---------------------------------\n";
	biggesteString := Printf.sprintf "\n\nmay be to partialise\n";
	currentChoosenNode := [];
		List.iter (fun(name,nbc,nbcil,fixed,endofred)->
			let initsize = (getFunctionSize name !callsListEval) in
			if List.mem name !listAlreadyNodeFunction then
			(
		
				let totalSize = ( nbcil*fixedPointCoef*initsize + (nbc - nbcil)*initsize + initsize *2 *fixed) in
				let mayBePessimistic = if List.mem name !listOfFunctionWithLoop && endofred then 
									(if List.mem name !maybepessimisticloopcall =false then  maybepessimisticloopcall:= List.append [name] !maybepessimisticloopcall; true) 
							   else false in
				if initsize> 5 && totalSize > 2500 || (mayBePessimistic && totalSize >1000)  then 
					(biggesteString:=!biggesteString^Printf.sprintf "%s   totalsize %d\n" name  totalSize ; currentChoosenNode := List.append [name,totalSize] !currentChoosenNode);
				resumeString := !resumeString^Printf.sprintf "%s = nbcall %d, nbcallinloop %d, size %d, totalsize %d\n" name nbc nbcil initsize totalSize
			)
						
		)l;
		let (classifiedList,_,_) = classified !currentChoosenNode !currentChoosenNode [] cl [] l in
		if classifiedList != [] then  biggesteString:=!biggesteString^Printf.sprintf "\nFuntions are classified : 0 are the first to partialise ...\n" 
		else biggesteString:=!biggesteString^Printf.sprintf "\nNothing to classifie...\n" ; 

		if !maybepessimisticloopcall != [] then 
			( biggesteString:=!biggesteString^Printf.sprintf "\nPessimism sources...predecessors of\n" ; List.iter (fun n-> biggesteString:=!biggesteString^Printf.sprintf "%s\n" n ;)!maybepessimisticloopcall)
		else  biggesteString:=!biggesteString^Printf.sprintf "\nNo pessimism sources...\n" ; 

		
		
		List.iter (fun(number,l)->
			  biggesteString:=!biggesteString^Printf.sprintf "Class %d \n" number; 
			  List.iter (fun id ->biggesteString:=!biggesteString^Printf.sprintf "\t%s\n" id;) l
						
		)classifiedList;
		let currentLevelChoosen= if List.mem_assoc 0 classifiedList then  List.assoc 0 classifiedList else [] in


(*	ALLFUNCTION
	| ONLYNOTPESSIMISTIC
	| WITHVALUE value*)
		biggesteString:=!biggesteString^Printf.sprintf "\nClassified with all big function will be partialised\n" ; 
		(biggesteString:=!biggesteString^Printf.sprintf "\nlevel 0 selected function all\n"; List.iter(fun n->biggesteString:=!biggesteString^Printf.sprintf "\t%s\n" n)	currentLevelChoosen); 
		chooseClassified 0 classifiedList cl l currentLevelChoosen !maybepessimisticloopcall ALLFUNCTION;
		
		let respess =  mayHaveListLevelNPessimisticnext  !maybepessimisticloopcall cl   currentLevelChoosen   in
		let value = 30000 in

		 listCurrent := [];
		biggesteString:=!biggesteString^Printf.sprintf "\nClassified with only not pessimistic big function will be partialised\n" ;  
		 let listCurrentNoPessimistic =List.filter(fun name  -> if List.mem_assoc name respess  then false else true)currentLevelChoosen in
			if respess = [] then
			(
				 biggesteString:=!biggesteString^Printf.sprintf "\nLevel 0 No pessimism \n";
				 biggesteString:=!biggesteString^Printf.sprintf "\nLevel 0 all are selected \n";
				(*	(biggesteString:=!biggesteString^Printf.sprintf "\nlevel 0 selected function no perssimistic\n"; List.iter(fun n->biggesteString:=!biggesteString^Printf.sprintf "\t%s\n" n)	currentLevelChoosen);*)
				listCurrent :=  currentLevelChoosen;
			)
			else 
			(
				biggesteString:=!biggesteString^Printf.sprintf "\nLevel 0 possible pessimism for \n" ; (* sauf si pas d'arcs rouge entre les deux *)
				List.iter(fun n-> if List.mem_assoc n respess = false then listCurrent := List.append [n] !listCurrent ;)currentLevelChoosen;
				List.iter(fun (name, suiv)->    
					if List.assoc name !currentChoosenNode >value then listCurrent := List.append [name] !listCurrent ;
					biggesteString:=!biggesteString^Printf.sprintf "\t%s for :\n" name  ; List.iter(fun (n,b)->  biggesteString:=!biggesteString^Printf.sprintf "\t\t%s\n" n)suiv        
				)respess;
				
			);



		let currentl = !listCurrent in
		let maybe = !maybepessimisticloopcall in
		(biggesteString:=!biggesteString^Printf.sprintf "\nlevel 0 selected function\n"; List.iter(fun n->biggesteString:=!biggesteString^Printf.sprintf "\t%s\n" n)listCurrentNoPessimistic);
		chooseClassified 0 classifiedList cl l listCurrentNoPessimistic maybe ONLYNOTPESSIMISTIC;

		
		biggesteString:=!biggesteString^Printf.sprintf "\nClassified with only not pessimistic little function size <= %d will be partialised\n" value;  
		(biggesteString:=!biggesteString^Printf.sprintf "\nlevel 0 selected function\n"; List.iter(fun n->biggesteString:=!biggesteString^Printf.sprintf "\t%s\n" n)!listCurrent);
		chooseClassified 0 classifiedList cl l currentl maybe (WITHVALUE value);
	

		resumeString := !resumeString^(!biggesteString)^Printf.sprintf "\n---------------------------------*/\n"



let resume secondParse complet=
analyse_defs secondParse;
  getInfoFunctions doc;

(*Printf.printf "number of function %d \n" !numberofFunction;*)
  evalCallList !callsList;
  let write_commented_dot comment graph filename =
  	let file = open_out filename
  	in let _ = Printf.fprintf file "%s %s" comment (Tod.string_of_graph graph)
  	in close_out file
in

let _ = dot_sizes := read_dot_size() in

if complet then 
begin
	graph := Digraph("main", false, [
		Attribute(GCenter(true));
		NodeAttr([NShape("plaintext"); NFontSize(12)]);
	]);
	
	
	getAllgraph !callsList ;
	
	
	evalCallListNumbers  false !listAssosFonctioNameNBCalls;
	resumeForPartial !callsListNumbers !callsList;
		 
	(* Write the .dot file with the comment *)
	write_commented_dot !resumeString !graph (Filename.concat (!Cextraireboucle.out_dir) "main.dot");
end
else
begin
	List.iter (fun name ->
		graph := Digraph(!name, false, [
			Attribute(GCenter(true));
			NodeAttr([NShape("plaintext"); NFontSize(12)]);
		]);
		listAlreadyNodeFunction := [];
 		
        listAssosFonctioNameNBCalls := [];
		maybepessimisticloopcall := [];
		newcurrentcallslist := [];
		partialised := [];

		getPartialgraph !name !callsList;
		evalCallListNumbers  true !listAssosFonctioNameNBCalls;
		resumeForPartial !callsListNumbers !callsList;
		
				
		(* Write the .dot file with the comment *)
		write_commented_dot !resumeString !graph (Filename.concat (!Cextraireboucle.out_dir) (!name ^ ".dot"));
		
	) (!Cextraireboucle.names)
end	;


