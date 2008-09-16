
(* cvarabs -- use Frontc CAML  abstract store evaluation and evaluation of expression
*
** Project:	O_Range
** File:	cvarabs.ml
** Version:	1.1
** Date:	11.7.2008
** Author:	Marianne de Michiel
*)
open Cabs
open Cxml
open Cprint
open Cexptostr
open Cvariables
open Constante

let version = "cvarabs Marianne de Michiel"


	type arraySize = NOSIZE | SARRAY of int |MSARRAY of int list

	let listAssosArrayIDsize  =  ref [(" ", NOSIZE)]
	let existAssosArrayIDsize name  = (List.mem_assoc name !listAssosArrayIDsize)
	let setAssosArrayIDsize name size = 
		if existAssosArrayIDsize name = false then listAssosArrayIDsize := List.append   [(name, size)]   !listAssosArrayIDsize 	
	let getAssosArrayIDsize name  = if existAssosArrayIDsize name then (List.assoc name !listAssosArrayIDsize) else NOSIZE


let aAntiDep = ref false
let vDEBUG = ref false
let vEPSILON = ref (VARIABLE("EPSILON"))
let vEPSILONFLOAT = ref (CONSTANT (CONST_FLOAT "0.001"))
let vEPSILONINT = ref (CONSTANT (CONST_INT "1"))
(*let vEPSILON = ref (CONSTANT (CONST_FLOAT "0.001"))*)
let isIntoSwithch = ref false

let estDansBoucle = ref false



let rec getArrayNameOfexp exp =
	match exp with
		  UNARY (op, e) ->
			let (tab1,lidx1, e1) =getArrayNameOfexp e in
			(match op with
			  MEMOF | ADDROF -> (tab1,lidx1,  UNARY (op,e1))
			|_->(tab1,lidx1, e1))

		| BINARY (_, exp1, exp2) ->
			let (tab1,lidx1, e1) = getArrayNameOfexp exp1 in
			if tab1 = "" then  getArrayNameOfexp exp2  
			else (tab1,lidx1, e1)
		| CAST (typ, e) -> getArrayNameOfexp e 
		| VARIABLE name -> (name, [], exp)
		| INDEX (exp1, idx) ->let (tab,lidx) = analyseArray exp []  in (tab,lidx, exp)
		|_ ->("", [], NOTHING)


and analyseArray exp lidx =
	match exp with 
		VARIABLE v -> (v , lidx)
		| INDEX (e, i) ->  analyseArray e (List.append [i] lidx) 
		| _ -> (* actuellement  non traitée *)("", lidx)


type newBaseType =
	FLOAT_TYPE (*float values*)
	|INT_TYPE
(*	| ENUM_TYPE of string*)
	| UNION_TYPE  of string
	| TYPEDEF_NAME of string
	|  STRUCT_TYPE of string 


let get_estAffect exp =
	match exp with
	BINARY (op, _, _) ->
	( match op with ASSIGN|ADD_ASSIGN|SUB_ASSIGN|MUL_ASSIGN|DIV_ASSIGN|MOD_ASSIGN|BOR_ASSIGN|XOR_ASSIGN|SHL_ASSIGN|SHR_ASSIGN->  true
	  |_ -> false )
	| UNARY (op, _) -> ( match op with		PREINCR | PREDECR 	| POSINCR	| POSDECR ->  true |_ -> false )
	|_ -> false	

type expVA = EXP  of expression |	MULTIPLE


type  inst =
	  VAR of string * expVA		
	| MEMASSIGN of string * expVA * expVA
	| TAB of string * expVA * expVA
	| IFV of expVA * inst 			
	| IFVF of expVA * inst * inst			  
	| BEGIN of inst list 
	| FORV of int*string * expVA * expVA * expVA * expVA *inst 	(*derniere expression nb it*)
	| APPEL of int*inst*(* inst*) string * inst*inst *string	



(* il  faudra ajouter les struct *)
let new_instVar id exp  = VAR(id, if !isIntoSwithch = false then exp else EXP(NOTHING))
let new_instMem id exp1 exp2  = MEMASSIGN(id, exp1, if !isIntoSwithch = false then exp2  else EXP(NOTHING))
let new_instTab id exp1 exp2  = TAB(id, exp1, if !isIntoSwithch = false then exp2  else EXP(NOTHING))
let new_instIFVF exp inst1 inst2  = IFVF(exp, inst1, inst2)
let new_instIFV exp inst1   = IFV(exp, inst1)
let new_instFOR num id exp1 exp2 exp3 nbIt inst  = FORV(num,id, exp1, exp2, exp3, nbIt, inst)
let new_instBEGIN listeInst  = BEGIN(listeInst)
let new_instAPPEL num instAffectIn nom instAffectSortie corps s = APPEL(num, instAffectIn, nom, instAffectSortie,corps, s)
type listeDesInst = inst list
let listAssocIdType  = ref []

type decType =
STRUCTORUNION of (string*newBaseType) list
| TYPEDEFTYPE of newBaseType

let newDecTypeSTRUCTORUNION l = STRUCTORUNION(l)
let newDecTypeTYPEDEFTYPE n = TYPEDEFTYPE(n)

let listAssosIdTypeTypeDec = ref []

let rec getBaseType t =
match t with
	FLOAT_TYPE |INT_TYPE -> t 
	| UNION_TYPE s -> t
	| TYPEDEF_NAME s->  
		 if (List.mem_assoc s !listAssosIdTypeTypeDec)= true then 
		 begin
			match  (List.assoc s !listAssosIdTypeTypeDec)  with  TYPEDEFTYPE (typ) -> getBaseType typ  | _->t
		 end
		 else t
	|  STRUCT_TYPE s ->  t



let rec getInitVarFromStruct (exp : expression)   =
	 match exp with
		 VARIABLE name ->  [name] 
		| INDEX (e, _)  -> getInitVarFromStruct e 
		| MEMBEROF (e, c)  | MEMBEROFPTR (e, c) -> List.append (getInitVarFromStruct e) [c]
		| UNARY (op, e) ->
					(match op with 
							ADDROF ->
								(*Printf.printf "getInitVarFromStruct &assign\n";*)
								getInitVarFromStruct e 
							|_->(*Printf.printf "not &assign\n";*)[])
		| _-> []

let rec consCommaExp front t champlist champlistLookingFor exp=
match t with
	FLOAT_TYPE |INT_TYPE  -> front
	|UNION_TYPE s| TYPEDEF_NAME s->  
		 if (List.mem_assoc s !listAssosIdTypeTypeDec)= true then 
		 begin
			match  (List.assoc s !listAssosIdTypeTypeDec)  with 
				 TYPEDEFTYPE (typ) -> consCommaExp front typ champlist champlistLookingFor exp | _->front
		 end
		else front
	|  STRUCT_TYPE s ->  
		if (List.mem_assoc s !listAssosIdTypeTypeDec)= true then 
		 begin
			match  (List.assoc s !listAssosIdTypeTypeDec)  with  
				STRUCTORUNION (l) -> 
			CONSTANT(	CONST_COMPOUND(
					List.map (
					fun(n,t)->  
						let ncl = List.append champlist [n] in
						if ncl = champlistLookingFor then exp 
						else consCommaExp ( MEMBEROF (front, n)) t ncl champlistLookingFor exp  
					)l  ))
				| _->front
		 end
		else front

						

let rec getconsCommaExp  t  champlistLookingFor lexp =
if champlistLookingFor = [] || lexp = []  then (NOTHING) else 
match t with
	FLOAT_TYPE |INT_TYPE  -> (NOTHING)
	|UNION_TYPE s| TYPEDEF_NAME s->  
		 if (List.mem_assoc s !listAssosIdTypeTypeDec)= true then 
		 begin
			match  (List.assoc s !listAssosIdTypeTypeDec) with  
				TYPEDEFTYPE (typ) -> 
										getconsCommaExp  typ  champlistLookingFor lexp 
				| _->(NOTHING)
		 end
		else (NOTHING)
	|  STRUCT_TYPE s ->  
		(*Printf.printf"getconsCommaExp ";*)
		if (List.mem_assoc s !listAssosIdTypeTypeDec)= true then 
		 begin
			match  (List.assoc s !listAssosIdTypeTypeDec)  with  
			STRUCTORUNION (l) -> 
				if champlistLookingFor = [] || lexp = [] || l = [] then (NOTHING)
				else
				begin	
					let (champ,suitec,expChamp,suiteexpc) = (List.hd champlistLookingFor,List.tl champlistLookingFor,
															 List.hd lexp,  List.tl lexp) in

					
					let ((n,typ),suitedec) = (List.hd l,List.tl l) in
(*Printf.printf "champ=%s, n %s\n"champ n;*)
					if n = champ then
						if  suitec = [] then begin (* print_expression expChamp 0; new_line();*)  expChamp end(*trouve*)
						else getconsCommaExp  typ  suitec suiteexpc(*dans sous champs*)
					else getNextChamp  champlistLookingFor  suiteexpc suitedec (*dans autre champs*)
				end
				
			| _->(NOTHING)
		 end
		else (NOTHING)

and getNextChamp lchamps  lexp ldec =
if lchamps = [] || lexp = [] || ldec = [] then (NOTHING)
else
begin	
	let (champ,suitec,expChamp,suiteexpc) = (List.hd lchamps,List.tl lchamps, List.hd lexp,  List.tl lexp) in
	let ((n,typ),suitedec) = (List.hd ldec,List.tl ldec) in
(*Printf.printf "getNextChamp champ=%s, n %s\n"champ n;*)
	if n = champ then
						if  suitec = [] then expChamp (*trouve*)
						else getconsCommaExp  typ  suitec suiteexpc(*dans sous champs*)
	else getNextChamp  lchamps  suiteexpc suitedec (*dans autre champs*)
end

let rec printfBaseType t=
match t with
	FLOAT_TYPE -> Printf.printf " flottant "
	|INT_TYPE -> Printf.printf " integer "
	| UNION_TYPE s ->  Printf.printf " union of %s" s
	| TYPEDEF_NAME s->  Printf.printf " type of %s" s;
		 if (List.mem_assoc s !listAssosIdTypeTypeDec)= true then 
		 begin
			match  (List.assoc s !listAssosIdTypeTypeDec)  with  TYPEDEFTYPE (typ) -> printfBaseType typ  | _->Printf.printf " inconnu "
		 end
	|  STRUCT_TYPE s ->  Printf.printf " struct of %s" s;
		if (List.mem_assoc s !listAssosIdTypeTypeDec)= true then 
		 begin
			match  (List.assoc s !listAssosIdTypeTypeDec)  with  
				STRUCTORUNION (l) -> List.iter (fun(n,t)-> Printf.printf " champ %s type\n" n ; printfBaseType t; new_line() )l  
				| _->Printf.printf " inconnu "
		 end
		


let print_expVA e = match e with MULTIPLE -> Printf.printf "MULTIPLEDEF \n"| EXP (e) -> if e = NOTHING then Printf.printf "NOTHING" else print_expression e 0


let rec hasPtrArrayBoundConditionExp e =
match e with
		  UNARY (_, exp) ->hasPtrArrayBoundConditionExp exp 
		| BINARY (_, exp1, exp2) ->
			let (b1,e1 )= hasPtrArrayBoundConditionExp exp1 in
			let (b2,e2 )= hasPtrArrayBoundConditionExp exp2 in
			if b1 && b2 = false then  (b1, e1) 
			else  if b1 = false && b2 then (b2, e2)  else (false, "") 
		| VARIABLE id -> 
			if (String.length id > 19) then
				if (String.sub id  0 19) = "getvarTailleTabMax_" then
				begin
					let var = String.sub id 19 ((String.length id)-19) in
				(*	Printf.printf "dans hasPtrArrayBoundConditionExp, trouve %s type : \n" var;
					printfBaseType (getBaseType (List.assoc var !listAssocIdType) );*)
				    (true , var)	
				end
				else begin(* Printf.printf "dans hasPtrArrayBoundConditionExp, autre\n" ;*)(false, "") end
			else   (false, "") 
		| _ ->  (false, "") 

let hasPtrArrayBoundCondition e = match e with MULTIPLE -> (false, "") | EXP (e) -> hasPtrArrayBoundConditionExp e 

let estNothing e = match e with MULTIPLE -> 	false | EXP (e) -> 	match e with NOTHING -> true |_-> false

type sens =	CROISSANT|   DECROISSANT|   NONMONOTONE|   CONSTANTE

let printSens s =
match s with
	CROISSANT -> 	Printf.printf "CROISSANT \n"
|   DECROISSANT -> 	Printf.printf "DECROISSANT \n"
|   NONMONOTONE -> 	Printf.printf "NONMONOTONE \n"
|   CONSTANTE -> 	Printf.printf "CONSTANTE \n"

type infoAffich =
{
	conditionA : expVA;
	infA : expVA;
	supA : expVA;
	incA : expVA;
	sensVariationA : sens;
	opA :  binary_operator ;
}

let new_infoAffich c i s incr d o=
{
	conditionA =c;
	infA =i;
	supA =s;
	incA =incr;
	sensVariationA =d;
	opA = o;
} 

let infoaffichNull = ref (new_infoAffich (EXP(NOTHING)) (EXP(NOTHING))(EXP(NOTHING)) (EXP(NOTHING)) NONMONOTONE ADD) 

type expressionEvaluee =
	 NOCOMP
	| Boolean of bool
	| Var of string
   	| ConstInt of string
	| ConstFloat of string
	| Sum of expressionEvaluee * expressionEvaluee    (* e1 + e2 *)
	| Shr of expressionEvaluee * expressionEvaluee    (* e1 SHR e2 *)
	| Shl of expressionEvaluee * expressionEvaluee    (* e1 SHL e2 *)
   	| Diff of expressionEvaluee * expressionEvaluee   (* e1 - e2 *)
   	| Prod of expressionEvaluee * expressionEvaluee    (* e1 + e2 *)
	| Mod of expressionEvaluee * expressionEvaluee    (* e1 + e2 *)
	| Quot of expressionEvaluee * expressionEvaluee    (* e1 + e2 *)
   	| PartieEntiereSup of expressionEvaluee   (* e1 - e2 *)
   	| PartieEntiereInf of expressionEvaluee   (* e1 * e2 *)
	| Puis of expressionEvaluee * expressionEvaluee    (* e1 ** e2 *)
	| Log of expressionEvaluee
    | Sygma of string * expressionEvaluee *expressionEvaluee * expressionEvaluee (*expression*)  (* e1 / e2 *)
    | Max of string * expressionEvaluee *expressionEvaluee * expressionEvaluee (*expression*)  (* e1 / e2 *)
	| Eq1 of expressionEvaluee  (*si E1 = 1 alors e2 sinon e3*)
	| Maximum of expressionEvaluee * expressionEvaluee (* maximum entre 2 expressions *)
	| Minimum of expressionEvaluee * expressionEvaluee 

let rec expressionEvalueeToExpression exprEvaluee =
match exprEvaluee with
	ConstInt(i) 			->  CONSTANT(CONST_INT(i))
	| 	ConstFloat (f) 		->  CONSTANT(CONST_FLOAT (f))
	|	NOCOMP				->	NOTHING 
	|   Boolean (b)			-> if b = true then CONSTANT(CONST_INT("1")) else CONSTANT(CONST_INT("0"))	
	|  	Var (s) 			-> 	VARIABLE(s)
	|  	Sum (f, g)  		-> 	let exp1 = expressionEvalueeToExpression f in
								let exp2 = expressionEvalueeToExpression g in
								if exp1 = NOTHING || exp2 = NOTHING then NOTHING else BINARY (ADD, exp1, exp2) 										
	|  	Shl (f, g)  		-> 	let exp1 = expressionEvalueeToExpression f in
								let exp2 = expressionEvalueeToExpression g in
								if exp1 = NOTHING || exp2 = NOTHING then NOTHING
								else BINARY (DIV, exp1,  CALL (VARIABLE("pow"), List.append [CONSTANT(CONST_INT("2"))] [exp2])) 
	|  	Shr (f, g)  		-> 	let exp1 = expressionEvalueeToExpression f in
								let exp2 = expressionEvalueeToExpression g in
								if exp1 = NOTHING || exp2 = NOTHING then NOTHING
								else BINARY (MUL, exp1, CALL (VARIABLE("pow") , List.append [CONSTANT(CONST_INT("2"))] [exp2])) 
	| 	Diff (f, g) 		-> 	let exp1 = expressionEvalueeToExpression f in
								let exp2 = expressionEvalueeToExpression g in
								if exp1 = NOTHING || exp2 = NOTHING then NOTHING else BINARY (SUB, exp1, exp2) 
	| 	Prod (f, g)  		-> 	let exp1 = expressionEvalueeToExpression f in
								let exp2 = expressionEvalueeToExpression g in
								if exp1 = NOTHING || exp2 = NOTHING then NOTHING else BINARY (MUL, exp1, exp2) 
	| 	Mod (f, g)  		-> 	let exp1 = expressionEvalueeToExpression f in
								let exp2 = expressionEvalueeToExpression g in
								if exp1 = NOTHING || exp2 = NOTHING then NOTHING else BINARY (MOD, exp1, exp2) 	
	| 	Quot (f, g)  		-> 	let exp1 = expressionEvalueeToExpression f in
								let exp2 = expressionEvalueeToExpression g in
								if exp1 = NOTHING || exp2 = NOTHING then NOTHING else BINARY (DIV, exp1, exp2) 
	| 	Puis (f, g)  		-> 	let exp1 = expressionEvalueeToExpression f in
								let exp2 = expressionEvalueeToExpression g in
								if exp1 = NOTHING || exp2 = NOTHING then NOTHING else CALL (VARIABLE("pow") , List.append [exp1] [exp2])
	| 	PartieEntiereSup (e)-> 	let exp1 = expressionEvalueeToExpression e in
								if exp1 = NOTHING  then NOTHING else CALL (VARIABLE("partieEntiereSup") , [exp1])
	| 	PartieEntiereInf (e)-> 	let exp1 = expressionEvalueeToExpression e in
								if exp1 = NOTHING then NOTHING else CALL (VARIABLE("partieEntiereInf") , [exp1])
	| 	Log (e)				-> 	let exp1 = expressionEvalueeToExpression e in
								if exp1 = NOTHING  then NOTHING else CALL (VARIABLE("log") , [exp1])
   	| 	Sygma (var,min,max,e)->  let exp1 = expressionEvalueeToExpression max in
								let exp2 = expressionEvalueeToExpression e in
								if exp1 = NOTHING || exp2 = NOTHING then NOTHING
								else CALL (VARIABLE("SYGMA"), List.append[VARIABLE (var)] (List.append [exp1] [exp2]))
   	| 	Max (var,min,max,e)	-> 	let exp1 = expressionEvalueeToExpression max in
								let exp2 = expressionEvalueeToExpression e in
								if exp1 = NOTHING || exp2 = NOTHING then NOTHING
								else CALL (VARIABLE("MAX"), List.append[VARIABLE (var)] (List.append [exp1] [exp2]))
	|  Eq1 (e1) -> 				let exp1 = expressionEvalueeToExpression e1 in
								if exp1 = NOTHING then NOTHING else BINARY(EQ, exp1, CONSTANT(CONST_INT("1")))
	|  Maximum (f, g)  		-> 	let exp1 = expressionEvalueeToExpression f in
								let exp2 = expressionEvalueeToExpression g in
								if exp1 = NOTHING || exp2 = NOTHING then NOTHING else CALL (VARIABLE("MAXIMUM") , (List.append [exp1] [exp2] ))	
	|  Minimum (f, g)  		-> 	let exp1 = expressionEvalueeToExpression f in
								let exp2 = expressionEvalueeToExpression g in
								if exp1 = NOTHING || exp2 = NOTHING then NOTHING else CALL (VARIABLE("MINIMUM") , (List.append [exp1] [exp2] ))	



let estNoComp expr = match expr with NOCOMP	 | 	Sygma (_,_,_,_) | 	Max (_,_,_,_)-> true 
| 	ConstInt(i) 		-> if i = "" then true else false
| 	ConstFloat (f) 			-> if f = "" then true else false 
| 	_-> false

let rec print_expTerm	exprEvaluee =
	match exprEvaluee with
			ConstInt(i) 			->  Printf.printf " %s" i
		| 	ConstFloat (f) 			-> 	Printf.printf " %s" f
		|	NOCOMP					->	Printf.printf " NOCOMP" 		
		|   Boolean(b)				->  if b = true then Printf.printf " true" 	else Printf.printf " false" 	
		|  	Var (s) 				-> 	Printf.printf " %s" s
		|  	Sum (f, g)  			-> 	Printf.printf "("; print_expTerm f; Printf.printf ") + ("; 
										print_expTerm g; Printf.printf ")"
		|  	Shl (f, g)  			-> 	Printf.printf "("; print_expTerm f; Printf.printf ") << ("; 
										print_expTerm g; Printf.printf ")"
		|  	Shr (f, g)  			-> 	Printf.printf "("; print_expTerm f; Printf.printf ") >> ("; 
										print_expTerm g; Printf.printf ")"
		| 	Diff (f, g)  			-> 	Printf.printf "("; print_expTerm f; Printf.printf ") - ("; 
										print_expTerm g; Printf.printf ")"
		| 	Prod (f, g)  			-> 	Printf.printf "("; print_expTerm f; Printf.printf ") * ("; 
										print_expTerm g; Printf.printf ")"
		| 	Mod (f, g)  			-> 	Printf.printf "("; print_expTerm f; Printf.printf ") Mod ("; 
							  	 		print_expTerm g; Printf.printf ")"
		| 	Quot (f, g)  			-> 	Printf.printf "("; print_expTerm f; Printf.printf ") / ("; 
										print_expTerm g; Printf.printf ")"
		| 	Puis (f, g)  			-> 	Printf.printf "("; print_expTerm f; Printf.printf ") ** ("; 
										print_expTerm g; Printf.printf ")"
		| 	PartieEntiereSup (e)	-> 	Printf.printf "PartieEntiereSup ("; print_expTerm e; Printf.printf ")"
	    | 	PartieEntiereInf (e)	-> 	Printf.printf "PartieEntiereInf ("; print_expTerm e; Printf.printf ")"
		| 	Log (e)					-> 	Printf.printf "Log ("; print_expTerm e; Printf.printf ")"
   		| 	Sygma (var,min,max,e)	-> Printf.printf " NOCOMP" ;	
										if !vDEBUG then
										begin
											Printf.printf "SYGMA pour %s = " var ;print_expTerm min;
											Printf.printf "à " ; print_expTerm max; 
											Printf.printf " (" ;print_expTerm e; Printf.printf ")"
										end
   		| 	Max (var,min,max,e)		->  Printf.printf " NOCOMP" ;	
									if !vDEBUG then
									begin
										Printf.printf "SYGMA pour %s = " var ;print_expTerm min;
										Printf.printf "à " ; print_expTerm max; 
										Printf.printf " (" ;print_expTerm e; Printf.printf ")"
									end
		| 	Eq1 (e1)-> 			Printf.printf " Val TEST " ;	
								print_expTerm e1; Printf.printf " else  " 
		|  Maximum (f, g)  	-> 	Printf.printf " maximum( " ;	print_expTerm f;Printf.printf ", " ;
								print_expTerm g; Printf.printf " ) " 
		|  Minimum (f, g)  	-> 	Printf.printf " minimum( " ;	print_expTerm f;Printf.printf ", " ;
								print_expTerm g; Printf.printf " ) " 	


let rec epsIsonlyVar exp = 
	match exp with
			ConstInt(_) | 	ConstFloat (_) |	NOCOMP	|   Boolean(_)	->   true 
		|  	Var (s) 				-> 	if s = "EPSILON" then true else false (*MARQUE*)
		|  	Sum (f, g) |Shl (f, g) | Shr (f, g) | Diff (f, g)| Prod (f, g)| Mod (f, g)| Quot (f, g) | Puis (f, g)| Maximum (f, g)| Minimum (f, g)  	
				-> 	(epsIsonlyVar) f && (epsIsonlyVar g)
		| 	PartieEntiereSup (e) | 	PartieEntiereInf (e)| 	Log (e)| 	Eq1 (e)	-> epsIsonlyVar e
   		| _	-> false

let espIsNotOnlyVar exp = epsIsonlyVar exp = false   		

let estNul exp =	
	match exp with 
	ConstInt (i)->   (int_of_string  i) = 0 
	|ConstFloat (i) ->  (float_of_string  i) = 0.0 | _->false
					
let estPositif exp =
	match exp with ConstInt (i)->  (int_of_string  i) >= 0 
	| ConstFloat (i) ->  (float_of_string  i) >= 0.0 | _->false

let estStricPositif exp =
	match exp with 
	 ConstInt (i)-> (int_of_string  i) > 0 
	| ConstFloat (i) ->   (float_of_string  i) > 0.0 | _->false

let estUn exp =
	match exp with 
	 ConstInt (i)-> (int_of_string  i) = 1 
	| ConstFloat (i) ->   (float_of_string  i) > 1.0 | _->false

let estMUn exp =
	match exp with 
	 ConstInt (i)-> (int_of_string  i) = -1 
	| ConstFloat (i) ->   (float_of_string  i) > -1.0 | _->false

let estStricNegatif exp =
	match exp with 
	 ConstInt (i)-> (int_of_string  i) < 0 
	| ConstFloat (i) ->   (float_of_string  i) < 0.0 | _->false

let rec estInt exp =
	match exp with 
	 ConstInt (_)	-> 	true
	| ConstFloat (f)->  if (floor (float_of_string f)) = (float_of_string f)  then true else false 
	|  	Var (s) 	-> 	if s = "EPSILON" then true (*MARQUE*)
						else 
						begin 
							if (List.mem_assoc s !listAssocIdType)= true then 
							begin
							(*	Printf.printf "variable de type ???\n";*)
								match getBaseType (List.assoc s !listAssocIdType)    with
									INT_TYPE ->   true
									| _  -> (*Printf.printf "variable de type autre\n";*) false
							end			
							else begin (*Printf.printf "variable %s de type non trouvee\n" s; *) false end
						end 
	|  	Sum (f, g) |Shl (f, g) | Shr (f, g) | Diff (f, g)| Prod (f, g)| Mod (f, g)| Quot (f, g) | Puis (f, g)| Maximum (f, g)
	| Minimum (f, g)  	
			-> 	(estInt) f && (estInt g)
	| 	PartieEntiereSup (e) | 	PartieEntiereInf (e)| 	Log (e)| 	Eq1 (e)	-> estInt e
   	| _	-> false


let rec estFloat exp =
	match exp with 
	 ConstInt (_)-> false
	| ConstFloat (f) -> if (floor (float_of_string f)) = (float_of_string f)  then false else true 
	|  	Var (s) 	-> 	if s = "EPSILON" then true (*MARQUE*)
						else 
						begin 
							if (List.mem_assoc s !listAssocIdType)= true then 
								match getBaseType (List.assoc s !listAssocIdType)    with
									INT_TYPE ->   true
									| _  -> (*Printf.printf "variable de type autre\n"; *) false			
												
							else begin (*Printf.printf "variable de type non trouve\n";*) false end
						end 
	|  	Sum (f, g) |Shl (f, g) | Shr (f, g) | Diff (f, g)| Prod (f, g)| Mod (f, g)| Quot (f, g) | Puis (f, g)| Maximum (f, g)| 
		Minimum (f, g)  	
			-> 	(estFloat) f || (estFloat g)
	| 	PartieEntiereSup (e) | 	PartieEntiereInf (e)| 	Log (e)| 	Eq1 (e)	-> estFloat e
   	| _	-> false	
	
let estDefExp exp = match exp with ConstInt (i) | ConstFloat (i) ->  true| _->false
let estBool exp = match exp with Boolean (_) ->true| _->false
let estBoolOrVal exp = estDefExp exp || estBool exp 
	
let rec evalexpression  exp =
(*Printf.printf"evalexpression\n";print_expTerm exp; new_line ();*)
   match exp with
	NOCOMP -> NOCOMP	
	|  ConstInt (_) |  ConstFloat (_) ->  exp
	|  Var (_)| Boolean(_) 	-> exp
	|  Sum (f, g)  -> 
		let val1 = evalexpression f in
		let val2 = evalexpression g in
		if  estNoComp val1  or estNoComp val2  then NOCOMP 
		else 
		begin 
			match val1 with
			ConstInt (i) ->
				(	let valeur = (int_of_string  i) in
					match val2 with 
					ConstInt(j) -> 		ConstInt(Printf.sprintf "%d" (valeur + (int_of_string  j)))
					|ConstFloat(j)-> 	ConstFloat (Printf.sprintf "%f" (float(valeur) +. (float_of_string  j)))
					|Var(v) -> 			if valeur = 0 then val2 else  Sum(Var(v),val1)
					|_->exp
				)				
			|ConstFloat (i)->	
			(
				let valeur1 = (float_of_string  i) in
				match val2 with 
					ConstInt(j) -> 		ConstFloat(Printf.sprintf "%f" (valeur1 +. (float_of_string  j)))
					|ConstFloat (j)-> 	ConstFloat(Printf.sprintf "%f" (valeur1 +. (float_of_string  j)))
					|Var(v) -> 	if valeur1 = 0.0 then val2 else  begin (*Printf.printf "somme val2, val1\n";*) Sum(Var(v),val1) end
					|_->exp
			)
			|Var(_) -> 
			(
				match val2 with 
					ConstInt(j) -> 			if (float_of_string  j) = 0.0 then	val1 else Sum(val2,val1)
					|ConstFloat (j)->		if (float_of_string  j) = 0.0 then val1 else Sum(val2,val1)
					|Var(_) ->  			Sum(val2,val1)
					|_->exp
			)
			| _ ->exp
		end
  	| Diff (f, g)   -> 
		let val1 = evalexpression f in
		let val2 = evalexpression g in
		if estNoComp val1 or estNoComp val2 then NOCOMP 
		else 
			begin 
				match val1 with
				ConstInt (i) ->
					begin
						match val2 with 
						ConstInt(j) -> 	  ConstInt(Printf.sprintf "%d"  ((int_of_string  i) - (int_of_string  j)))
						|ConstFloat (j)-> ConstFloat(Printf.sprintf "%f" ((float_of_string  i) -. (float_of_string  j)))
						|Var(v) -> 		  if (int_of_string  i) = 0 then 
										  Diff (ConstInt("0"), val2) else  Diff(val1,val2)
						|_->exp
					end				
				|ConstFloat (i)->	
					begin
						let valeur1 = (float_of_string  i) in
						match val2 with 
						ConstInt(j) -> 		ConstFloat(Printf.sprintf "%f" (valeur1 -. (float_of_string  j)))
						|ConstFloat (j)-> 	ConstFloat(Printf.sprintf "%f" (valeur1 -. (float_of_string  j)))
						|Var(v) -> 			if valeur1 = 0.0 then Diff (ConstInt("0"), val2) else  Diff(val1,val2)
						|_->exp
					end
				|Var(v) -> 
				(
					match val2 with 
					ConstInt(j) -> 			if (float_of_string  j) = 0.0 then	val1	else Diff(val1,val2)
					|ConstFloat (j)-> 		if (float_of_string  j) = 0.0 then 	val1	else Diff(val1,val2)
					|Var(v) ->  Diff(val1,val2)
					|_->exp	
				)
				|_->exp
		end
	| 	Puis (f, g)    	->

(*Printf.printf "evalexpression pow\n";*)
		let val1 = evalexpression f in
		let val2 = evalexpression g in
(* print_expTerm	val1;
 print_expTerm	val2;new_line();*)

		if estNoComp val1  or estNoComp val2  then NOCOMP 
		else 
		begin 
			match val1 with
			ConstInt (i) ->
				if (int_of_string  i) = 1 then ConstInt("1")
				else			
					(match val2 with 
					ConstInt(j) |ConstFloat (j)-> 
						let val2 = (float_of_string  j) in
						if val2  = 1.0 then	ConstInt (i) else ConstFloat(Printf.sprintf "%f" ((float_of_string  i) **val2))
					|Var(v) ->   Puis (val1,val2)
					|_->exp)
									
			|ConstFloat (i)->	
				begin
					let valeur1 = (float_of_string  i) in
					if valeur1 = 1.0 then ConstInt("1")
					else
					(match val2 with 
						ConstInt(j) ->
							let val2 = (float_of_string  j) in
							if val2  = 1.0 then	ConstFloat (i)
							else ConstFloat(Printf.sprintf "%f" (valeur1 ** (float_of_string  j)))
						|ConstFloat (j) -> 
							let val2 = (float_of_string  j) in
							if val2  = 1.0 then	ConstFloat (i)  else ConstFloat(Printf.sprintf "%f" (valeur1 ** (float_of_string  j)))
						|Var(v) ->   Puis(val1,val2)
						|_->exp)
				end
			|Var(v) -> 
				begin
					match val2 with 
					ConstInt(j) -> 
						if (float_of_string  j) = 0.0 then ConstInt("1")
						else if (float_of_string  j) = 1.0 then	val1 else Puis(val1,val2)
					|ConstFloat (j)-> 		
						if (float_of_string  j) = 0.0 then ConstInt("1")
						else if (float_of_string  j) = 1.0 then	val1 else Puis(val1,val2)
					|Var(v) ->  Puis(val1,val2)
					|_->exp
				end						
			|_->exp
		end
	| Prod (f, g)  	->
		let val1 = evalexpression f in
		let val2 = evalexpression g in

		if estNoComp val1  or estNoComp val2  then NOCOMP 
		else 
		begin 
			match val1 with
			ConstInt (i) ->
				begin
					match val2 with 
					ConstInt(j) -> 
						ConstInt(Printf.sprintf "%d"  ((int_of_string  i) * (int_of_string  j)))
					|ConstFloat (j)-> 
					 ConstFloat(Printf.sprintf "%f" ((float_of_string  i)*. (float_of_string  j)))
					|Var(v) -> if (int_of_string  i) = 0 then ConstInt("0")
							  else if (int_of_string  i) = 1  then	 val2 else  Prod (val2,val1)
					|_->exp
				end				
		  	|ConstFloat (i)->	
				begin
					let valeur1 = (float_of_string  i) in
					match val2 with 
					ConstInt(j) -> 
						ConstFloat(Printf.sprintf "%f" (valeur1 *. (float_of_string  j)))
					|ConstFloat (j)-> 		
						ConstFloat(Printf.sprintf "%f" (valeur1 *. (float_of_string  j)))
					|Var(v) -> if valeur1 = 0.0 then ConstInt("0")
							  else if valeur1 = 1.0  then	 val2 else  Prod(val1,val2)
					|_->exp
				end
			|Var(v) -> 
				begin
					match val2 with 
					ConstInt(j) -> 
						if (float_of_string  j) = 0.0 then ConstInt("0")
						else if (float_of_string  j) = 1.0 then	val1 else Prod(val2,val1)
					|ConstFloat (j)-> 		
						if (float_of_string  j) = 0.0 then ConstInt("0")
						else if (float_of_string  j) = 1.0 then	val1 else Prod(val2,val1)
					|Var(v) ->  Prod(val2,val1)
					|_->exp
				end
									
			|_->exp
		end
	| Shr (f, g)  	->
		let val1 = evalexpression f in
		let val2 = evalexpression g in

		if estNoComp val1  or estNoComp val2  then NOCOMP 
		else 
		begin 
			match val1 with
			ConstInt (i) ->
				begin
					match val2 with 
					ConstInt(j) ->  ConstInt(Printf.sprintf "%d"  ((int_of_string  i) lsr (int_of_string  j)))
					|ConstFloat (j)->  ConstInt(Printf.sprintf "%d" ((int_of_string   i) lsr (int_of_string  j)))
					|Var(v) -> if (int_of_string  i) = 0 then ConstInt("0") else Shr (val1,val2)
					|_->exp
				end				
			|ConstFloat (i)->	
				begin
					let valeur1 = (int_of_string   i) in
					match val2 with 
					ConstInt(j) ->  ConstInt(Printf.sprintf "%d" (valeur1 lsr (int_of_string  j)))
					|ConstFloat (j)->ConstInt(Printf.sprintf "%d" (valeur1 lsr (int_of_string  j)))
					|Var(v) -> if valeur1 = 0 then ConstInt("0")  else  Shr(val1,val2)
					|_->exp
				end
			|Var(v) -> 
				begin
					match val2 with 
					ConstInt(j) -> if (int_of_string  j) = 0 then val1 else Shr(val1,val2)
					|ConstFloat (j)-> if (int_of_string  j) = 0 then val1 else  Shr(val1,val2)
					|Var(v) ->  Shr(val1,val2)
					|_->exp
				end
									
			|_->exp
		end
	| Shl (f, g)  	->
		let val1 = evalexpression f in
		let val2 = evalexpression g in

		if estNoComp val1  or estNoComp val2  then NOCOMP 
		else 
			begin 
				match val1 with
				ConstInt (i) ->
					begin
						match val2 with 
						ConstInt(j) ->      ConstInt(Printf.sprintf "%d"  ((int_of_string  i) lsl (int_of_string  j)))
						|ConstFloat (j)->   ConstInt(Printf.sprintf "%d" ((int_of_string   i) lsl (int_of_string  j)))
						|Var(v) -> if (int_of_string  i) = 0 then ConstInt("0") else Shl (val1,val2)
						|_->exp
					end				
				|ConstFloat (i)->	
					begin
						let valeur1 = (int_of_string   i) in
						match val2 with 
						ConstInt(j) ->  ConstInt(Printf.sprintf "%d" (valeur1 lsl (int_of_string  j)))
						|ConstFloat (j)->  ConstInt(Printf.sprintf "%d" (valeur1 lsl (int_of_string  j)))
						|Var(v) -> if valeur1 = 0 then ConstInt("0") else  Shl(val1,val2)
						|_->exp
					end
				|Var(v) -> 
					begin
						match val2 with 
						ConstInt(j) -> 		if (int_of_string  j) = 0 then val1 else Shl(val1,val2)
						|ConstFloat (j)-> 	if (int_of_string  j) = 0 then val1 else Shl(val1,val2)
						|Var(v) ->  Shl(val1,val2)
						|_->exp
					end
									
				|_->exp
		end
	| Mod (f, g)  	-> 
		let val1 = evalexpression f in
		let val2 = evalexpression g in
		if estNoComp val1  or estNoComp val2  then NOCOMP 
		else 
			begin 
				match val1 with
				ConstInt (i) ->
					begin
						match val2 with 
						ConstInt(j) -> 
						 ConstInt(Printf.sprintf "%d"  ((int_of_string  i) mod (int_of_string  j)))
						|Var(v) ->  Mod(val1,val2)
						|_->exp				
					end
				|Var(v) ->
					(
						match val2 with 
						ConstInt(j) -> if (float_of_string  j) = 1.0 then val1 else Mod(val1,val2)
						|ConstFloat(j)->if (float_of_string  j) = 1.0 then val1 else Mod(val1,val2)
						|Var(v) ->  Mod(val1,val2)
						|_->exp
					)
									  
				|_->exp
			end
	| Quot (f, g)  -> 
		let val1 = evalexpression f in
		let val2 = evalexpression g in
		if estNoComp val1  or estNoComp val2  then NOCOMP 
		else 
			begin 
				match val1 with
				ConstInt (i) ->
					begin
						match val2 with 
						ConstInt(j) ->  ConstInt(Printf.sprintf "%d" ((int_of_string  i) / (int_of_string  j)))
						|ConstFloat (j)->   ConstFloat(Printf.sprintf "%f"((float_of_string  i)/. (float_of_string  j)))
						|Var(v) ->  Quot(val1,val2)
						|_->exp
					end				
			  	|ConstFloat (i)->	
					begin
						let valeur1 = (float_of_string  i) in
						match val2 with 
						ConstInt(j) ->  ConstFloat(Printf.sprintf "%f" (valeur1 /. (float_of_string  j)))
						|ConstFloat (j)-> ConstFloat(Printf.sprintf "%f" (valeur1 /. (float_of_string  j)))
						|Var(v) ->  Quot(val1,val2)
						|_->exp
					end
				|Var(v) ->
					(
						match val2 with 
						ConstInt(j) ->     if (float_of_string  j) = 1.0 then	val1	else Quot(val1,val2)
						|ConstFloat (j)->  if (float_of_string  j) = 1.0 then	val1	else Quot(val1,val2)
						|Var(v) ->  Quot(val1,val2)
						|_->exp
					)
				|_->exp
		end
   | PartieEntiereSup (e)-> 
		let val1 = evalexpression e in 	
		if estNoComp val1  then NOCOMP 
		else
			begin
				match val1 with
				ConstInt(_) 	-> val1
				| 	ConstFloat (f) ->	let valeur = (float_of_string f) in
										let pe = truncate valeur in
										let (_,partieFract) =modf valeur in
										if partieFract  = 0.0 then ConstInt(Printf.sprintf "%d" pe)
										else 	ConstInt(Printf.sprintf "%d" (pe + 1)) (*is_integer_num*)
				|Var(v)				-> 	PartieEntiereSup (e)
				|	_				->	exp
			end
   | PartieEntiereInf (e)-> 
		let val1 = evalexpression e in 
		if estNoComp val1  then NOCOMP 
		else 
		begin
			match val1 with
			ConstInt(_) 	-> val1
			| 	ConstFloat (f) 	->	ConstInt(Printf.sprintf "%d" (truncate (float_of_string f)))
			|	Var(v)			-> 	PartieEntiereInf (e)
			|	_				->	exp
		end
   | Sygma (var,min,max,e)-> 	exp
   | Log (e)-> 	let val1 = evalexpression e in 
		if estNoComp val1  then NOCOMP 
		else 
		begin
			match val1 with
			ConstInt(v) 	-> if val1 = ConstInt("0") then  NOCOMP else ConstFloat (Printf.sprintf "%f" (log ( float_of_string v)))
			| 	ConstFloat (f) 	->	if val1 = ConstFloat("0.O") then  NOCOMP else  ConstFloat (Printf.sprintf "%f" (log ( float_of_string f)))
			|	Var(v)			-> 	Log (val1)
			|	_				->	Log (val1)
			end	
   | Max (var,min,max,e)-> 	exp
   | Eq1 (e1)-> 			
		let val1 = evalexpression e1 in 
		if estNoComp val1  then NOCOMP 
		else 
		begin
			match val1 with
			ConstInt(_) 	->      if val1 = ConstInt("1") then ConstInt("1") else ConstInt("0")
			| 	ConstFloat (f) 	->if val1 = ConstFloat("1.0") then ConstInt("1") else ConstInt("0")
			|	Var(v)			-> 	Eq1 (val1)
			|	_				->	exp
		end
	|  Maximum (f, g)  			-> 	
		let val1 = evalexpression f in
		let val2 = evalexpression g in
		if estNoComp val1 or estNoComp val2 then NOCOMP 
		else  if estDefExp val1  &&  estDefExp val2 then maxi val1 val2
			 else NOCOMP
	
	|  Minimum (f, g)  	-> 	
		let val1 = evalexpression f in
		let val2 = evalexpression g in
		if estNoComp val1  &&  estNoComp val2 then NOCOMP
		else if estDefExp val1  &&  estDefExp val2 then mini val1 val2
			 else if  estDefExp val1 then val1 else val2

		

and mini v1 v2 = if estPositif (evalexpression (Diff( v1, v2))) then v2 else v1
and maxi v1 v2 = if estPositif (evalexpression (Diff( v1, v2))) then v1 else v2

let rec reecrireSygma var expO =
	match expO with
		 BINARY (op, exp1, exp2) ->BINARY (op, reecrireSygma var  exp1, reecrireSygma var  exp2) 
		| CALL (exp, args) ->	
			begin
				match exp with		
					VARIABLE("SYGMA") -> (*	Printf.printf "reecrireSygma :"	;	*)
						(*print_expression expO 0; new_line();*)
						let varexp = List.hd args in
					 	let suite = List.tl args in
						(match varexp with	
							VARIABLE (varS) ->	
								let max = List.hd suite in
								let expE =List.hd (List.tl suite)  in
								if varS = var then
								begin			
									(*Printf.printf "reecrireSygma :remplacer  varS = var %s\n"	var;	*)
									BINARY(MUL, BINARY(ADD,max,(CONSTANT (CONST_INT "1"))) , expE)
								end
								else
								begin
								(*Printf.printf "reecrireSygma : sygma varS %s!= var%s\n"varS var	;*)
									let newmax = reecrireSygma var max in
									let newexp =  reecrireSygma var expE in
									let newargs = List.append [VARIABLE (varS)] (List.append [newmax][newexp]) in
									CALL (exp, newargs)
								end 	
							|_-> expO);
										
					|_-> 
						begin
							let newargs = List.map (fun arg->reecrireSygma var  arg)args in
							CALL (exp, newargs)
						end 
			end	
		| _ -> 	expO
	
let rec remplacerValPar0  var expr =
	match expr with
	NOTHING 					-> NOTHING
	| UNARY (op, exp) 			-> UNARY (op, remplacerValPar0   var exp)
	| BINARY (op, exp1, exp2) 	-> BINARY (op, remplacerValPar0   var  exp1, remplacerValPar0   var exp2)
	| CALL (exp, args) 			->	CALL (exp, List.map(fun a-> remplacerValPar0  var a)args)
	| VARIABLE (s) 				->	if s = var then CONSTANT (CONST_INT "0") else expr
	| _ 						-> 	expr

let rec remplacerValPar  var nouexp expr =
	match expr with
	NOTHING 					-> NOTHING
	| UNARY (op, exp) 			-> UNARY (op, remplacerValPar   var nouexp exp)
	| BINARY (op, exp1, exp2) 	-> BINARY (op, remplacerValPar   var nouexp exp1, remplacerValPar   var nouexp exp2)
	| CALL (exp, args) 			->	CALL (exp, List.map(fun a-> remplacerValPar  var nouexp a)args)
	| VARIABLE (s) 				->	if s = var then nouexp else expr
	| _ 						-> 	expr



let rec remplacerNOTHINGPar  expr =
	match expr with
	NOTHING 					-> VARIABLE ("NODEF") 
	| UNARY (op, exp) 			-> UNARY (op, remplacerNOTHINGPar    exp)
	| BINARY (op, exp1, exp2) 	-> BINARY (op, remplacerNOTHINGPar exp1, remplacerNOTHINGPar exp2)
	| CALL (exp, args) 			->	CALL (exp, List.map(fun a-> remplacerNOTHINGPar a)args)
	| VARIABLE (s) 				->	expr
	| _ 						-> 	expr

let remplacerNOTHINGParAux e =
match e with MULTIPLE ->VARIABLE ("NODEF") | EXP (e) -> if e = NOTHING then VARIABLE ("NODEF")  else remplacerNOTHINGPar e 
	
let rec  calculer expressionVA ia l=
	match expressionVA with
	EXP  (expr) ->
	(	match expr with
		NOTHING -> (*Printf.printf "calculer NOTHING\n";*)NOCOMP
		| UNARY (op, exp) ->
			begin
				let val1 = calculer (EXP exp) ia l in 
				
					match op with
					MINUS ->  	if estNoComp val1   then NOCOMP else 	evalexpression(	Diff (ConstInt ("0"), val1)) (*voir*)
					| PLUS ->  	if estNoComp val1   then NOCOMP else	evalexpression	val1 (*voir*)
					| NOT ->  	if estNoComp val1   then NOCOMP
								else (* print_expTerm val1;new_line();*)
									if val1 = Boolean(true) || val1 = ConstInt ("1") 
										|| val1 = ConstFloat("1.0")
									then Boolean(false) 
									else	if val1 = Boolean (false) || val1 = ConstInt ("0")  ||	val1 = ConstFloat("0.0")							
											then Boolean(true) else NOCOMP (*neg*)
					| BNOT -> 	NOCOMP
					| MEMOF  -> (*Printf.printf" calculer MEMOF\n";print_expression exp 0; new_line();*)
						( match exp with  UNARY(ADDROF, exp2) ->   calculer (EXP exp2) ia l 
											|_-> NOCOMP)
					| ADDROF ->   
						( match exp with  UNARY(MEMOF, exp2) ->  calculer (EXP exp2) ia l 
										  
											|_-> NOCOMP)
					| PREINCR ->  	if estNoComp val1   then NOCOMP else evalexpression (Sum (val1, ConstInt ("1")) )
					| PREDECR ->   	if estNoComp val1   then NOCOMP else evalexpression (Diff (val1, ConstInt ("1")) )
					| POSINCR ->  	if estNoComp val1   then NOCOMP else evalexpression (Sum (val1, ConstInt ("1")) )
					| POSDECR ->  	if estNoComp val1   then NOCOMP else evalexpression (Diff (val1, ConstInt ("1")) )
					
				
			end
		| BINARY (op, exp1, exp2) ->
			if !vDEBUG then 
			begin 
				Printf.printf"binary\n";print_expression exp1 0;new_line ()	; 
				print_expression exp2 0;new_line () 
			end;
			let val1 = (calculer (EXP(exp1 )) ia l) in 
			(*Printf.printf"var1\n "; print_expTerm val1; new_line();*)
			let val2 = (calculer (EXP(exp2 )) ia l) in 
			(*Printf.printf"var2\n "; print_expTerm val2;new_line();*)
			if estNoComp val1 || estNoComp val2 then 
				if op = OR then 
					if estNoComp val1  then 
					 	if estNoComp val2 then NOCOMP 
						else (val2)
					else (val1)
				else NOCOMP  
			else
			begin

				match op with
				ADD		->  evalexpression (Sum (val1, val2)) 	
				| SUB		->  evalexpression (Diff (val1, val2)) 	
				| MUL	   	->  evalexpression (Prod (val1, val2)) 	
				| DIV		->  evalexpression (Quot (val1, val2)) 
				| MOD		->  evalexpression (Mod (val1, val2)) 	
				| SHL 		->  evalexpression (Shl (val1, val2)) 
				| SHR		->  evalexpression (Shr (val1, val2)) 		
				| EQ 		->  
			(*	Printf.printf"EQ exp1 , exp2\n";  print_expTerm val1; new_line(); print_expTerm val2;new_line();*)

				if estBool val1 && estBool val2 then if val1 = val2   then Boolean(true)  else Boolean (false)
				else if estDefExp val1  &&  estDefExp val2 then 
				begin
									let diff = evalexpression (Diff (val1, val2 )) in
									if estNul diff then Boolean(true) 
									else Boolean (false)
								end
								else NOCOMP
				
				
				| NE-> 	
(*Printf.printf"NEQ exp1 , exp2\n";  print_expTerm val1; new_line(); print_expTerm val2;new_line();*)
						if estBool val1 && estBool val2 then if val1 = val2  then Boolean(false)  else Boolean (true)
						else if estDefExp val1 && estDefExp val2 then 
								if estNul (evalexpression (Diff (val1, val2 ))) then Boolean(false) 
								else Boolean (true)
						else NOCOMP

				| LT -> if estDefExp val1 && estDefExp val2 then 
							if estPositif  (evalexpression (Diff (val1, val2 ))) then Boolean(false)  else Boolean (true)
						else NOCOMP
				| GT -> if estDefExp val1 && estDefExp val2 then 
							if estStricPositif  (evalexpression (Diff (val1, val2 ))) then Boolean(true) 
							else Boolean (false)
						else NOCOMP
				| LE -> if estDefExp val1 && estDefExp val2 then 
							if estStricPositif (evalexpression (Diff (val1, val2 ))) then  Boolean(false) 
							else Boolean (true)
						else NOCOMP
				| GE -> if estDefExp val1 && estDefExp val2 then 
							if estPositif (evalexpression (Diff (val1, val2 ))) then Boolean(true) 
							else Boolean (false)
						else NOCOMP
				| AND |OR ->
					let (resb1,comp1) = 
						(	if val1 = Boolean(true) || val1 = ConstInt ("1")  || val1 = ConstFloat("1.0")
							then (true,true)
							else 
								if val1 = Boolean (false) || val1 = ConstInt ("0")  ||val1 = ConstFloat("0.0")									
								then (false, true) else (false, false) )in
					let (resb2, comp2) = 
						(	if val2 = Boolean(true) || val2 = ConstInt ("1")   || val2 = ConstFloat("1.0")	
							then (true,true)
							else 
								if val2 = Boolean (false) || val2 = ConstInt ("0")  ||val2 = ConstFloat("0.0")									
								then (false, true) else (true, false) )in

(*estBoolOrVal*)
					if comp1 = false && comp2 = false then begin (*Printf.printf " NOCOMP AND OR \n";*)NOCOMP end
					else
					begin
						if op = OR then 
						begin 
								if comp1 = false  then Boolean(resb2 )
								else if comp2 = false then Boolean(resb1) else  Boolean(resb1 || resb2) 
						end
						else  if comp1 = false ||  comp2 = false then NOCOMP else   Boolean(resb1 && resb2) 
						
					end
				| BAND	| BOR| XOR	| ASSIGN | ADD_ASSIGN
				| SUB_ASSIGN| MUL_ASSIGN| DIV_ASSIGN | MOD_ASSIGN | BAND_ASSIGN	|BOR_ASSIGN
				| XOR_ASSIGN
				| SHL_ASSIGN| SHR_ASSIGN	->  NOCOMP
			end
			| QUESTION (_, _, _) ->	NOCOMP
			| CAST (_, e) ->		calculer (EXP(e)) ia l
			| CALL (exp, args) ->	
			(match exp with
				
				VARIABLE("partieEntiereInf") -> 
					if !vDEBUG then 
					begin Printf.printf"\ncalcul partieEntiereInf expression\n";
						print_expression (List.hd args) 0;		new_line ()	
					end;
					let val1 =  (calculer (EXP(List.hd args)) ia l)in
					if estNoComp val1  then 
					begin (*Printf.printf"NO COMP partieEntiereInf\n";*)	NOCOMP end
					else evalexpression (PartieEntiereInf (val1)) 	
															  
				|VARIABLE("partieEntiereSup") ->
					let val1 = evalexpression (calculer (EXP(List.hd args)) ia l)in
					if estNoComp val1  then 
					begin (*Printf.printf"NO COMP partieEntiereSup\n";	*)NOCOMP end
					else evalexpression (PartieEntiereSup (val1)) 	
				|VARIABLE("pow10") ->
					let val1 = evalexpression (calculer (EXP(List.hd args)) ia l)in
					if estNoComp val1  then  NOCOMP  
					else  evalexpression (Puis  (val1, ConstInt("10"))	)
				|VARIABLE("pow") ->
					let val1 = evalexpression (calculer (EXP(List.hd args)) ia l)in
					if estNoComp val1  then 
					begin (*Printf.printf"NO COMP partieEntiereSup\n";	*)NOCOMP end
					else
					begin
						let suite = List.tl args in
						let val2 = (calculer (EXP(List.hd suite )) ia l)in
						if estNoComp val2   then  NOCOMP else evalexpression (Puis  (val1, val2)) 
					end
				|VARIABLE("MAXIMUM") ->
					let val1 = evalexpression (calculer (EXP(List.hd args)) ia l)in
					if estNoComp val1  then 
					begin (*Printf.printf"NO COMP partieEntiereSup\n";	*)NOCOMP end
					else
					begin
						let suite = List.tl args in
						let val2 = (calculer (EXP(List.hd suite )) ia l)in
						if estNoComp val2   then  NOCOMP  
						else evalexpression (Maximum  (val1, val2)) 
					end		
				|VARIABLE("MINIMUM") ->
					let val1 = evalexpression (calculer (EXP(List.hd args)) ia l) in
					if (List.tl args ) <> [] then 
					begin 
						let val2 = evalexpression (calculer (EXP(List.hd (List.tl args ))) ia l )in	
					
						if estNoComp val1   then val2
						else 	if estNoComp val2   then   val1   
								else evalexpression (Minimum  (val1, val2)) 
					end
					else val1
				|VARIABLE("log") ->
					let val1 = evalexpression (calculer (EXP(List.hd args)) ia l)in
					if estNoComp val1   then 
					begin (*Printf.printf"NO COMP partieEntiereSup\n";	*)NOCOMP end
					else evalexpression (Log (val1)) 	
				|VARIABLE("log10") ->
					let val1 = evalexpression (calculer (EXP(List.hd args)) ia l)in
					if estNoComp val1   then 
					begin (*Printf.printf"NO COMP partieEntiereSup\n";	*)NOCOMP end
					else evalexpression (Quot (Log (val1), Log(ConstInt("10") ) ) 	)
				|VARIABLE("log2") -> 
					let val1 = evalexpression (calculer (EXP(List.hd args)) ia l)in
					if estNoComp val1   then 
					begin (*Printf.printf"NO COMP partieEntiereSup\n";	*)NOCOMP end
					else evalexpression  (Quot (Log (val1), Log(ConstInt("2") ) ) 	)
				|VARIABLE("max") ->
					let val1 = evalexpression (calculer (EXP(List.hd args)) ia l)in
					if estNoComp val1   then 
					begin (*Printf.printf"NO COMP partieEntiereSup\n";	*)NOCOMP end
					else val1
				|VARIABLE("SYGMA") -> 		
				 begin
					if !vDEBUG then Printf.printf"SYGMA\n";
					let varexp = ( List.hd args )in
				 	let suite = List.tl args in
					match varexp with	
					VARIABLE (var) ->												
						let max = (calculer (EXP(List.hd suite )) ia l)in
						if  estNoComp max   then NOCOMP
						else
						begin
							if !vDEBUG then 
							begin
								Printf.printf"SYGMA simplifier\n";
								Printf.printf"SYGMA pour %s =\n" var;
								Printf.printf"SYGMA pour %s expression simplifier\n" var;
								Printf.printf "evalexpression max\n"; 
								print_expTerm max; new_line ();
								print_expression (List.hd (List.tl suite) ) 0;new_line ();
							end;
							if List.mem var l then NOCOMP
							else
							begin
								let expE = (calculer  (EXP(List.hd (List.tl suite) ))ia  (List.append [var] l) ) in
								if  estNoComp expE   then  NOCOMP
								else
								begin
									let val1 = simplifier var max expE ia in
									if  estNoComp val1 then   Sygma (var ,ConstInt("0")(* ou 1 voir*), max,expE)
									else	val1
								end	
							end
						end			
					|_-> NOCOMP
				end					
				|VARIABLE("MAX") -> 		
				begin
					if !vDEBUG then Printf.printf"MAX\n";
				 	let varexp = ( List.hd args )in
				 	let suite = List.tl args in
					match varexp with
					VARIABLE (var) ->												
						let max = (calculer (EXP(List.hd suite )) ia l)in
						if  estNoComp max   then NOCOMP
						else
						begin
							if !vDEBUG then 
							begin
								Printf.printf"MAX simplifier\n";
								Printf.printf"MAX pour %s = O..\n" var;
								
								print_expTerm max; new_line ();Printf.printf" ( " ;
								print_expression (List.hd (List.tl suite) ) 0;new_line ();
								Printf.printf" ) " ;
							end;
							if estDefExp max && estNul max then 
							begin
							(*	Printf.printf "remplacer max\n"	;*)
								calculer  (EXP
											(remplacerValPar0 var (List.hd (List.tl suite)) ))
								ia l 
							end
							else
							begin
								let expE = (calculer  (EXP(List.hd (List.tl suite) ))ia l) in
								if estNoComp expE  then  NOCOMP
								else
								begin		
									let val1 = simplifierMax var max expE ia in
									(*Printf.printf"calcul MAX pour %s =\n" var; 
									print_expTerm val1; new_line ();
									Printf.printf"MAX apres calcul =\n";*)
									if  estNoComp val1 then  NOCOMP
										(*Max (var ,ConstInt("0")(* ou 1 voir*), max,expE)*)
									else	val1
								end	
							end
						end																	
														
					|_-> NOCOMP
				end
				|_-> (*|VARIABLE("MAX") -> *)	NOCOMP
			)
			| COMMA _ ->					NOCOMP
			| CONSTANT cst -> 													
				(	match cst with
						CONST_INT i 	->	  	 (ConstInt(Printf.sprintf "%d" (string_to_int  i)))
						| CONST_FLOAT r ->	   	 (ConstFloat(Printf.sprintf "%f" (string_to_float  r)))
						| CONST_CHAR _ 	|CONST_STRING _ | CONST_COMPOUND _ ->	NOCOMP
				)
			| VARIABLE (s) ->		 (Var(s))
			| _ -> 	NOCOMP
	)
|	MULTIPLE -> NOCOMP

and estVarDsExpEval var expre =
match expre with
		NOCOMP 			-> false
	 	| Sum (f, g) 	->  (estVarDsExpEval var f) or (estVarDsExpEval var g)
		| Diff (f, g) 	->  (estVarDsExpEval var f) or (estVarDsExpEval var g)
		| Prod (f, g)  	->  (estVarDsExpEval var f) or (estVarDsExpEval var g)
		| Shr (f, g)  	->  (estVarDsExpEval var f) or (estVarDsExpEval var g)
		| Shl (f, g)  	->  (estVarDsExpEval var f) or (estVarDsExpEval var g)
		| Quot (f, g)	->  (estVarDsExpEval var f) or (estVarDsExpEval var g)
		| Puis (f, g)	->  (estVarDsExpEval var f) or (estVarDsExpEval var g)
		| Mod (f, g)	->  (estVarDsExpEval var f) or (estVarDsExpEval var g)
		| ConstInt(_) 	->  false
		| ConstFloat (_)->  false
		| Boolean (_) -> 	false
		| Var (s) -> 		if s = var then true else false
		| PartieEntiereSup (e)-> 	(estVarDsExpEval var e) 
		| Log (e)-> 		(estVarDsExpEval var e) 
	    | PartieEntiereInf (e)-> 	(estVarDsExpEval var e) 
   		| Sygma (v,min,max,exp)-> (estVarDsExpEval var min) or (estVarDsExpEval var max)or (estVarDsExpEval var exp) or v = var
    	| Max (v,min,max,exp)-> (estVarDsExpEval var min) or (estVarDsExpEval var max)or (estVarDsExpEval var exp)or v = var
  		| Eq1 (v)-> 		 (estVarDsExpEval var v) 
  		| Maximum (f, g)  -> (estVarDsExpEval var f) or (estVarDsExpEval var g)
		| Minimum (f, g)  -> (estVarDsExpEval var f) or (estVarDsExpEval var g)

and estAffine var expre =
if !vDEBUG then Printf.printf"SYGMA simplifier dans affine\n";
	match expre with
		NOCOMP -> false
	 	| Sum (f, g) 	->  (estAffine var f) && (estAffine var g)
		| Diff (f, g) 	->  (estAffine var f) && (estAffine var g)
		| Prod (f, g)  ->  	if (estVarDsExpEval var f = false) then (estAffine var g)
							else if (estVarDsExpEval var g = false) then (estAffine var f)  else false
		| Puis (f, g) ->  	if (estVarDsExpEval var f = false) && (estVarDsExpEval var g = false) then true else false
		| Quot (f, g)	->  if (estVarDsExpEval var g = false) then (estAffine var f)  else false
		| Shr (f, g)  ->	if (estVarDsExpEval var f = false) then (estAffine var g)
							else if (estVarDsExpEval var g = false) then (estAffine var f) else false
		| Shl (f, g)	->  if (estVarDsExpEval var g = false) then (estAffine var f)  else false
		| Mod (f, g)	->  if (estVarDsExpEval var g = false)then (estAffine var f)  else false
		| ConstInt(_)| Boolean(_) | ConstFloat (_) | Var (_) -> 		true
		| PartieEntiereSup (e)->  (estAffine var e) (*revoir*)
	    | PartieEntiereInf (e)->  (estAffine var e)
   	    | Sygma (v,_,_,_)-> 
			if v = var then false else
			if (estVarDsExpEval var expre = false) then true else false
  	    | Max (_,_,_,_)->   if (estVarDsExpEval var expre = false) then true else false
		| Log (_)->      	if (estVarDsExpEval var expre = false) then true else false
 		| Eq1 (v)-> 		(estAffine var v)
  		| Maximum (f, g)  -> if (estVarDsExpEval var f = false) && (estVarDsExpEval var g = false) then true else false 
  		| Minimum (f, g)  -> if (estVarDsExpEval var f = false) && (estVarDsExpEval var g = false) then true else false 
	
and remplacerVpM var max expre =
if !vDEBUG then Printf.printf"SYGMA simplifier avant remplacerVpM\n";
	match expre with
		  ConstInt(_)->evalexpression(Prod (expre,Sum(max, ConstInt("1"))))
		| ConstFloat (_)->evalexpression(Prod (expre, Sum(max, ConstInt("1")) )) 	
		| NOCOMP		->NOCOMP	
		| Var (s) -> if s = var then Quot ( Prod (max,(Sum (max, ConstInt("1"))) ) ,ConstInt("2")) (* n*(n+1)/2*)
					 else evalexpression(Prod (expre,Sum(max, ConstInt("1"))))
		| Sum (f, g)  -> Sum((remplacerVpM var max f) , (remplacerVpM var max g))
		| Diff (f, g)  -> Diff((remplacerVpM var max f) , (remplacerVpM var max g))
		| Prod (f, g)  -> if (estVarDsExpEval var g= false) then Prod((remplacerVpM var max f) , g)
								else Prod(f , (remplacerVpM var max g))
		| Shr (f, g)  -> if (estVarDsExpEval var g= false) then Shr((remplacerVpM var max f) , g)
								else Shr(f , (remplacerVpM var max g))
		| Mod (f, g)  	-> Mod((remplacerVpM var max f) ,  g)
		| Quot (f, g)  -> Quot((remplacerVpM var max f) ,  g)
		| Puis (_, _)  -> expre (* variable pas dans exp sinon pas affine *)
		| Shl (f, g)  -> Shl((remplacerVpM var max f) ,  g)
		| PartieEntiereSup (e)-> PartieEntiereSup(remplacerVpM var max e)
	    | PartieEntiereInf (e)-> PartieEntiereInf(remplacerVpM var max e)
	    | Log (e)-> Log(remplacerVpM var max e)
   	    | Sygma (v,min,maxi,e)-> Sygma(v, min,(remplacerVpM var max maxi) , (remplacerVpM var max e))
		| Max (v,min,maxi,e)-> Max(v, min,(remplacerVpM var max maxi) , (remplacerVpM var max e))
 		| Eq1 (v)-> (remplacerVpM var max v) 
		| Maximum (f, g)  ->  Maximum((remplacerVpM var max f) , (remplacerVpM var max g))
		| Minimum (f, g)  ->  Minimum((remplacerVpM var max f) , (remplacerVpM var max g))
		| _->expre


and remplacerVal var max expre =
(*if !vDEBUG then Printf.printf"SYGMA simplifier avant remplacerVpM\n";*)
	match expre with
		  ConstInt(_) | ConstFloat (_) | Boolean (_)->expre
		| NOCOMP			->NOCOMP	
		| Var (s) 	  -> if s = var then max else expre
		| Sum (f, g)  -> Sum((remplacerVal var max f) , (remplacerVal var max g))
		| Diff (f, g) -> Diff((remplacerVal var max f) , (remplacerVal var max g))
		| Prod (f, g) -> Prod((remplacerVal var max f) , (remplacerVal var max g))
		| Shr (f, g)  -> Shr((remplacerVal var max f) , (remplacerVal var max g))
		| Shl (f, g)  -> Shl((remplacerVal var max f) , (remplacerVal var max g))	
		| Mod (f, g)  -> Mod((remplacerVal var max f) , (remplacerVal var max g))
		| Quot (f, g) -> Quot((remplacerVal var max f) , (remplacerVal var max g))
		| PartieEntiereSup(e)-> PartieEntiereSup(remplacerVal var max e)
	    | PartieEntiereInf(e)-> PartieEntiereInf(remplacerVal var max e)
		| Log (e)	  -> Log(remplacerVal var max e)
   	    | Sygma (v,min,maxi,e)-> 
			if var <> v then Sygma(v, min,(remplacerVal var max maxi) , (remplacerVal var max e)) else expre
		| Max (v,min,maxi,e)-> 
			if var <> v then Max(v, min,(remplacerVal var max maxi) , (remplacerVal var max e)) else expre
		| Puis (v,e)  ->
			let (val1,val2) = (evalexpression (remplacerVal var max v) , evalexpression (remplacerVal var max e)) in
		if estNoComp val1 or estNoComp val2 then  NOCOMP else  Puis(val1 , val2)  
 		| Eq1 (v)		-> (remplacerVal var max v) 
		| Maximum (f, g)-> Maximum((remplacerVal var max f) , (remplacerVal var max g))
		| Minimum (f, g)-> Minimum((remplacerVal var max f) , (remplacerVal var max g))
		

and calculaetbAffineForne x expre = (* a*x+b d'une foction affine en x *)
	match expre with
		NOCOMP -> (ConstInt("0"),ConstInt("0"))
		| Boolean (_)->(ConstInt("0"),ConstInt("0"))
	 	| Sum (f, g) 	->  
			if (estVarDsExpEval x f = false) then
			begin 
				if (estVarDsExpEval x g = false) then 
					(ConstInt("0"), (evalexpression (Sum (evalexpression f, evalexpression g))))
				else 
				begin
					let (a1, b1) = calculaetbAffineForne x g in (a1 , evalexpression (Sum (evalexpression f, b1)) )
				end
			end
			else 
			begin
				if (estVarDsExpEval x g = false) then 
				begin
					let (a1, b1) = calculaetbAffineForne x f in (a1 , evalexpression (Sum (evalexpression g, b1)) )
				end
				else
				begin
					let (a1, b1) = calculaetbAffineForne x f in
					let (a2, b2) =  calculaetbAffineForne x g in
					(evalexpression (Sum (a1, a2)),evalexpression( Sum (b1, b2)) ) 
							(*a1x+b1+a2x+b2 =(a1+a2)x+(b1+b2)*)
				end
			end
		| Diff (f, g) 	->  
			if (estVarDsExpEval x f = false) then
			begin 
				if (estVarDsExpEval x g = false) then 
					( ConstInt("0"),
					 (evalexpression (Sum (evalexpression f, evalexpression (Diff (ConstInt("0"),evalexpression g)) ))))
				else 
				begin
					let (a1, b1) = calculaetbAffineForne x g in
					(
						evalexpression (Diff (ConstInt("0"), a1)),
						evalexpression (Sum  (evalexpression f,   evalexpression (Diff (ConstInt("0"), b1)) )))
				end
			end
			else 
			begin
				if (estVarDsExpEval x g = false) then 
				begin
					let (a1, b1) = calculaetbAffineForne x f in
					(a1 , evalexpression (Sum  (b1,  evalexpression (Diff (ConstInt("0"),evalexpression g)) )))
				end
				else  
				begin
					let (a1, b1) = calculaetbAffineForne x f in
					let (a2, b2) =  calculaetbAffineForne x g in
					( evalexpression (Sum (a1, evalexpression (Diff (ConstInt("0"),a2)))),
					  evalexpression( Sum (b1, evalexpression (Diff (ConstInt("0"),b2))) )) 
								(*a1x+b1+a2x+b2 =(a1+a2)x+(b1+b2)*)
				end
			end
		| Prod (f, g)  ->  
			if (estVarDsExpEval x f = false) then (* f constante*) 
			begin
			 	if (estVarDsExpEval x g = false) then 
					(ConstInt("0"),evalexpression (Prod (evalexpression f, evalexpression g) ))
				else
				begin (*Printf.printf "pas dans f mais dans g\n";*)
					let (a1, b1) = calculaetbAffineForne x g in
					(evalexpression (Prod (evalexpression f, a1)), evalexpression (Prod (evalexpression f, b1)))
				end
				end
			else
				if (estVarDsExpEval x g = false) then 
				begin
					let (a1, b1) = calculaetbAffineForne x f in
					(evalexpression (Prod (evalexpression g, a1)), evalexpression (Prod (evalexpression g, b1)))
				end
			else (ConstInt("0"),ConstInt("0"))
		| Shr (f, g)  ->  
				if (estVarDsExpEval x f = false) then (* f constante*) 
				begin
					 if (estVarDsExpEval x g = false) then 
						(ConstInt("0"),evalexpression (Shr (evalexpression f, evalexpression g) ))
					 else
					 begin (*Printf.printf "pas dans f mais dans g\n";*)
						let (a1, b1) = calculaetbAffineForne x g in
						 (evalexpression (Shr (evalexpression f, a1)), evalexpression (Shr (evalexpression f, b1)))
					 end
				end
				else
				 	if (estVarDsExpEval x g = false) then 
					begin
						 let (a1, b1) = calculaetbAffineForne x f in
						 (evalexpression (Shr (evalexpression g, a1)), evalexpression (Shr (evalexpression g, b1)))
					end
					else (ConstInt("0"),ConstInt("0"))
		| Quot (f, g)	->  
				if (estVarDsExpEval x g = false) then 
				begin
					if (estVarDsExpEval x f = false) then 
						(ConstInt("0"),evalexpression (Quot (evalexpression f, evalexpression g) ))
					else					
					begin
						let (a1, b1) = calculaetbAffineForne x f in
						let (fa1, fb1) = (( match a1 with  ConstInt(j) -> ConstFloat(j) |_-> a1),
										  ( match b1 with  ConstInt(j) -> ConstFloat(j) |_-> b1) ) in
						(evalexpression (Quot ( fa1, evalexpression g)), evalexpression(Quot ( fb1, evalexpression g)))
					end
				end
				else (ConstInt("0"),ConstInt("0"))
		|  Puis (f, g)	->   (ConstInt("0"),ConstInt("0"))
		|  Mod (f, g)	->  
				if (estVarDsExpEval x g = false) then 
				begin
					if (estVarDsExpEval x f = false) then 
						(ConstInt("0"),evalexpression (Mod (evalexpression f, evalexpression g) ))
					else					
					begin
						let (a1, b1) = calculaetbAffineForne x f in
						let (fa1, fb1) = (( match a1 with  ConstInt(j) -> ConstFloat(j) |_-> a1),
										  ( match b1 with  ConstInt(j) -> ConstFloat(j) |_-> b1) ) in
						(evalexpression (Mod ( fa1, evalexpression g)), evalexpression(Mod ( fb1, evalexpression g)))
					end
				end
				else (ConstInt("0"),ConstInt("0"))
		|  Shl (f, g)	->  
				if (estVarDsExpEval x g = false) then 
				begin
					if (estVarDsExpEval x f = false) then 
						(ConstInt("0"),evalexpression (Shl (evalexpression f, evalexpression g) ))
					else					
					begin
						let (a1, b1) = calculaetbAffineForne x f in
						let (fa1, fb1) = (( match a1 with  ConstInt(j) -> ConstFloat(j) |_-> a1),
										  ( match b1 with  ConstInt(j) -> ConstFloat(j) |_-> b1) ) in
						(evalexpression (Shl ( fa1, evalexpression g)), evalexpression(Shl ( fb1, evalexpression g)))
					end
				end
				else (ConstInt("0"),ConstInt("0"))
		| ConstInt(_) -> (ConstInt("0"),evalexpression expre)
		| ConstFloat (_) -> (ConstInt("0"),evalexpression expre)
		| Var (v) -> if v = x then (ConstInt("1"), ConstInt("0")) else (ConstInt("0"),Var (v))
		| PartieEntiereSup (e)->  	(* evalexpression (PartieEntiereSup*)
									let (a1, b1) =calculaetbAffineForne x e 	in 
									( a1, evalexpression (PartieEntiereSup b1))		
	    | PartieEntiereInf (e)->  	 	let (a1, b1) =calculaetbAffineForne x e 	in 
									( a1, evalexpression (PartieEntiereInf b1))
	    | Log (e)->  	 	let (a1, b1) =calculaetbAffineForne x e 	in 
									( a1, evalexpression (Log b1))
   	    | Sygma (_,_,_,_)->     (ConstInt("0"),evalexpression expre)
		| Max (_,_,_,_)->     (ConstInt("0"),evalexpression expre)	
		| Eq1 (v)->  calculaetbAffineForne x v 		
		|  Maximum (f, g)  ->  
			if (estVarDsExpEval x f = false) && (estVarDsExpEval x g = false) then 
					(	ConstInt("0"), (evalexpression  (Maximum (evalexpression f, evalexpression g)) ))
			else (	ConstInt("0"), ConstInt("0"))
		|  Minimum (f, g)  ->  
			if (estVarDsExpEval x f = false) && (estVarDsExpEval x g = false) then 
					(	ConstInt("0"), (evalexpression  (Minimum (evalexpression f, evalexpression g)) ))
			else (	ConstInt("0"), ConstInt("0"))

and sensVariation var max expre ia =
	if (estAffine var expre)   then 
	begin 
		let (a,b) = calculaetbAffineForne var expre in		
		let (var1, var2) = (evalexpression a , evalexpression b) in
		if  (estStricPositif var1) then CROISSANT
		else begin if (estNul var1) then  CONSTANTE  else DECROISSANT end
	end
	else 
	begin
	let sensRes =
	(
		match expre with
			NOCOMP -> NONMONOTONE
		 	| Sum (f, g) 	->  
				let sensf = sensVariation var max f ia in
				let sensg =  sensVariation var max g ia in
				(*Printf.printf "Sum sens f g\n" ; printSens sensf; printSens sensg;*)
				if (sensf = sensg) then sensf 
				else if (sensf <> NONMONOTONE) && (sensg = CONSTANTE) then  sensf
					 else if (sensg <> NONMONOTONE) && (sensf = CONSTANTE) then  sensg
						  else NONMONOTONE
			| Diff (f, g) 	->
				let sensf = sensVariation var max f ia in
				let sensg =  sensVariation var max g ia in
				(*Printf.printf "Diff sens f , g\n" ;printSens sensf; printSens sensg;*)
				(match sensf with
					CONSTANTE ->
						if   (CONSTANTE = sensg )  then CONSTANTE
						else (* sensg != CONSTANTE *)
							if (sensg =  DECROISSANT) then  CROISSANT  
							else if sensg  = CROISSANT then DECROISSANT else NONMONOTONE
				   | NONMONOTONE -> NONMONOTONE
				   | CROISSANT ->
						if ( sensg = CONSTANTE) || (sensg =  DECROISSANT) then  CROISSANT  else NONMONOTONE
						
					| DECROISSANT->
						if ( sensg = CONSTANTE) || (sensg =  CROISSANT) then  DECROISSANT   else NONMONOTONE
				)
			| Prod (f, g)| Shr (f, g) |  Puis (f, g)  ->  
				let sensf = sensVariation var max f ia in
				let sensg =  sensVariation var max g ia in
				(*Printf.printf "Prod sens f , g\n" ;printSens sensf; printSens sensg;*)
				(match sensf with
					CONSTANTE ->
						if   (CONSTANTE = sensg )  then CONSTANTE
						else (* sensg != CONSTANTE *)
							if estNul f then  CONSTANTE 
							else 
								if (estStricPositif f) then  sensg
								else if (sensg = CROISSANT) then DECROISSANT else CROISSANT
				   | NONMONOTONE -> NONMONOTONE
				   | CROISSANT ->
						if sensg  = CROISSANT then CROISSANT
						else 
							if ( sensg = CONSTANTE) then
								if (estStricPositif g) then  sensf
								else  if estNul g then  CONSTANTE else DECROISSANT  
							else NONMONOTONE
						
					| DECROISSANT->
						if (sensg  = DECROISSANT)  then DECROISSANT
						else if sensg  = CONSTANTE then
								if (estStricPositif g)   then DECROISSANT
								else  if (estNul g) then  CONSTANTE else CROISSANT 	
							 else NONMONOTONE
				)
			| Quot (f, g)	|  Mod (f, g) 	|  Shl (f, g)->  
				let sensf = sensVariation var max f ia in
				let sensg =  sensVariation var max g ia in
(*Printf.printf "Quot sens f , g\n" ;printSens sensf; printSens sensg;*)
				(match sensf with
					CONSTANTE ->
						if   (CONSTANTE = sensg )  then CONSTANTE
						else 
							if estNul f then  CONSTANTE 
							else 
								if (estStricPositif f) then  
									if sensg = CROISSANT then DECROISSANT else CROISSANT 
								else  sensg
				   | NONMONOTONE -> NONMONOTONE
				   | CROISSANT ->
						if sensg  = DECROISSANT then CROISSANT
						else if sensg  = CONSTANTE then
								if (estStricPositif g)   then CROISSANT
								else DECROISSANT
							else NONMONOTONE
					| DECROISSANT->
						if (sensg  = CROISSANT)  then DECROISSANT
						else if sensg  = CONSTANTE then
								if (estStricPositif g)   then DECROISSANT
								else CROISSANT
							else NONMONOTONE
				)
								 
			| ConstInt(_) | ConstFloat (_)  -> CONSTANTE
			| Var (_) ->  CROISSANT 
			| PartieEntiereSup (e)  | PartieEntiereInf (e)  | Log (e)->  	 	sensVariation var max e ia
	   	    | Sygma (_,_,_,exp)->    let sensexp = sensVariation var max exp ia  in
									 if (sensexp = CROISSANT  ) || (sensexp = CONSTANTE  )then CROISSANT
									 else NONMONOTONE
			| Max (_,_,_,exp)->      sensVariation var max exp ia 
			| Eq1 (v)->  NONMONOTONE 		
			|  Maximum (f, g)  ->  
				let sensf = sensVariation var max f ia in
				let sensg =  sensVariation var max g ia in
				
				if (sensf  = CONSTANTE) && (sensg  = CONSTANTE ) then CONSTANTE
				else	if ((sensf  = CROISSANT) || (sensf  = CONSTANTE) )
								&& ((sensg  = CROISSANT) || (sensg  = CONSTANTE))  then CROISSANT
					else if ((sensf  = DECROISSANT) || (sensf  = CONSTANTE)) &&
						 ((sensg  = DECROISSANT) ||(sensg  = CONSTANTE))  then DECROISSANT  else NONMONOTONE
		   |  Minimum (f, g)  ->  
				let sensf = sensVariation var max f ia in
				let sensg =  sensVariation var max g ia in
				
				if (sensf  = CONSTANTE) && (sensg  = CONSTANTE ) then CONSTANTE
				else	if ((sensf  = CROISSANT) || (sensf  = CONSTANTE) )
								&& ((sensg  = CROISSANT) || (sensg  = CONSTANTE))  then CROISSANT
					else if ((sensf  = DECROISSANT) || (sensf  = CONSTANTE)) &&
						 ((sensg  = DECROISSANT) ||(sensg  = CONSTANTE))  then DECROISSANT  else NONMONOTONE	
	  	   | Boolean (_)->NONMONOTONE
	) in
(*printSens sensRes; Minimum*)
sensRes
	end
(* terminer *)
and estCroissantOuCte var max expre ia =
let sens = sensVariation  var max expre ia in
sens = CROISSANT || sens = CONSTANTE  

and estDecroissantOuCte var max expre ia =
let sens = sensVariation  var max expre ia in
sens = DECROISSANT || sens = CONSTANTE 

and simplifierSYGMA var max expre ia =
	match expre with
		NOCOMP -> NOCOMP
	 	| Sum (f, g) 	->  
			if (estVarDsExpEval var f = false) then
			begin 
				if (estVarDsExpEval var g = false) then 
					(*let maximum = simplifierMax var max val2 ia in*)
					evalexpression (Prod (Sum(max,ConstInt("1")), expre))
				else 
					evalexpression ( Sum ( evalexpression (Prod (Sum(max,ConstInt("1")), f)),
										  simplifierSYGMA var max g ia	))
			end
			else 
			begin
				if (estVarDsExpEval var g = false) then 
					evalexpression ( Sum ( simplifierSYGMA var max f ia	,
										  evalexpression (Prod (Sum(max,ConstInt("1")), g))
										 ))
				else
					evalexpression ( Sum  ( simplifierSYGMA var max f ia,  simplifierSYGMA var max g ia	))
			end
		| Diff (f, g) 	->  
			if (estVarDsExpEval var f = false) then
			begin 
				if (estVarDsExpEval var g = false) then 
					(*let maximum = simplifierMax var val1 val2 ia in*)
					evalexpression (Prod (Sum(max,ConstInt("1")), expre))
				else 
					evalexpression ( Diff 
										( evalexpression (Prod (Sum(max,ConstInt("1")), f)),
										  simplifierSYGMA var max g ia	))
			end
			else 
			begin
				if (estVarDsExpEval var g = false) then 
					evalexpression ( Diff ( simplifierSYGMA var max f ia	,
										  evalexpression (Prod (Sum(max,ConstInt("1")), g))
										 ))
				else
					evalexpression ( Diff  ( simplifierSYGMA var max f ia,  simplifierSYGMA var max g ia	))
			end
	
		| Prod (f, g)  | Shr (f, g) ->  
				if (estVarDsExpEval var f = false) then (* f constante*) 
				begin
					 if (estVarDsExpEval var g = false) then 
						evalexpression(Prod (Sum(max,ConstInt("1")), expre))
					 else
					 begin 
						(*Printf.printf "pas dans f mais dans g\n";
						 print_expTerm (evalexpression f);  new_line ();Printf.printf " * ";
 print_expTerm (simplifierSYGMA var max g ia);  new_line ();Printf.printf " \n\n ";*)
						evalexpression(Prod ( f, simplifierSYGMA var max g ia))
					 end
				end
				else
				 	if (estVarDsExpEval var g = false) then 
					begin
						if expre =  Prod (f, g) then evalexpression(Prod ( simplifierSYGMA var max f ia, g))
						else  evalexpression(Shr ( simplifierSYGMA var max f ia, g))
					end 
					else 
					begin
                        if ((sensVariation var max  f ia = CROISSANT) && (sensVariation var max g ia = CROISSANT) )
						|| ((sensVariation var max f ia = DECROISSANT) && (sensVariation var max g ia =DECROISSANT))then
						begin
							let maximum = simplifierMax var max expre ia in
							if (estNoComp maximum) || estNul maximum then begin (*Printf.printf "NOCOMP2\n";*)NOCOMP end
							else  evalexpression (Prod (Sum(max,ConstInt("1")), maximum))
						end
						else NOCOMP
					end
		 	
			|  Mod (f, g)	->  
				if (estVarDsExpEval var g = false) then 
					if (estVarDsExpEval var f = false) then evalexpression(Prod (Sum(max,ConstInt("1")), expre))
					else evalexpression(Mod (simplifierSYGMA var max f ia , g))
				else  NOCOMP
			| Quot (f, g)	|  Shl (f, g)->  
				if (estVarDsExpEval var g = false) then 
				begin
					if (estVarDsExpEval var f = false) then  evalexpression(Prod (Sum(max,ConstInt("1")), expre))
					else	
					begin
						let res = simplifierSYGMA var max f ia in
						if expre = Quot (f, g) 	then	evalexpression(Quot (res , g))
						else evalexpression(Shl (res , g))
					end
				end
				else if (estVarDsExpEval var f = false) then 	
					begin
						(* je ne sais simplifier que si g est de la forme  cte puiss var *)
						let valg = evalexpression g in
						(match valg with
							Puis(e,vare) ->if (estVarDsExpEval var e = false) then
										   begin
											let res = simplifierSYGMA var max (Puis(Quot(ConstInt("1"), e), vare)) ia in
											evalexpression(Quot (f, res) )
										  end
										 else NOCOMP
							| _-> NOCOMP
						)
					end
					else NOCOMP
		|  Puis (f, g)	->  
				if (estVarDsExpEval var g = false) then 
				begin
					if (estVarDsExpEval var f = false) then  evalexpression(Prod (Sum(max,ConstInt("1")), expre))
					else NOCOMP
				end
				else 
				begin
					if (estVarDsExpEval var f = false) then 
					begin
						if (estAffine var g)   then 
						begin 
							let (a,b) = calculaetbAffineForne var g in		
							let (var1, var2) = (evalexpression a , evalexpression b) in
							let resaux = evalexpression f in
							let maxPlusun = evalexpression (Sum(max,ConstInt("1"))) in
							if (estNul var1) ||( estNul (Diff(resaux, ConstInt("1")))) then maxPlusun
							else if  (estStricPositif var1) then 
								 begin 
									let q = evalexpression( Puis(f, var1)) in
									let unMoinsq = evalexpression( Diff (ConstInt("1"), q) ) in
									let unMoinqPuisitPlusun = evalexpression(Diff(ConstInt("1"), Puis(q, maxPlusun))) in
									evalexpression(Prod(Puis(f,var2), Quot(unMoinqPuisitPlusun, unMoinsq)))
								 end
								 else 
								 begin
									let q = evalexpression( Puis(f, Diff(ConstInt("0"),var1))) in
									let unMoinsq = evalexpression( Diff (ConstInt("1"), q) ) in
									let unMoinqPuisitPlusun = evalexpression(Diff(ConstInt("1"), Puis(q, maxPlusun))) in
									evalexpression(Prod(Puis(f,var2), Quot(unMoinqPuisitPlusun, unMoinsq)))
								 end
						end
						else NOCOMP
					end
					else NOCOMP
				end
		| ConstInt(_) 
		| ConstFloat (_) -> evalexpression (Prod (Sum(max,ConstInt("1")), expre))
		| Boolean (_)-> NOCOMP
		| Var (v) -> if v = var then evalexpression (Sygma (var , ConstInt("0"), max, Var (v)) )
					 else  evalexpression (Prod (Sum(max,ConstInt("1")), expre))
		| PartieEntiereSup (e) ->  evalexpression	(PartieEntiereSup(simplifierSYGMA var max e ia))
		| PartieEntiereInf (e)->  evalexpression	(PartieEntiereInf(simplifierSYGMA var max e ia))
		| Log (e)->  evalexpression	(Log(simplifierSYGMA var max e ia))
   	    | Sygma(v,inf,sup,e)-> evalexpression(Sygma (v,inf,simplifierSYGMA var max sup ia,simplifierSYGMA var max e ia))
		| Max (v,inf,sup,e)->  evalexpression(Max (v,inf,simplifierSYGMA var max sup ia,simplifierSYGMA var max e ia))
		| Eq1 (v)->  Eq1 (v)		
		|  Maximum (f, g)  ->  
			if (estVarDsExpEval var f = false) then
				if (estVarDsExpEval var g = false) then 
					evalexpression  (Maximum (evalexpression f, evalexpression g)) 
				else evalexpression  (Maximum (evalexpression f, simplifierSYGMA var max g ia)) 
			else if (estVarDsExpEval var g = false) then 
					evalexpression  (Maximum (simplifierSYGMA var max f ia, evalexpression g)) 
				else NOCOMP
		|  Minimum (f, g)  ->  
			if (estVarDsExpEval var f = false) then
				if (estVarDsExpEval var g = false) then 
					evalexpression  (Minimum (evalexpression f, evalexpression g)) 
				else evalexpression  (Minimum (evalexpression f, simplifierSYGMA var max g ia)) 
			else if (estVarDsExpEval var g = false) then 
					evalexpression  (Minimum (simplifierSYGMA var max f ia, evalexpression g)) 
				else NOCOMP
	
and evalProd var max expre ia=
	let val1 = evalexpression max in
	let val2 = evalexpression expre in
	(*Printf.printf "produit\n";
	print_expTerm val1; new_line ();Printf.printf"\n";
	print_expTerm  val2; new_line ();Printf.printf"\n";
	Printf.printf "produit\n";*)
	if (estNoComp val1) || (estNoComp val2 ) then begin (*Printf.printf "NOCOMP\n";*)NOCOMP end
	else 
	begin
		let res = simplifierSYGMA var val1 val2 ia in
		if estNoComp res then
			if (estCroissantOuCte var val1 val2 ia) || (estDecroissantOuCte var val1 val2 ia) then
			begin
				let maximum = simplifierMax var max expre ia in
				if (estNoComp maximum) || estNul maximum then begin (*Printf.printf "NOCOMP2\n";*) NOCOMP end
				else  evalexpression (Prod (Sum(max,ConstInt("1")), maximum))
			end
			else NOCOMP
		else res
	end

and invaq1 v = if v = ConstInt("0") then ConstInt("1") else if v = ConstInt("1") then ConstInt("0") else invaq1 v 

and simplifieraa var max expre ia =
	if !vDEBUG then 
	begin  
		Printf.printf "SYGMA simplifier avant affine\n";
		print_expTerm max; new_line ();Printf.printf"\n";
		print_expTerm expre; new_line ();Printf.printf"\n";
	end;
	if !vDEBUG then Printf.printf"SYGMA simplifier dans simplifier\n"; 
if estDefExp max = false then NOCOMP
else
if estNul max then (remplacerVpM  var (ConstInt("0")) expre) 
else
begin
    if (ia.sensVariationA = NONMONOTONE) then NOCOMP
	else
	begin		
		if ((estAffine var expre) && (estVarDsExpEval var max = false))  then 
		begin 
			(*Printf.printf"SYGMA simplifier dans simplifier affine\n"; *)
			let borneMaxSupposee = evalexpression (remplacerVpM  var max expre) in
			let borneInfSupposee = evalexpression (remplacerVpM  var (ConstInt("0")) expre) in

		if  estDefExp borneMaxSupposee && estDefExp borneInfSupposee then
		begin
			(*Printf.printf "bornes definies simplifier aa \n";*)
			let sensVariReel  =
			(	if estPositif borneMaxSupposee && estPositif borneInfSupposee then
				 	estPositif 
					( evalexpression (Diff( evalexpression borneMaxSupposee, borneInfSupposee))) 
				else if estPositif borneMaxSupposee && (estPositif borneInfSupposee =false) then
					 true
					 else 
						if (estPositif borneMaxSupposee =false) && (estPositif borneInfSupposee )
						then false
						else 
						estPositif ( evalexpression 
						(Diff( evalexpression borneMaxSupposee, borneInfSupposee))) = false
			) in

			if (estPositif borneMaxSupposee = false) && (estPositif borneInfSupposee =false) then  
			begin
				(*Printf.printf "pas dans la boucle\n";		*)	
				ConstInt("0")
			end
			else
			begin
				let (a,b) = calculaetbAffineForne var expre in		
				let (var1, var2) = (evalexpression a , evalexpression b) in
				let convFloat =  ( match var1 with  ConstInt(j) -> ConstFloat(j) |_-> var1) in
				let mbSura = 
					(if convFloat = ConstFloat("0") then ConstFloat("0")
					 else  evalexpression (Quot ( Diff	 ( ConstInt("0"),var2 )  , convFloat)))in
						(*-b/a*)
				let mbSuraInf = evalexpression 
							(PartieEntiereSup ( evalexpression (Diff (mbSura,ConstInt("1"))))) in
				let mbSuraSup = evalexpression 
							(PartieEntiereInf ( evalexpression (Sum  (mbSura,ConstInt("1"))))) in
				

			if  (estDefExp var1 && estDefExp var2) then
			begin
				if  (estPositif var1) then (* revoir ce test pour resludcmp.c*)   
				begin
					if  (sensVariReel = true) then
					begin
						(*Printf.printf"positif croissant\n";*)
						let maxMoinsMbSura=evalexpression (Diff( evalexpression max, mbSuraInf)) in
						if (estPositif maxMoinsMbSura) then
						begin
							let maximum = maxi mbSuraInf  (ConstInt("0"))  in
							if (maximum = ConstInt("0")) then 
								evalexpression (remplacerVpM var max expre) 
							else  evalexpression
								(Diff  ( evalexpression (remplacerVpM var max expre) ,  
								remplacerVpM var
									(evalexpression (Diff (mbSuraInf,ConstInt("1")))) expre) )
						end
						else  begin (*Printf.printf"CAS1\n";*)ConstInt("0")  end
					end
					else	(* decr*)
					begin
						(*Printf.printf"positif decroissant\n";*)
						let maxMoinsMbSura =evalexpression(Diff( evalexpression max, mbSuraSup)) in
						if (estPositif maxMoinsMbSura) then
						begin 
							let maximum = maxi mbSuraSup  (ConstInt("0"))  in
							if maximum = ConstInt("0") then 
							begin
							(*	Printf.printf "decroissant max = 0 maxMoinsMbSura >0\n";	*)	
								evalexpression (remplacerVpM var max expre)
							end
							else
							begin
								(*Printf.printf "decroissant max > 0maxMoinsMbSura >0\n"; *)
								evalexpression (Diff 
									( evalexpression (remplacerVpM var max expre) ,  
									 remplacerVpM  var  
									(evalexpression (Diff (mbSuraSup,ConstInt("1")))) expre) )
							end
						end
						else   begin (*Printf.printf"CAS2\n";*)ConstInt("0")  end
					end (*end decr*)
				end
				else (* var1 neg*)
				begin
					if  (sensVariReel = true) then
					begin (*Printf.printf"negatif croissant\n";*)
						if estPositif mbSuraSup then 
							evalexpression (remplacerVpM var (mini mbSuraSup  max) expre) 
						else  begin (*Printf.printf "CAS6\n";*) ConstInt("0")  	end
					end
					else		
					begin	(*Printf.printf"negatif decroissant\n";*)
						if estPositif mbSuraInf = false then  
							evalexpression (remplacerVpM var (ConstInt("0")) expre) 
						else  begin (*Printf.printf "CAS7\n";*) (ConstInt("0"))
							(*evalexpression (remplacerVpM var (maxi mbSuraInf  (ConstInt("0")))
 expre) *)  			end	
					end
				end
			end else NOCOMP
			end
			end (*estDef*)
			else NOCOMP
		end (*fin affine*)
		else (*non affine*)
		begin
			if  ((estVarDsExpEval var expre = false) && (estVarDsExpEval var max) )then 
				evalexpression(Prod (expre,Sum(max, ConstInt("1"))))
			else 
			begin 
				if !vDEBUG then Printf.printf"SYGMA simplifier non affine !!!\n"; 
			(*	 traiterGeometrique var expre max ia *) 
				evalProd var max expre ia
			end
		end
	end
end

and simplifier var max expre ia =
let simpli = simplifieraa var max expre ia in

let prodeng = evalProd var max expre ia in
if estNoComp simpli  && estNoComp prodeng  then 
begin
	if  estPositif (evalexpression (Diff( prodeng, simpli))) then simpli else  prodeng
end
else simpli
(*simpli*)

and simplifierMax var max expre ia =
	if !vDEBUG then 
	begin  
		Printf.printf "Max simplifier avant affine var %s \n" var;
		print_expTerm max; new_line ();
		print_expTerm expre; new_line ();
	end;

if ((estVarDsExpEval var expre = false) && (estVarDsExpEval var max = false))  then expre
else
begin
  if (ia.sensVariationA = NONMONOTONE) then NOCOMP
  else
  begin		
	if ((estAffine var expre) && (estVarDsExpEval var max = false))  then 
	begin 
	(*	Printf.printf"MAX simplifier dans simplifier affine\n"; *)
		let borneMaxSupposee = evalexpression (remplacerVpM  var max expre) in
		let borneInfSupposee = evalexpression (remplacerVpM  var (ConstInt("0")) expre) in
	if  estDefExp borneMaxSupposee && estDefExp borneInfSupposee then
	begin
		let sensVariReel  =
		  (if estPositif borneMaxSupposee && estPositif borneInfSupposee then
		  	estPositif (evalexpression (Diff( evalexpression borneMaxSupposee, borneInfSupposee))) 
			else 
				if estPositif borneMaxSupposee && (estPositif borneInfSupposee =false) then true
			 	else 
					if (estPositif borneMaxSupposee =false) && (estPositif borneInfSupposee)
					then false
					else 
						estPositif ( evalexpression (Diff( evalexpression borneMaxSupposee, borneInfSupposee))) = false
			) in

		if (estPositif borneMaxSupposee = false) && (estPositif borneInfSupposee =false) then 
		begin
			(*Printf.printf"MAXCAS1\n";*)
			if estDefExp borneMaxSupposee = true then 	ConstInt("0") else NOCOMP
		end
		else
		begin
			let (a,b) = calculaetbAffineForne var expre in		
			let var1 = evalexpression a in
			let var2 = evalexpression b in
			let convFloat =  ( match var1 with  ConstInt(j) -> ConstFloat(j) |_-> var1) in
			let mbSura =(if convFloat = ConstFloat("0") then ConstFloat("0")
						else  evalexpression (Quot ( Diff( ConstInt("0"),var2 ), convFloat)))in	
	(*-b/a*)

			let mbSuraInf =  evalexpression (PartieEntiereSup ( evalexpression (Diff (mbSura,ConstInt("1"))))) in
			let mbSuraSup =  evalexpression (PartieEntiereInf ( evalexpression (Sum (mbSura,ConstInt("1"))))) in	

			let bmaximum = 
			(
			if  (estDefExp var1 && estDefExp var2) then
			begin
				if  (estPositif var1)  then 
				begin
					if (sensVariReel = true ) then
					begin
						(*Printf.printf "a positif croissant\n";*)
						let maxMoinsMbSura=evalexpression(Diff( evalexpression max, mbSuraInf)) in
						if estPositif maxMoinsMbSura then
						begin (*Printf.printf"eval2\n";*)
							evalexpression (remplacerVal var max expre) 
						end
						else  begin (*Printf.printf"MAXCAS2\n";*)  ConstInt("0")  end
					end
					else
					begin
						(*Printf.printf "a positif decroissant\n";*)
						let maxMoinsMbSura=evalexpression (Diff( evalexpression max, mbSuraSup)) in
						if estPositif maxMoinsMbSura then
						begin
							(*Printf.printf "cas 2 decroissant \n";*)
							let maximum = maxi mbSuraSup  (ConstInt("0"))  in
							if maximum = ConstInt("0") then 
							begin (*Printf.printf"eval3\n";*)
								evalexpression (remplacerVal var (ConstInt("0")) expre)
							end
							else  
							begin (*Printf.printf"eval4\n";*)
								evalexpression ( remplacerVal  var  mbSuraSup expre) 
							end
						end
						else  begin  (*Printf.printf"MAXCAS3\n";*) ConstInt("0") end  
					end
				end
				else 
				begin
					if (sensVariReel = true )then
					begin
						if estPositif mbSuraSup then 
						begin
							(*Printf.printf"eval5\n";*)
							evalexpression (remplacerVal var (ConstInt("0")) expre)
						end
						else begin  (*Printf.printf"MAXCAS4\n";*) ConstInt("0") end  	
					end
					else
					begin			
						if estPositif mbSuraInf = false then (*revoir*)
						begin
							(*Printf.printf"eval6\n";*)
							 evalexpression (remplacerVal var (ConstInt("0")) expre)
						end
						else begin (*Printf.printf "cas 4\n";*) ConstInt("0")
					(*evalexpression (remplacerVal var (maxi mbSuraInf (ConstInt("0"))) expre) *) 							end	
					end						
				end
				end else NOCOMP
				) in
				(*Printf.printf "maximum5\n" ;*)(*print_expTerm bmaximum; new_line (); Printf.printf "maximum\n";*)
		if estPositif bmaximum then bmaximum else 
		begin  (*Printf.printf"MAXCAS5\n";*) ConstInt("0") end 
	end
end (*estDef*)
			else NOCOMP
	end
	else
	begin
		if  ((estVarDsExpEval var expre = false) && (estVarDsExpEval var max) )then 
		begin 
			if !vDEBUG then Printf.printf"MAX simplifier borne depend\n";
				evalexpression (expre)
		end
		else 
		begin 
			let sens = sensVariation var max  expre ia in
			(*printSens sens;*)
			if sens <> NONMONOTONE then
			begin
				(*traiterGeometrique var expre max ia *)
				let borneMaxSupposee = evalexpression (remplacerVal  var max expre) in
				let borneInfSupposee = evalexpression (remplacerVal  var (ConstInt("0")) expre) in
					
				(*if estMONOTONBE var max expr then*)
				if !vDEBUG then 
				begin
					Printf.printf"MAX simplifier non affine max expre max suppose min suppose\n"; 
					print_expTerm max; new_line ();Printf.printf"\n"; 
					print_expTerm expre; new_line ();Printf.printf"\n"; 
					print_expTerm borneMaxSupposee; new_line ();Printf.printf"\n"; 
					print_expTerm borneInfSupposee; new_line ();Printf.printf"\n"; 
				end;
				let maximum = maxi borneMaxSupposee  borneInfSupposee  in
	(*Printf.printf"maximum6\n"; *)
	(*print_expTerm maximum; new_line ();Printf.printf"\n"; *)
				if estPositif maximum  then maximum  else begin (* Printf.printf"MAXCAS6\n"; *) ConstInt("0") end 
				end
				else begin (*Printf.printf "non monotone\n";*) NOCOMP end
			end
		end
	end
end

let geometrique exp expvarB = 
BINARY(	DIV ,
		BINARY(	SUB,CONSTANT(CONST_INT("1")) , 
			CALL (VARIABLE("pow"),List.append	
				[exp] 
				[CALL (	VARIABLE("MAXIMUM") ,  List.append 
					  [CONSTANT(CONST_INT("0"))] [BINARY(ADD, VARIABLE expvarB, CONSTANT(CONST_INT("1")) )])
				] )),
		BINARY(SUB ,CONSTANT(CONST_INT("1")) , exp)
	)

											
let rec afficherLesAffectations listeAffect = List.iter (fun affect -> afficherUneAffect affect; flush();flush(); space(); new_line ()) listeAffect
and afficherUneAffect affect =
	Printf.printf "\t\t\t\t\t";
	match affect with
	 VAR ( id, expVA1) 				->	 Printf.printf "%s  <- " id ;  flush (); print_expVA expVA1; flush(); space();
	|  MEMASSIGN ( id, expVA1, expVA2)	->	 Printf.printf "%s  <- (" id ; flush (); print_expVA expVA1; flush(); space();
																 Printf.printf " ) <- ";flush(); space(); 
											 flush (); print_expVA expVA2; flush(); space();
	| TAB ( id, expVA1, expVA2) 	->   Printf.printf "%s  [" id ; flush (); print_expVA expVA1; flush(); space();
										 Printf.printf " ] <- "; print_expVA expVA2; 	flush(); space();
	| IFVF ( expVA1, i1, i2) 		->
			Printf.printf  "if (";	print_expVA expVA1;flush(); space(); Printf.printf  ")"; new_line (); 
			Printf.printf "{";		indent (); afficherUneAffect i1;flush(); space(); new_line (); unindent ();
			Printf.printf "}";new_line ();
			Printf.printf  "else "; 
			Printf.printf "{";		indent (); afficherUneAffect i2; flush(); space();	unindent ();
			Printf.printf "}"; new_line ()
	| IFV ( expVA1, i1) 		->
			Printf.printf  "if (";	print_expVA expVA1; flush(); space();Printf.printf  ")"; new_line (); 
			Printf.printf "{";		indent (); afficherUneAffect i1; unindent ();
			Printf.printf "}"; new_line ()
	| BEGIN (liste)			->  afficherLesAffectations liste; new_line ()	;	flush(); space();			
	| FORV ( num, id, expVA1, expVA2, expVA3, _, i) -> 	
			Printf.printf "num loop %d\n" num; Printf.printf "/* %s" id ; flush();Printf.printf " */\nfor ("; flush(); space();
			new_line ();  print_expVA expVA1;flush(); space(); Printf.printf "; ";	print_expVA expVA2; flush(); space();Printf.printf "; " ;
			print_expVA expVA3;  new_line () ; Printf.printf ")\n" ;
			Printf.printf "{";		indent (); afficherUneAffect i; flush(); space(); unindent ();
			Printf.printf "}"; new_line ()
	| APPEL (num, avant, nom, apres,corps,_) ->
			Printf.printf  "\n\t\t\t\tFUNCTION CALL INPUT APPEL numbero %d %s \n" num nom; 
			afficherUneAffect avant;new_line () ;
			Printf.printf  "\n\t\t\t\tFUNCTION CORPS APPEL numbero %d\n" num; 
			afficherUneAffect corps;new_line () ;
			Printf.printf  "\t\t\t\t NAME %s\n" nom; 
			Printf.printf  "\t\t\t\t FUNCTION CALL OUTPUT\n"; 
			afficherUneAffect apres;new_line () ;flush(); space();
Printf.printf  "\t\t\t\t FIN  OUTPUT %d %s\n" num nom;  
Printf.printf  "\n\t\t\t\tFUNCTION CALL INPUT APPEL numbero %d %s FIN \n" num nom









type abstractStore =
		ASSIGN_SIMPLE of string  * expVA
	|	ASSIGN_DOUBLE of string * expVA * expVA
	|   ASSIGN_MEM of string * expVA * expVA 

let new_assign_simple id exp  = ASSIGN_SIMPLE(id, exp)
let new_assign_double id exp1 exp2  = ASSIGN_DOUBLE(id, exp1, exp2)
let new_assign_mem id exp1 exp2  = ASSIGN_MEM (id, exp1, exp2)

type typeListeAS = abstractStore list
type assos = string * abstractStore list
let new_assos id asL = (id,asL)

let listeASCourant = ref [] 	
let listeDesVarDependITitcour = ref [] (* as changed durind fixed point operator*)

let afficherAS a =
match a with
		ASSIGN_SIMPLE (s, e) 	 -> 
		(match e with EXP(ex) ->print_expression  (BINARY(ASSIGN, VARIABLE(s),  ex)) 0
						|_->print_expression  (BINARY(ASSIGN,VARIABLE(s), VARIABLE("NODEF"))) 0)
	|	ASSIGN_DOUBLE (s,e1, e2) -> 
		
			(match e1 with EXP(e) ->  
						(match e2 with EXP(ex) ->print_expression  (BINARY(ASSIGN,INDEX(VARIABLE(s),  e),  ex)) 0
						 	|_->print_expression  (BINARY(ASSIGN,INDEX(VARIABLE(s),  e),  VARIABLE("?"))) 0)
					| _->print_expression  (BINARY(ASSIGN,INDEX(VARIABLE(s),  VARIABLE("NODEF")),  VARIABLE("NODEF"))) 0)
				 
	|   ASSIGN_MEM (s, e1, e2)	-> 		
			(match e1 with EXP(e) ->  
						(match e2 with EXP(ex) ->print_expression  (BINARY(ASSIGN,INDEX(VARIABLE("*"^s),  e),  ex)) 0
						 	|_->print_expression  (BINARY(ASSIGN,INDEX(VARIABLE("*"^s),  e),  VARIABLE("NODEF"))) 0)
					| _->print_expression  (BINARY(ASSIGN,INDEX(VARIABLE("*"^s),  VARIABLE("NODEF")),  VARIABLE("NODEF"))) 0)

let abGlobales = ref []
let  globalesVar = ref[]
let asToListeAffect a =
match a with
		ASSIGN_SIMPLE (s, e) 	 ->	new_instVar s e 	
	|	ASSIGN_DOUBLE (s,e1, e2) ->	new_instTab s e1 e2
	|	ASSIGN_MEM (id, e1, e2)	->  new_instMem id e1 e2


let rec listeAsToListeAffect l =
if l = [] then [] else List.append [asToListeAffect (List.hd l)] (listeAsToListeAffect (List.tl l))
						
let afficherListeAS asL =space(); new_line() ;flush(); List.iter (fun a-> afficherAS a; space(); new_line() ;flush(); )asL

let afficherListeDesFctAS liste=
if liste <> [] then
begin
	Printf.printf "AFFICHER LISTE DES ASSOS\n";
	List.iter (fun (n,asL)->  new_line ();Printf.printf n;new_line ();afficherListeAS asL;new_line ();new_line ()  ) liste  ;						
	Printf.printf "AFFICHER FIN LISTE DES ASSOS\n"
end

let new_listeAssos  a liste= liste := List.append !liste [a]
	
let  expVaToExp exp = match exp with EXP(e) ->e| _->NOTHING




let rec extractVarCONDAffectaux  listeAffect listeCondVar =
if listeAffect = [] then ([], [])
else 
begin
	let (affect, suite) = (List.hd listeAffect, List.tl listeAffect) in

	let (newSuite, listeaux) = extractVarCONDAffectaux suite listeCondVar in

	match affect with
	 VAR ( id, exp) 				->	 
		if  List.mem id listeCondVar then 
		begin 
			(List.append [affect] newSuite, union  listeaux (listeDesVarsDeExpSeules  (expVaToExp (exp)))) 
		end 
		else (newSuite, listeaux) 
	| TAB ( id, _, _) 	->  (newSuite, listeaux)
	|  MEMASSIGN ( id, _, _)	->  (newSuite, listeaux) (*voir*)
	| IFVF ( expVA1, i1, i2) 		->
			let (newi1, listeaux1) = extractVarCONDAffectaux [i1] listeCondVar in
			let (newi2, listeaux2)  = extractVarCONDAffectaux [i2] listeCondVar in
			if newi1 = [] && newi2 = [] then (newSuite, listeaux)
			else 
			begin
				let next1 = if newi1 = [] then BEGIN([]) else List.hd newi1 in
				let next2 = if newi2 = [] then BEGIN([]) else List.hd newi2 in
				(List.append [IFVF ( expVA1, next1, next2) ] newSuite, union (union listeaux1 listeaux2) listeaux)
			end
	| IFV ( expVA1, i1) 		->
			let (newi1, listeaux1) = extractVarCONDAffectaux [i1] listeCondVar in
			
			if newi1 = []  then (newSuite, listeaux)
			else (List.append [IFV ( expVA1, List.hd newi1)] newSuite, union listeaux1 listeaux)
	| BEGIN (liste)			->  
			let (newi1, listeaux1) = extractVarCONDAffectaux liste listeCondVar in		
			if newi1 = []  then (newSuite, listeaux)
			else (List.append [BEGIN ( newi1)] newSuite, union listeaux1 listeaux)			
	| FORV ( num, id, expVA1, expVA2, expVA3, n, i) -> 	
			let (newi1, listeaux1) = extractVarCONDAffectaux [i] listeCondVar in		
			if newi1 = []  then (newSuite, listeaux)
			else (List.append [  FORV ( num, id, expVA1, expVA2, expVA3, n, (List.hd newi1))] newSuite, union listeaux1 listeaux)			

	| APPEL (num, e, nom, s,c,v) ->

			(* var may be a global *)
			let (newi1, listeaux1) = extractVarCONDAffectaux [c] listeCondVar in
			if newi1 = []  then (newSuite, listeaux)
			else (List.append [ APPEL( num, e,nom ,s, (List.hd newi1),v)] newSuite, union  listeaux1 listeaux)				
end

(* fixed point operator to find any usefull variable for loop condition*)
let rec extractVarCONDAffect listeAffect listeCondVar =
let (extractsInst, listevar) = extractVarCONDAffectaux  listeAffect listeCondVar in
if listevar = [] || (inclus listevar listeCondVar) then extractsInst
else extractVarCONDAffect listeAffect (union listeCondVar listevar)



let rec existAffectVDsListeAS v (*index*) l =
(*Printf.printf "recherche %s dans liste :\n" v;afficherListeAS l;new_line ();Printf.printf "fin s liste :\n" ;*)
if l = [] then false
else 
let a = List.hd l in
let suite = List.tl l in
	match a with
		ASSIGN_SIMPLE (s, e) 	 -> 	if s = v then true else existAffectVDsListeAS v (*index*) suite
	|	ASSIGN_DOUBLE (s,e1, e2) -> 	
			if s = v (*and il faut évaluer les 2 expression index = e1*) then true
			else  existAffectVDsListeAS v (*index*) suite
	| ASSIGN_MEM (id, e1, e2)	-> 
			if id = v (*and il faut évaluer les 2 expression index = e1*) then true
			else  existAffectVDsListeAS v (*index*) suite


let rec rechercheAffectVDsListeAS v (*index*) l =
(*Printf.printf "recherche %s dans liste :\n" v;afficherListeAS l;new_line ();Printf.printf "fin s liste :\n" ;*)
if l = [] then EXP(NOTHING)
else 
let a = List.hd l in
let suite = List.tl l in
	match a with
		ASSIGN_SIMPLE (s, e) 	 -> 	if s = v then e else rechercheAffectVDsListeAS v (*index*) suite
	|	ASSIGN_DOUBLE (s,e1, e2) -> 	
			if s = v (*and il faut évaluer les 2 expression index = e1*) then 
			begin
				if !vDEBUG then begin	Printf.printf "tableau avec index à terminer\n";(* afficherAS a *) end; 
				e2
			end
			else  rechercheAffectVDsListeAS v (*index*) suite
	| ASSIGN_MEM (s, e1, e2)	-> 
			if s = v (*and il faut évaluer les 2 expression index = e1*) then 
			begin
				if !vDEBUG then begin	Printf.printf "tableau avec index à terminer\n";(* afficherAS a *) end; 
				e2
			end
			else  rechercheAffectVDsListeAS v (*index*) suite


let estMultipleDef v (*index*) l = match rechercheAffectVDsListeAS v (*index*) l with MULTIPLE -> true | EXP (e) -> false

let estDef v (*index*) l = match rechercheAffectVDsListeAS v (*index*) l with MULTIPLE -> true | EXP (e) -> if e=NOTHING then false else true

let expressionAffectVar v (*index*) l = match rechercheAffectVDsListeAS v (*index*) l with MULTIPLE -> NOTHING | EXP (e) -> e

let contientAssos liste n = List.exists (fun a ->let (nom, _) = a in nom = n)liste	
let valeurAssos liste n = List.find (fun a ->let (nom, _) = a in nom = n)liste
	
type listeDesVar = string list

let rec rechercheLesVar listeaS listeVAR =
if (listeaS = []) then listeVAR
else 
	begin
		let aSCourant = List.hd listeaS in
		let suite = List.tl listeaS in
		match aSCourant with
		ASSIGN_SIMPLE (id, _) ->if(List.mem id listeVAR) then (rechercheLesVar suite listeVAR)
								else 	List.append (rechercheLesVar suite listeVAR) [id]
		|	ASSIGN_DOUBLE (id, _, _) -> 
								if(List.mem id listeVAR) then (rechercheLesVar suite listeVAR)
								else List.append (rechercheLesVar suite listeVAR) [id]	
		| ASSIGN_MEM (id, _, _)	-> 	if(List.mem id listeVAR) then (rechercheLesVar suite listeVAR)
								else List.append (rechercheLesVar suite listeVAR) [id]	
	end
	
let existeAffectationVarListe var liste =
  List.exists (fun aSCourant -> 	
			 		match aSCourant with
					ASSIGN_SIMPLE (id, _) -> 	(id = var)  |	ASSIGN_DOUBLE (id, _, _) ->  (id = var)|ASSIGN_MEM (id, _, _)	-> 
					id = var
			   ) liste  
			 
let ro var liste =
   List.find  (fun aSCourant -> match aSCourant with ASSIGN_SIMPLE (id, _) ->  (id = var)  |	ASSIGN_DOUBLE (id, _, _) ->   (id =
			 var)|ASSIGN_MEM (id, _, _)	-> 
					id = var ) liste

let rofilter var liste =
		List.filter 
		(fun aSCourant ->  match aSCourant with ASSIGN_SIMPLE (id, _) ->  (id = var)  |	ASSIGN_DOUBLE (id, _, _) ->   (id =
			 var)|ASSIGN_MEM (id, _, _)	-> 
					id = var ) liste



let rec roavant  (liste: abstractStore list )
				 ( aS: abstractStore  ) 
				 (resaux : abstractStore list )=
if liste = [] then resaux
else
begin
	let (head, others) = (List.hd liste,  List.tl liste) in
 	if (aS = head) then  resaux else (roavant  others aS (List.append resaux [head]) )
end

let listeAffectationVarListe var liste =
 List.filter (fun aSCourant -> match aSCourant with ASSIGN_SIMPLE (id, _) -> 	(id = var)  |	ASSIGN_DOUBLE (id, _, _) ->  (id = var) |ASSIGN_MEM (id, _, _)	-> 
					(id = var) ) liste  
						
let boolAS = ref true

let eqindex i j =
if i = j then begin (*Printf.printf " index egaux \n" ;*) true end else 
begin
	let i1 = calculer i !infoaffichNull [] in
	let ii1 = calculer j !infoaffichNull  [] in
	if estNoComp i1 || estNoComp ii1 then false (*en fait en ne peut pas répondre*)
	else if  estNul (evalexpression (Diff (i1, ii1 ))) then  begin (*Printf.printf " index egaux \n" ;*) true end  else false
end

let diffindex i j  = (*parfois ni diff ni eq on ne sait pas *)
		let i1 = calculer i !infoaffichNull  [] in
		let ii1 = calculer j !infoaffichNull  [] in
		if estNoComp i1 || estNoComp ii1 then false (*en fait en ne peut pas répondre*)
		else if  estNul (evalexpression (Diff (i1, ii1 ))) = false then 
			 begin(* Printf.printf "differents index \n" ;*) true end  
			 else false

let couldBeEqIndex i j  = if (eqindex i j  = false) && (diffindex i j = false) then true else false 


let rofilterWithoutIndex var liste i=
		List.filter 
		(fun aSCourant ->  
			match aSCourant with ASSIGN_SIMPLE (id, _) ->  (id = var)  
			|	ASSIGN_DOUBLE (id, index, _) ->   
					if (id = var) then 
						if couldBeEqIndex i index then false else true
					else false
			|ASSIGN_MEM (id, index, _)	-> 
					if (id = var) then 
						if couldBeEqIndex i index then false else true
					else false
		) liste


let existeAffectationVarIndexListe var l i=
    List.exists (fun aS ->  match aS with ASSIGN_SIMPLE (id, _) ->  (id = var)  |ASSIGN_DOUBLE (id, index, _) -> (id = var) && eqindex index i|ASSIGN_MEM (id, e, _)	-> 
					id = var&& eqindex e i) l

let couldExistAssignVarIndexList var l i=
    List.exists (fun aS ->  match aS with ASSIGN_SIMPLE (id, _)-> (id = var) |ASSIGN_DOUBLE (id, index, _)->(id = var) && couldBeEqIndex index i| ASSIGN_MEM (id, e, _)	-> 
					id = var&& eqindex e i) l

let roindex var l i=
   List.find  (fun aSC ->  match aSC with ASSIGN_SIMPLE (id, _) ->  (id = var) |ASSIGN_DOUBLE (id, index, _)-> (id = var) && eqindex index i| ASSIGN_MEM (id, e, _)	-> 
					id = var&& eqindex e i) l


let isCallVarStruct lid =
if lid = [] then true
else			let x =  (List.hd lid) in
				if (String.length x> 4) then
				begin
					let var4 = (String.sub x  0 4) in
					if  var4 = "call"   then 
					begin if !vDEBUG then Printf.printf "non traite champ struct depuis appel de fonction";true end else false
				end 
				else false

let rec consArrayFromPtrExp exp arrayName =
	 match exp with
		
		 UNARY (op, exp)	-> 
			(match op with
				MINUS | PLUS-> let varOfExp = (listeDesVarsDeExpSeules exp) in
							   if List.mem arrayName varOfExp = false then (exp, false)
							   else (NOTHING, false)
				|_->(NOTHING, false) )

		| BINARY (op, exp1, exp2) ->
			
			let varOfExp1 = (listeDesVarsDeExpSeules exp1) in
			let varOfExp2 = (listeDesVarsDeExpSeules exp2) in
			if List.mem arrayName varOfExp1 = false then
			begin
				let (resexp2, hasArray) = consArrayFromPtrExp exp2 arrayName in
				if hasArray then
					match op with
					 ADD|SUB -> if resexp2 = NOTHING then ( exp1, true) else ( BINARY(op, exp1, resexp2), true)
						|_-> (NOTHING, false)
				else (NOTHING, false)
			end
			else 
			begin
				
				if List.mem arrayName varOfExp2 = false then
				begin
					let (resexp1, hasArray) = consArrayFromPtrExp exp1 arrayName in
					if hasArray then
						match op with
						 ADD|SUB -> if resexp1 = NOTHING then (exp2, true) else ( BINARY(op, resexp1, exp2), true)
							|_-> (NOTHING, false)
					else (NOTHING, false)
	
				end
				else (NOTHING,false)
			end
		| CONSTANT c-> (exp,false)
		| VARIABLE name ->  if name = arrayName then (NOTHING, true) 
							else if (String.length name > 4) then
									if (String.sub name  0 4) = "bIt_" then  (exp, false) else (NOTHING, false)
								 else (NOTHING, false)		(* sinon pb si ptr=tab+k ; k=k+1; *ptr=... donc pour le moment que constante*)						
		|_ ->(* actuellement  non traitée *)(NOTHING, false)


let getArrayAssign  x index assign =
		
									(*	Printf.printf "variable *%s " ptr_name;
									 	afficherAS ro2x; flush(); new_line(); *)
	
		(*Printf.printf "variable %s " x ;
		Printf.printf "<- \n" ;	print_expression (expVaToExp assign)  0; new_line(); flush() ;space(); flush(); new_line(); flush();*)
		let (tab1,_, _) =getArrayNameOfexp (expVaToExp index) in
								
		if tab1 != "" then
		begin
			(*Printf.printf "tableau tab trouve tab %s ptr %s \n" tab1 x;*)
			let (indexexp , isok) = consArrayFromPtrExp (expVaToExp index )  tab1 in
			if isok then 
			begin
				let resindex = expressionEvalueeToExpression( calculer (EXP(indexexp))  !infoaffichNull []) in
										

				(*print_expression  (INDEX(VARIABLE(tab1), resindex)) 0; new_line(); flush() ;space(); flush(); new_line(); flush();
				Printf.printf "<- \n" ;print_expression (expVaToExp assign) 0; new_line(); flush() ;space flush; new_line(); flush();*)
				new_assign_double tab1 (EXP(resindex)) assign
			end else new_assign_mem x index assign 
		end else new_assign_mem x index assign 

let arrayAssignFilter var liste=
		List.filter 
		(fun aSCourant ->  
			match aSCourant with ASSIGN_SIMPLE (id, _)  |	ASSIGN_DOUBLE (id, _, _)  |ASSIGN_MEM (id, _, _)	->  (id = var)  
		) liste


let rec applyStore e a =
match e with
	NOTHING  -> NOTHING
	| VARIABLE name ->  
		if (existeAffectationVarListe name a ) then 
			match (ro name a) with ASSIGN_SIMPLE (_(*id*), EXP(valeur)) -> (valeur) | _ ->(*impossible ou erreur code c*)	(NOTHING)
		else (e)
	| CONSTANT 					cst	->
							(match cst with 
								CONST_COMPOUND expsc ->(*Printf.printf "consta conpound 1\n"; print_expression e 0; new_line();*)
								let na = CONSTANT( CONST_COMPOUND( List.map (fun arg -> applyStore (arg) a) expsc)) in
								(*if na != e then begin Printf.printf "new 1\n";print_expression na 0; new_line() end;*)
								(na)
								|_->(*Printf.printf "consta\n";*)(e)	)
		 (*	Printf.printf " expression applystore constante\n";*)
	| UNARY (op, exp1) 				-> 
		(	match op with 
				MEMOF ->
						let exp1e = applyStore exp1 a in
						let (tab1,_, _) =getArrayNameOfexp  exp1  in
						if tab1 != "" then
						begin
							let (indexexp , isok) = consArrayFromPtrExp ( exp1  )  tab1 in
							if isok then 
							begin
								if existAssosArrayIDsize tab1  then 
								begin
									let resindex = expressionEvalueeToExpression( calculer (EXP(indexexp))  !infoaffichNull []) in

									if (existeAffectationVarIndexListe tab1 a (EXP(applyStore resindex a))) then
									begin
												
										let rotab =roindex tab1 a (EXP(resindex)) in
										(match rotab with
											ASSIGN_DOUBLE  (_, _, EXP(exp2))-> (*je ne suis pas sure d'avoir bien interpete l'algo *)
								(*print_expression  (INDEX(VARIABLE(tab1), resindex)) 0; new_line(); flush() ;space(); flush(); new_line(); flush();
												Printf.printf "soit :\n";
												print_expression  exp2  0; new_line(); flush() ;space(); flush(); new_line(); flush();*)
													exp2 
											| 	_->(UNARY (op, exp1e  )))

									end
									else 
									begin
										(*print_expression  (INDEX(VARIABLE(tab1), resindex)) 0; new_line(); flush() ;space(); flush(); new_line(); flush();Printf.printf"non exist affect\n";*)
(*let arrayas = arrayAssignFilter tab1 a in
if arrayas != [] then begin Printf.printf "les as rofilter array\n" ; afficherListeAS arrayas; Printf.printf "fin \n" end ;*)
 
										INDEX(VARIABLE(tab1), resindex)
									end
										(*UNARY (op, exp1e  )*)
											 
								end
								else (UNARY (op,exp1e ))
							end else (UNARY (op, exp1e  ))
						end 
						else 
						begin
							(match exp1 with
							 UNARY (ADDROF, next) ->   applyStore next a 
							 |_->	UNARY (op, exp1e  ))
						end
			|ADDROF->    	(match exp1 with
							 UNARY (MEMOF, next) ->  applyStore next a 
							 |_->	 UNARY (op, (applyStore exp1 a) ))
			|_->(* if op = NOT then begin Printf.printf "NOT\n" ; print_expression  (UNARY (op, (applyStore exp1 a) ))) 0; new_line();end;*) (UNARY (op, (applyStore exp1 a) )))
	| BINARY (op, exp1, exp2) 		-> 	(BINARY (op, (applyStore exp1 a), (applyStore exp2 a)))
	| QUESTION (exp1, exp2, exp3) ->  	(QUESTION ((applyStore exp1 a), (applyStore exp2 a) , (applyStore exp3 a) ))
	| CAST (typ, exp1) 				->	let res = (applyStore exp1 a) in 
										if res = NOTHING then NOTHING else res
	| CALL (exp1, args) 			->	
										(CALL ( exp1 , List.map (fun arg -> applyStore (arg) a) args))
	| COMMA exps 					->	(COMMA ( List.map (fun arg -> applyStore (arg) a) exps))
	| EXPR_SIZEOF exp 				->	(EXPR_SIZEOF (applyStore exp a))
	| TYPE_SIZEOF _ 				->	(e)
	| INDEX (exp, idx) 				->	(*Printf.printf " expression applystore index\n";*)
		 let index = (applyStore idx a) in
		(	match exp with
			VARIABLE name ->
				if (existeAffectationVarIndexListe name a (EXP(index)))	then 
				begin
					let absl = roindex  name a (EXP(index))	 in
					(
						match absl with
						ASSIGN_DOUBLE  (_, _, EXP(exp2))-> exp2 (*je ne suis pas sure d'avoir bien interpete l'algo *)
						| 	_->begin boolAS:= true; (NOTHING) end
					)
				end	 
				else	if couldExistAssignVarIndexList name a (EXP(index))	 then begin boolAS:= true; (NOTHING) end 
						else 
						begin

(*let arrayas = arrayAssignFilter name a in
if arrayas != [] then begin Printf.printf "les as rofilter array\n" ; afficherListeAS arrayas; Printf.printf "fin \n" end ;*)

							 (INDEX (exp, index))
						end
			| _-> if !vDEBUG then Printf.printf"t[i] definit mais pas g->a[i] --A TERMINER \n";
				boolAS:= true; 
				(NOTHING)
		)				
	 | MEMBEROF (ex, c) 			
	 | MEMBEROFPTR (ex, c) 		->	
		let lid =	getInitVarFromStruct e  in
		if lid != [] && (isCallVarStruct lid = false )then 
		begin

			let (btype, id) =  ( getBaseType (List.assoc (List.hd lid) !listAssocIdType) , List.hd lid)  in
			if (existeAffectationVarListe id a ) then 
			begin
				
				(match (ro id a) with 
					ASSIGN_SIMPLE (id, EXP(valeur)) -> (*Printf.printf "applystore assign %s\n" id;print_expression valeur 0; new_line();*)
					(	match (valeur) with  
						CONSTANT cst ->
							(match cst with 
								CONST_COMPOUND expsc ->  (*Printf.printf "applystore MEMBEROFPTR lid non vide  assigncomma%s\n" id;*)
									(*List.iter (fun x-> Printf.printf "%s." x)lid;	Printf.printf "\n"; *)
									let na = getconsCommaExp  btype (List.tl lid) expsc in
	 							(*	Printf.printf "new\n";print_expression na 0; new_line() ;*)
									(na)
								|_->(valeur)	
							)
						|  UNARY (op, e) ->
							(match op with
								ADDROF ->
								(*	Printf.printf "&assign\n";*)
									(match e with 
										CONSTANT cst ->
											(match cst with
												CONST_COMPOUND expsc ->  
												(*Printf.printf "applystore MEMBEROFPTR lid non vide  &assigncomma%s\n" id;*)
											   (* List.iter (fun x-> Printf.printf "%s." x)lid;	Printf.printf "\n"; *)
												let na = getconsCommaExp  btype (List.tl lid) expsc in
 												(*Printf.printf "new\n";print_expression na 0; new_line() ;*)
												(na)
												|_->(valeur)
											)
										|_-> begin boolAS:= true; (NOTHING) end 
									)
								|_-> begin boolAS:= true; (NOTHING) end 
							)(*voir autres cas*)
						|_->	begin boolAS:= true; (NOTHING)end
					)
					| _ ->(*impossible ou erreur code c*)	begin boolAS:= true; (NOTHING)end
				)
			end
			else begin (*Printf.printf "AS non exist \n" ;*) (e)end
		end
		else begin boolAS:= true; (NOTHING)end

	| _	-> if !vDEBUG then Printf.printf "struct et gnu body non traités pour le moment \n"; 
			boolAS:= true; 
			(NOTHING)



let rec hasSygmaExp e =
(*Printf.printf "  asSygmaExp \n";*)
match e with
	| UNARY (_, exp1) 				-> 	hasSygmaExp exp1 
	| BINARY (_, exp1, exp2) 		-> 	hasSygmaExp exp1 || hasSygmaExp exp2
	| QUESTION (exp1, exp2, exp3) ->  	hasSygmaExp exp1 || hasSygmaExp exp2 || hasSygmaExp exp3
	| CAST (_, exp1) 				->	hasSygmaExp exp1 
	| CALL (exp, args) 			->	( match exp with VARIABLE("SYGMA") -> true 
									|	_-> 
										if args = [] then false 
								else  List.exists (fun a ->hasSygmaExp a)args	 )
	| INDEX (exp, idx) 				->		hasSygmaExp exp || hasSygmaExp idx
	| EXPR_LINE (expr, _, _) ->hasSygmaExp expr
	|_->false

	
and  hasSygmaExpVA eva =
(*Printf.printf "  hasSygmaExp \n";*)
match eva with
	  MULTIPLE -> false
	| EXP (e) -> (*(*hasSygmaExp e*) true*)hasSygmaExp e
		
let applyStoreVA exp a = 
match exp with
	  MULTIPLE -> (*Printf.printf "dans applyStoreVA multiple\n";*) (exp)
	| EXP (e) -> (*Printf.printf "dans applyStoreVA\n";*)
			boolAS := false;  
			let res = applyStore e a  in
			if (!boolAS = false) then EXP(res) else MULTIPLE
		
			


let listWithoutVarAssignSingle var liste =
 List.filter (fun aS ->  match aS with ASSIGN_SIMPLE (id, _) -> 	(id <> var)  |_ ->  true  ) liste  

let listWithoutIndexAssign n index l =
 List.filter 
	(fun aS -> match aS with ASSIGN_SIMPLE (id, _) -> true |ASSIGN_DOUBLE (id, i, _) -> if id = n &&  (eqindex index  i) then false else true|ASSIGN_MEM (id, i, _) -> if id = n &&  (eqindex index  i) then false else true) l  
	

let rondListe a1 a2 ro2x =
		let avant = roavant  a2 ro2x [] in
		match ro2x with 
			ASSIGN_SIMPLE (x, exp) ->
				let assign = (applyStoreVA(applyStoreVA exp avant) a1) in
				let na =  new_assign_simple x assign in
			([ na], listWithoutVarAssignSingle x a1)
				
		|	ASSIGN_DOUBLE (x, exp1, exp2) ->  
			
		let index =  (applyStoreVA(applyStoreVA exp1 avant) a1) in
(*let f=rofilter x a1 in
			if f != [] then
			begin	
					Printf.printf "les as filter array\n" ;afficherListeAS f;Printf.printf "fin \n";

					let f1=rofilterWithoutIndex x a1 index in
					if f1 != [] then 
					begin 
						Printf.printf "les as rofilterWithoutIndex array\n" ; afficherListeAS f1; Printf.printf "fin \n"
					end
			end;*)


			if (existeAffectationVarIndexListe x a1 index) then
			begin (* affectation de x(i) dans les deux cas *)
				let na = new_assign_double x index (applyStoreVA (applyStoreVA exp2 avant) a1) in 
			    (*List.append [na]  (rofilterWithoutIndex x a1 index) *)([na], listWithoutIndexAssign x index a1)
			end
			else
			begin
				 if couldExistAssignVarIndexList x a1 index then  
						(*List.append*) ([new_assign_double x index MULTIPLE], a1)
								 (*rofilterWithoutIndex x a1 index*)
				 else (* n'appartient pas à ro1*)	
					(*List.append*)	([new_assign_double x index (applyStoreVA (applyStoreVA exp2 avant) a1)], a1)	
						  (*rofilter x a1 *)  
			     
			end		
		|	ASSIGN_MEM (x, exp1, exp2) -> (* Printf.printf"mem affect\n";*)
(*Printf.printf "les as filter array %s\n" x ;afficherListeAS avant;Printf.printf "fin \n";
Printf.printf "les as filter array a1\n" ;afficherListeAS a1;Printf.printf "fin \n";
print_expVA  exp1 ; new_line();flush();space(); flush(); new_line();flush();*)
	(*if avant != [] then begin			Printf.printf "les as 2 avant \n" ;
				afficherListeAS avant;
				Printf.printf "fin \n" end;*)
			let index =  (applyStoreVA(applyStoreVA exp1 avant) a1) in
(*let f=rofilter x a1 in*)
		(*	if f != [] then
			begin	
					Printf.printf "les as filter mem\n" ;afficherListeAS f;Printf.printf "fin \n";

					let f1=rofilterWithoutIndex x a1 index in
					if f1 != [] then 
					begin 
						Printf.printf "les as rofilterWithoutIndex mem\n" ; afficherListeAS f1; Printf.printf "fin \n"
					end
			end;*)


			let assign = (applyStoreVA(applyStoreVA exp2 avant) a1) in
			let na = getArrayAssign x index assign  in
			if (existeAffectationVarIndexListe x a1 index) then
			begin (* affectation de x(i) dans les deux cas *)
				([na] , listWithoutIndexAssign x index a1)
					 
			end
			else
			begin
				if couldExistAssignVarIndexList x a1 index then  
					 ([new_assign_mem x index MULTIPLE] , a1)
				else (* n'appartient pas à ro1*)	
							([na]	  , a1)
			end		

		
(*let rechercherToutesLesVariablesDE a1 a2 = rechercheLesVar a2 (rechercheLesVar a1 [])  *)
let rec conslist l1 l2 a2 =
if l2 = [] then []
else
	if l1 = [] then l2
	else
	begin 
		let (x,suite) =(List.hd l1, List.tl l1) in
		if (existeAffectationVarListe x a2) then conslist suite l2 a2 
		else List.append [x] (conslist suite l2 a2 )
	end

let rec consRondList a1 a2  revl2=
	if revl2 = [] then ([],a1)
	else
	begin
		let (first, next) = (List.hd  revl2, List.tl  revl2) in
		 
		let (nax,newa1)= (rondListe a1 a2 first) in
		let (suite, new2a1) = (consRondList newa1 a2 next  )in
		( ( List.append nax suite),new2a1)
	end


let rond a1 a2 =(* avant new*)
(* pour tout x appartenant à a1 ou à a2 *)
(*Printf.printf "rond\n";*)

if a1 = [] then listeASCourant := a2
else
	if a2 = [] then listeASCourant := a1
	else
	begin
	(*	Printf.printf "les as 1 \n" ;
		afficherListeAS a1;
		Printf.printf "fin \n";
		Printf.printf "les as 2 \n" ;
		afficherListeAS a2;
		Printf.printf "fin \n";*)
		 
		(*let l2 = rechercheLesVar a2 [] in 

			(*let listeDesVara1Eta2 = conslist l1 l2 a2   in *)
Printf.printf "l2\n";
List.iter(fun x ->Printf.printf "%s\t"x)l2;
Printf.printf "\nl2 fin\n";*)
			(*let revl2 =  List.rev a2  in*)

			let ( after, before)=  consRondList a1 a2  a2(*revl2*) in
			 listeASCourant := List.append  before after(*(*List.rev*) (List.map ( fun x ->rondListe a1 a2 x	)listeDesVara1Eta2);*)	
		 
	end;
(*Printf.printf "les as rond res \n" ;
		afficherListeAS !listeASCourant;
		Printf.printf "fin \n";*)
	(!listeASCourant)

(*

let rondListe a1 a2 x =

	if (existeAffectationVarListe x a2) then
	begin
	
		let ro2x = ro x a2 in
		let avant = roavant  a2 ro2x [] in
		match ro2x with 
		ASSIGN_SIMPLE (x, exp) ->
         
			 let na = new_assign_simple x (applyStoreVA(applyStoreVA exp avant) a1) in
			 na
				
		|	ASSIGN_DOUBLE (x, exp1, exp2) ->  
			let index = applyStoreVA  (applyStoreVA exp1 avant) a1 in
			if (existeAffectationVarIndexListe x a1 index) then
			begin (* affectation de x(i) dans les deux cas *)
				(*let b = a1 in
				let suite =   listWithoutIndexAssign x index b in  *)
				let na = new_assign_double x index (applyStoreVA (applyStoreVA exp2 avant) a1) in
				(*if na !=  ro2x then listeDesVarDependITitcour :=List.append !listeDesVarDependITitcour [na]; *)
			    na
				(*roindex x a1 index *)
			end
			else
			begin
				 let na = if couldExistAssignVarIndexList x a1 index then  new_assign_double x index MULTIPLE
				 else (* n'appartient pas à ro1*)		new_assign_double x index (applyStoreVA (applyStoreVA exp2 avant) a1)	in	
				
			     na
			end		
		|	ASSIGN_MEM (x, exp1, exp2) -> (* Printf.printf"mem affect\n";*)
 
let index =  (applyStoreVA(applyStoreVA exp1 avant) a1) in
 
			let assign = (applyStoreVA(applyStoreVA exp2 avant) a1) in
			let na = getArrayAssign x index assign  in
			if (existeAffectationVarIndexListe x a1 index) then
			begin (* affectation de x(i) dans les deux cas *)
				na
					 
			end
			else
			begin
				if couldExistAssignVarIndexList x a1 index then  
					new_assign_mem x index MULTIPLE
				else (* n'appartient pas à ro1*)	
							na
			end		
	end
	
	else (* si elle n'est pas dans a2 elle était dans a1 alors on met dans la liste ro1(x)*) 
		begin   ro x a1 end(* ro1(x)*)
		
(*let rechercherToutesLesVariablesDE a1 a2 = rechercheLesVar a2 (rechercheLesVar a1 [])  *)
let rec conslist l1 l2 a2 =
if l2 = [] then []
else
	if l1 = [] then l2
	else
	begin 
		let (x,suite) =(List.hd l1, List.tl l1) in
		if (existeAffectationVarListe x a2) then conslist suite l2 a2 
		else List.append [x] (conslist suite l2 a2 )
	end


let rond a1 a2 =(* avant new*)
(* pour tout x appartenant à a1 ou à a2 *)
(*Printf.printf "rond\n";*)

if a1 = [] then listeASCourant := a2
else
	if a2 = [] then listeASCourant := a1
	else
	begin
		(*Printf.printf "les as 1 \n" ;
		afficherListeAS a1;
		Printf.printf "fin \n";
		Printf.printf "les as 2 \n" ;
		afficherListeAS a2;
		Printf.printf "fin \n";*)
		let l1 = List.rev(rechercheLesVar a1 []) in
		let l2 = rechercheLesVar a2 [] in 

			let listeDesVara1Eta2 = conslist l1 l2 a2   in 
Printf.printf "l2\n";
List.iter(fun x ->Printf.printf "%s\t"x)l2;
Printf.printf "\nl2l1\n";
List.iter(fun x ->Printf.printf "%s\t"x) listeDesVara1Eta2 ;

			 listeASCourant := 	(*List.rev*) (List.map ( fun x ->rondListe a1 a2 x	)listeDesVara1Eta2);	
		 
	end;
(*Printf.printf "les as rond res \n" ;
		afficherListeAS !listeASCourant;
		Printf.printf "fin \n";*)
	(!listeASCourant)

*)
let estModifie = ref false

let closeForm assign varB listeDesVarModifiees =
estModifie := true;

let n = new_infoAffich (EXP(NOTHING)) (EXP(NOTHING)) (EXP(NOTHING)) (EXP(NOTHING)) CROISSANT ADD    in
let na =
(	match assign with
		ASSIGN_MEM (id, e1, e2) ->
		if id =varB then begin estModifie:= false; assign end
		else 
		begin
		(	match e1 with 
			MULTIPLE ->  listeDesVarDependITitcour :=List.append !listeDesVarDependITitcour [assign] ;assign
			| EXP(v1)->
				if List.mem id (listeDesVarsDeExpSeules v1)then 
				begin
				(	match e2 with
					MULTIPLE -> assign
					| EXP(v2) -> if List.mem id (listeDesVarsDeExpSeules v2) then  ASSIGN_MEM  (id, MULTIPLE, MULTIPLE) 
								else  assign 
				)
				end 
				else assign)		
		 end
	 |ASSIGN_DOUBLE (id,e1,e2) ->(*assign*)

(*Printf.printf "closeForm varB ASSIGN_DOUBLE = %s id %s =" varB id;  *)
		if id =varB then begin estModifie:= false; assign end
		else 
		begin
		(	match e1 with 
			MULTIPLE ->  listeDesVarDependITitcour :=List.append !listeDesVarDependITitcour [assign] ;assign
			| EXP(v1)->
				if List.mem id (listeDesVarsDeExpSeules v1)then 
				begin
				(	match e2 with
					MULTIPLE -> assign
					| EXP(v2) -> if List.mem id (listeDesVarsDeExpSeules v2) then  ASSIGN_DOUBLE  (id, MULTIPLE, MULTIPLE) 
								else  assign 
				)
				end 
				else assign)		
		 end
	|ASSIGN_SIMPLE (id, e)->	
(*Printf.printf "closeForm varB ASSIGN_SIMPLE = %s id %s =" varB id; *) 
	if id = varB then begin estModifie:= false; assign end
	else
	begin
		let varBPUN = BINARY(ADD, VARIABLE varB, CONSTANT(CONST_INT("1"))) in
	(	match e with 
		MULTIPLE -> listeDesVarDependITitcour :=List.append !listeDesVarDependITitcour [assign] ;assign
		|EXP (exp) ->
		(	match exp with
			UNARY (op, exp1) ->(*Printf.printf "closeForm varB ASSIGN_SIMPLE = %s id %s = UNARY" varB id;  *)
			(	match op with
				POSINCR|PREINCR ->   ASSIGN_SIMPLE ( id, EXP(BINARY(ADD, exp1,varBPUN)) )  (*il faut * it(i+1?)*)
				| POSDECR |PREDECR-> ASSIGN_SIMPLE ( id, EXP(BINARY(SUB, exp1,varBPUN)) ) 
				| MINUS ->  
					if List.mem id (listeDesVarsDeExpSeules exp1) then  
								ASSIGN_SIMPLE ( id, EXP(BINARY (MUL, exp1, 
									CALL (VARIABLE("pow"),List.append [CONSTANT(CONST_INT("-1"))] [varBPUN])))) 	else assign
				| _ -> 		if List.mem id (listeDesVarsDeExpSeules exp1) then ASSIGN_SIMPLE (id,MULTIPLE) else assign 
			)	
			| BINARY (op, exp1, exp2) ->(*Printf.printf "closeForm varB ASSIGN_SIMPLE = %s id %s = BINARY" varB id;  *)
				let varBPUN = BINARY(ADD, VARIABLE varB, CONSTANT(CONST_INT("1"))) in
				let (varE1,varE2) = (listeDesVarsDeExpSeules exp1,listeDesVarsDeExpSeules exp2) in 
				let (estVarE1, estVarE2)  = ( List.mem id varE1 ,List.mem id varE2 ) in
				(* if antidependance alors c'est pas id mais une variable de boucle autre *)
				if (estVarE1 = false) && (estVarE2 = false) then 	assign (*constant*)
				(* antidépendance si exp1 ou exp2 contiennent des variables modifiées par la boucle *)
				else
				begin
				(	match op with
					ADD| SUB| MUL| DIV| MOD	| SHL | SHR ->
						let valexp =calculer (EXP(exp))	n [] in
						if estVarDsExpEval id valexp = false then (* type x = cte*) assign 
						else if estAffine id valexp then
							 begin
								let (a,b) = calculaetbAffineForne id valexp in	 					
								let var1 = expressionEvalueeToExpression (evalexpression a) in
								let var2 = expressionEvalueeToExpression(evalexpression b) in	
								if var1 = CONSTANT(CONST_INT("1")) then (* type x = x + cte *)
									ASSIGN_SIMPLE (id,EXP(BINARY(ADD, VARIABLE(id), 
										BINARY(MUL,  var2, varBPUN))))
								else  if estNul b then (* type x = ax*) 		
										ASSIGN_SIMPLE  (id, EXP(BINARY(MUL, 
											VARIABLE(id),CALL (VARIABLE("pow"),   List.append [var1] [ varBPUN ]))))
									  else(* type x = ax+b*) 										
										ASSIGN_SIMPLE (	id, 
												EXP(BINARY(ADD, BINARY(MUL, var1, VARIABLE(id)), BINARY(MUL, var2, geometrique var1 varB))))
							 end
							 else ASSIGN_SIMPLE (id,MULTIPLE)
					| ADD_ASSIGN | SUB_ASSIGN -> 
						let opaux = (if (op = ADD_ASSIGN) then ADD else SUB) in
						let valexp =calculer (EXP(exp2)) n [] in
						if estVarDsExpEval id valexp = false then (* type x = x+b*) 
							ASSIGN_SIMPLE (id,EXP(BINARY(opaux, VARIABLE(id),  BINARY(MUL,  exp2, VARIABLE(varB)))))
						else (* type x = ax+b*) 
							if estAffine id valexp then
							begin
								let (a,b) = calculaetbAffineForne id valexp in	 					
								let var1 =  expressionEvalueeToExpression (evalexpression a)in
								let var2 = expressionEvalueeToExpression (evalexpression b) in	
								let vara =  BINARY (opaux,  CONSTANT(CONST_INT("1")), var1 )  in
								if estNul b then (* type x = ax*) 	
									ASSIGN_SIMPLE ( id, EXP(BINARY (MUL, VARIABLE(id), 
											  CALL (VARIABLE("pow"), List.append  [vara]  [varBPUN] ))))
								else(* type x = ax+b*) 										
									ASSIGN_SIMPLE (	id, EXP(BINARY(ADD, BINARY (MUL, vara, VARIABLE(id)),
												BINARY(MUL, var2, geometrique vara varB ) )) )
							end
						else ASSIGN_SIMPLE (id,MULTIPLE)
					| MUL_ASSIGN	| DIV_ASSIGN | MOD_ASSIGN | SHL_ASSIGN | SHR_ASSIGN-> 
						let valexp =calculer  (EXP(exp2)) n [] in
						if estVarDsExpEval id valexp = false then (* type x = x*cte*) 
							ASSIGN_SIMPLE  (id, EXP(BINARY( op, VARIABLE(id), CALL (VARIABLE("pow"), List.append [exp2] [ varBPUN ] ))))
						else ASSIGN_SIMPLE (id,MULTIPLE)			
					| _-> if List.mem id (listeDesVarsDeExpSeules exp) then  ASSIGN_SIMPLE ( id, MULTIPLE)
						  else assign
				)
				end (* binary*)
			| _->  (*Printf.printf "closeForm varB OTHER = %s id %s = BINARY" varB id; *)
				   if List.mem id (listeDesVarsDeExpSeules exp) then ASSIGN_SIMPLE ( id, MULTIPLE) else assign 
		))
	end
)	in

(*afficherListeAS [na] ;new_line();
Printf.printf "closeForm = \n" ; afficherListeAS [assign] ;new_line();*)
if na != assign then listeDesVarDependITitcour :=List.append !listeDesVarDependITitcour [na];
(*if !estModifie = true then listeDesVarDependITitcour :=List.append !listeDesVarDependITitcour [na];*)
na
			

let rec majexpaux var e	=
 match e with
	 	UNARY (op, exp) 		-> 	  UNARY (op, (majexpaux var exp))
	| 	BINARY (op, exp1, exp2) ->    BINARY (op, (majexpaux var exp1),  (majexpaux var exp2))
	| 	QUESTION (exp1, exp2, exp3)-> QUESTION ((majexpaux var exp1), (majexpaux var exp2), (majexpaux var exp3)) 
	| 	CAST (typ, exp) 		->	  CAST (typ, (majexpaux var exp))	
	| 	CALL (exp, args) 		->	  CALL (exp, (List.map (fun e -> majexpaux var e)args)) 
	| 	VARIABLE id			->	      if id = var then  BINARY(SUB, VARIABLE id, CONSTANT(CONST_INT("1")) ) else e
	| 	EXPR_SIZEOF exp 		->	  EXPR_SIZEOF  (majexpaux var exp)
	| 	INDEX (exp, idx) 		->	  INDEX ( (majexpaux var exp), idx)
	|	_ ->	e
(*	| 	MEMBEROF (exp, fld) 	->	  MEMBEROF ( (majexpaux var exp) , fld)
	| 	MEMBEROFPTR (exp, fld) 	->	  MEMBEROFPTR ( (majexpaux var exp) , fld)*)

let majexpauxaux varB e = match e with MULTIPLE -> MULTIPLE |EXP  (expr) ->  EXP(majexpaux varB expr)

let  rec majexpauxInit var e	init =
 match e with
	 	UNARY (op, exp) 		-> 	UNARY (op, (majexpauxInit var exp init))
	| 	BINARY (op, exp1, exp2) -> 	BINARY (op, (majexpauxInit var exp1 init),  (majexpauxInit var exp2 init))
	| 	QUESTION (exp1, exp2, exp3)-> QUESTION ((majexpauxInit var exp1 init), (majexpauxInit var exp2 init), (majexpauxInit var exp3 init)) 
	| 	CAST (typ, exp) 		->	CAST (typ, (majexpauxInit var exp init))	
	| 	CALL (exp, args) 		->	 CALL (exp, (List.map (fun e -> majexpauxInit var e init)args))
	| 	VARIABLE id				->	if id = var then   init else e
	| 	EXPR_SIZEOF exp 		->	EXPR_SIZEOF  (majexpauxInit var exp init)
	| 	INDEX (exp, idx) 		->	INDEX ( (majexpauxInit var exp init), idx)
	|	_ ->	e
	(*| 	MEMBEROF (exp, fld) 	->	MEMBEROF ( (majexpauxInit var exp init) , fld)
	| 	MEMBEROFPTR (exp, fld) 	->	MEMBEROFPTR ( (majexpauxInit var exp init) , fld)*)
	
let majexpauxauxInit varB e init= (* replace varB by init expression*)
match e with MULTIPLE -> MULTIPLE |EXP  (expr) -> EXP(majexpauxInit varB expr init)

let remplacer varB assign = 
	match assign with
	ASSIGN_SIMPLE (id, e)->         if id = varB then assign else ASSIGN_SIMPLE (id, majexpauxaux varB e)
	|   ASSIGN_DOUBLE (id,e1,e2) -> if id = varB then assign else ASSIGN_DOUBLE  (id, majexpauxaux varB e1, majexpauxaux varB e2)
	|   ASSIGN_MEM (id, e1, e2) -> if id = varB then assign else ASSIGN_MEM (id, majexpauxaux varB e1, majexpauxaux varB e2)

let rec replaceVarbyinitForEachInst var inst init =
	match inst with
	VAR ( id, expVA1) 				->	
		if List.mem var (listeDesVarsDeExpSeules (expVaToExp(expVA1))) then  VAR ( id, majexpauxauxInit var expVA1 init)  else  inst 		
	| TAB ( id, expVA1, expVA2) 	->	
		let newe1 = if List.mem var (listeDesVarsDeExpSeules (expVaToExp(expVA1)))  then majexpauxauxInit var expVA1 init else expVA1 in
		let newe2 =	if List.mem var (listeDesVarsDeExpSeules (expVaToExp(expVA2)))  then majexpauxauxInit var expVA2 init else expVA2 in
	 	TAB ( id, newe1, newe2) 		
	|  MEMASSIGN ( id, expVA1, expVA2)	->	
		let newe1 = if List.mem var (listeDesVarsDeExpSeules (expVaToExp(expVA1)))  then majexpauxauxInit var expVA1 init else expVA1 in
		let newe2 =	if List.mem var (listeDesVarsDeExpSeules (expVaToExp(expVA2)))  then majexpauxauxInit var expVA2 init else expVA2 in
	 	MEMASSIGN ( id, newe1, newe2) 	
			
	| IFVF ( expVA1, i1, i2) 		->
		let newe1 =	if List.mem var (listeDesVarsDeExpSeules (expVaToExp(expVA1))) then majexpauxauxInit var expVA1 init else expVA1 in
		IFVF ( newe1, replaceVarbyinitForEachInst var i1 init ,replaceVarbyinitForEachInst var i2 init ) 		
	| IFV ( expVA1, i1) 		->
		let newe1 =	if List.mem var (listeDesVarsDeExpSeules (expVaToExp(expVA1))) then majexpauxauxInit var expVA1 init else expVA1 in
		IFV ( newe1,replaceVarbyinitForEachInst var i1 init ) 	
	| BEGIN (liste)	-> BEGIN ( List.map (fun i -> replaceVarbyinitForEachInst var i init ) liste)		
	| FORV ( num, id, expVA1, expVA2, expVA3, n, i) -> 	
		let newe1 =if List.mem var (listeDesVarsDeExpSeules (expVaToExp(expVA1))) then majexpauxauxInit var expVA1 init else expVA1 in
		let newe2 =	if List.mem var (listeDesVarsDeExpSeules (expVaToExp(expVA2))) then majexpauxauxInit var expVA2 init else expVA2 in
		let newe3 =	if List.mem var (listeDesVarsDeExpSeules (expVaToExp(expVA3))) then majexpauxauxInit var expVA3 init else expVA1 in
		FORV ( num, id, newe1, newe2, newe3, n, replaceVarbyinitForEachInst var i init )
	| APPEL (num, avant, nom, apres,corps,varB) ->APPEL (num, avant, nom, apres,corps,varB) (* traiter avant ???*) 


let listeSansAffectVar l var= List.filter (fun e ->  match e with ASSIGN_SIMPLE (id, _)->if id = var then false else true |_->true ) l	

(*let rec majVG aG contexte = 
if contexte = [] then aG 
else if aG = [] then aG
	 else 
	 begin 
		let (prem, suite) = (List.hd aG, List.tl aG) in
		match prem with  
		ASSIGN_SIMPLE (x, exp) -> 
			if (existeAffectationVarListe x contexte ) then   List.append [ro x contexte] (majVG   suite contexte)
			else List.append [prem] (majVG   suite contexte)		
		| ASSIGN_DOUBLE (x, exp1, exp2) -> 
			let index = (applyStoreVA exp1 contexte) in
		 	if (existeAffectationVarIndexListe x contexte index)	then  List.append [roindex   x contexte index] (majVG   suite contexte)	
			else	if couldExistAssignVarIndexList x contexte  index	 then 
						List.append [ASSIGN_DOUBLE (x, index, MULTIPLE)] (majVG   suite contexte)	
					else List.append [prem] (majVG   suite contexte)
		| ASSIGN_MEM	 (x, exp1, exp2) -> 
			let index = (applyStoreVA exp1 contexte) in
		 	if (existeAffectationVarIndexListe x contexte index)	then  List.append [roindex   x contexte index] (majVG   suite contexte)	
			else	if couldExistAssignVarIndexList x contexte  index	 then 
						List.append [ASSIGN_MEM (x, index, MULTIPLE)] (majVG   suite contexte)	
					else List.append [prem] (majVG   suite contexte)
	end*)

let filterGlobales ascour globales =
List.filter(
fun prem ->
		match prem with  
		ASSIGN_SIMPLE (x, _) 
		| ASSIGN_DOUBLE (x, _, _)  -> if (List.mem x globales ) then begin  true end else false
		| ASSIGN_MEM	 (x, _, _)  -> if (List.mem x globales ) then begin  true end 
			else 
			begin
				false
			end
) ascour


let absMoinsT x a1 a2 =
(*Printf.printf "dans absMoinsT variable traitee %s \n" x;*)
	if ( existeAffectationVarListe x a1) then
	begin
(*Printf.printf "dans a1 %s \n" x;*)
		let ro1 = ro x a1 in 
		if ( existeAffectationVarListe x a2) then
		begin
(*Printf.printf "dans a2 %s \n" x;*)
			let ro2 = ro x a2 in
			if ro1 = ro2 		then ro1
			else 
			begin
				(*Printf.printf "MULTIPLE %s dans absMoinsT\n" x;*)
				match ro1 with
						ASSIGN_SIMPLE (_, _)->ASSIGN_SIMPLE (x, MULTIPLE)(*var MULTIPLE def voir si on
						utilise le max*)
					|	ASSIGN_DOUBLE (_, exp, _)-> ASSIGN_DOUBLE (x, exp, MULTIPLE) 
					|   ASSIGN_MEM (_, exp, _)-> ASSIGN_DOUBLE (x, exp, MULTIPLE) 
				
			end 
		end
		else begin(* rien pour x dans a2 on garde ce qu'il y a dans a1 *) (*Printf.printf "que dans a1 %s \n" x;afficherAS ro1;*) ro1 end
	end 
	else 
	begin
		(* rien pour x dans a1 on garde ce qu'il y a dans a2 *) 
		ro x a2 (* existe car dans au moins un] des deux ensembles*)		
	end	
	
let getVarDeAffect affect = match affect with ASSIGN_SIMPLE (id, _) ->id |	ASSIGN_DOUBLE (id, _, _) -> id|	ASSIGN_MEM (id, _, _) -> id


let rec paux a1 a2 l =
if l = [] then [] else  List.append  [absMoinsT (List.hd l) a1 a2 ] (paux a1 a2 (List.tl l) ) 

let  produit a1 a2  = 
(*Printf.printf "produit\n";*)
listeASCourant := paux a1 a2 (rechercheLesVar a2  (rechercheLesVar a1 []))



let absMoinsTEm x a1 a2 listeT=
	if ( existeAffectationVarListe x a1) then
	begin
		let ro1 = ro x a1 in 
		
		if ( existeAffectationVarListe x a2)  then
		begin
			
			let ro2 = ro x a2 in
			if ( List.mem x listeT) then ro2 (*changed into the two alternatives*)
			else
			begin
				if ro1 = ro2 	then ro1 (*changed into the only one alternative*)
				else 
				begin
					(*Printf.printf "MULTIPLE %s dans absMoinsTEm\n" x;*)
					match ro1 with
							ASSIGN_SIMPLE (_, _)->ASSIGN_SIMPLE (x, MULTIPLE)(*var MULTIPLE def voir si on utilise le max*)
						|	ASSIGN_DOUBLE (_, exp, _)-> ASSIGN_DOUBLE (x, exp, MULTIPLE) 
						|	ASSIGN_MEM (_, exp, _)-> ASSIGN_MEM (x, exp, MULTIPLE) 
				
				end 
			end
		end
		else (* rien pour x dans a2 on garde ce qu'il y a dans a1 *) ro1
	end 
	else 
	begin
		if ( List.mem x listeT) then ro x a2 (* existe car dans au moins un] des deux ensembles*)		
		else
		begin
			let resb = 
				if (String.length x > 4) then
				begin
					let var4 = (String.sub x  0 4) in
					let var3 = (String.sub x  0 3) in
					if  var3 = "IF_" || var3 = "tN_" || var4 = "max_" || var4 = "tni_" then true else false
				end
				else if (String.length x > 3) then if (String.sub x  0 3) = "IF_" then true else false else false in
			
			if resb then ro x a2
			else
			begin
					(*Printf.printf "MULTIPLE %s dans absMoinsTEm 2\n" x;Printf.printf "que dans a1 %s \n" x;afficherAS (ro x a2 );*)
					match ro x a2  with
							ASSIGN_SIMPLE (x, y)->if y = EXP(VARIABLE(x)) then ro x a2  else ASSIGN_SIMPLE (x, MULTIPLE)
						|	ASSIGN_DOUBLE (_, exp, _)-> ASSIGN_DOUBLE (x, exp, MULTIPLE) 
						|	ASSIGN_MEM (_, exp, _)-> ASSIGN_MEM (x, exp, MULTIPLE) 
				
				 
			end
		end
	end	


let rec pauxEm a1 a2 l listeT=
if l = [] then [] else  List.append  [absMoinsTEm (List.hd l) a1 a2 listeT] (pauxEm a1 a2 (List.tl l) listeT) 

let produitEm a1 a2 listeT = listeASCourant := pauxEm a1 a2 (rechercheLesVar a2  (rechercheLesVar a1 [])) listeT


let rec reecrireCallsInLoop var listeinst =
(*Printf.printf "reecrire liste appels dep de %s\n" var;*)
if listeinst = [] then listeinst
else 
begin
	let i = List.hd listeinst in
	let suite = List.tl listeinst in
	match i with 
		VAR (id, exp) -> List.append [i] (reecrireCallsInLoop var suite)
		| TAB (id, exp1, exp2) -> List.append [i] (reecrireCallsInLoop var suite)
		|  MEMASSIGN ( id, expVA1, expVA2)	->	 List.append [i] (reecrireCallsInLoop var suite)
		| BEGIN liste -> 		List.append [BEGIN(reecrireCallsInLoop var liste)]	 (reecrireCallsInLoop var suite)
		| IFVF (t, i1, i2) -> 	
			let liste1 = match i1 with BEGIN(e)-> e |_->[] in
			let res1 = reecrireCallsInLoop var liste1 in
			let liste2 = match i2 with BEGIN(e)-> e |_->[]  in
			let res2 = reecrireCallsInLoop var liste2 in
			List.append  [IFVF(t, BEGIN(res1), BEGIN(res2))] (reecrireCallsInLoop var suite)
		| IFV ( t, i1) 		-> 
			let liste1 = match i1 with BEGIN(e)-> e |_->[] in
			let res1 = reecrireCallsInLoop var liste1 in
			List.append [IFV ( t, BEGIN(res1))] (reecrireCallsInLoop var suite)
		| FORV (num,id, e1, e2, e3, nbIt, inst)	-> 
			let liste1 = match inst with BEGIN(e)-> e |_->[] in
			let res1 = reecrireCallsInLoop id liste1 in
			List.append [FORV (num,id, e1, e2, e3, nbIt,  BEGIN(res1))] (reecrireCallsInLoop var suite)
		| APPEL (i,e,nomFonc,s,c,_)-> 
			(*Printf.printf "reecriture appel %s depend de %s \n" nomFonc var;*)
			let liste1 = match c with BEGIN(e)-> e |_->[] in
			let res1 = reecrireCallsInLoop var liste1 in
			List.append [APPEL (i, e ,nomFonc,s,BEGIN(res1),var)] (reecrireCallsInLoop var suite) 
end

let corpsNouv = ref []
let corpsNouvI = ref []

(*let listeApres = ref []*)
let estTrue myTest =  if  myTest = Boolean(true) then true else false
let estFalse myTest = if  myTest = Boolean(false) then true else false

let rec evalStore i a =
(match i with 
	VAR (id, exp) -> (*Printf.printf "evalStore var %s valeur du contexte  \n" id; afficherListeAS a;
			Printf.printf "evalStore var apres contexte\n";*)
		
		listeASCourant :=rond a [new_assign_simple id exp];


		
	| TAB (id, exp1, exp2) -> (*Printf.printf "evalStore tab\n";*)
		listeASCourant :=rond a [new_assign_double id exp1 exp2]
		(*afficherListeAS !listeASCourant;*)
	|  MEMASSIGN ( id, exp1, exp2)	->	listeASCourant :=rond a [new_assign_mem id exp1 exp2];
(*Printf.printf"memassign\n"; afficherListeAS  [new_assign_mem id exp1 exp2];
Printf.printf"memassign as\n";	*)	
	| BEGIN liste ->(*Printf.printf "evalStore sequence\n";*)
		(*let pred = !listeASCourant in*)
		listeASCourant :=(traiterSequence liste a) ;
	(*afficherListeAS !listeASCourant;
		Printf.printf "fin evalStore sequence\n";*)
		
	| IFVF (cond, i1, i2) ->(*Printf.printf "evalStore if then else\n";*)

		let myCond = applyStoreVA (applyStoreVA  cond a) !abGlobales  in 
		let myTest = calculer myCond  !infoaffichNull  [] in
(*Printf.printf "evalStore if TRUE false\n"; 

print_expVA myCond; new_line();

		print_expTerm myTest;new_line();*)
		if !estDansBoucle = false then
		begin
			if estTrue myTest then  evalStore i1 a
			else 
			begin
				if estFalse myTest then evalStore i2 a
				else
				begin
					(*Printf.printf "\nevalStore if then else IF res test indefini\n";*)
					 listeASCourant := [];
					 evalStore i1 [];
					 let resT = !listeASCourant in
(*Printf.printf "les as de if T \n" ;
afficherListeAS !listeASCourant;
Printf.printf "fin \n";*)
					 let listeIF = (rechercheLesVar resT []) in
					 listeASCourant := [];
					 evalStore i2 [];
					 let resF = !listeASCourant in	
					 let listeELSE = (rechercheLesVar resF []) in
					 let inter = intersection listeELSE  listeIF in
					 	listeASCourant := []; 
					 produit resT resF 	;
					 
					 let resA = !listeASCourant in	
						listeASCourant := []; 
					 produitEm a resA inter	(*produit a resA*)
							(*	afficherListeAS !listeASCourant;*)
				end
			end
		end
		else
		begin
(*Printf.printf "dans boucle\n" ;*)
					 listeASCourant := [];
					 evalStore i1 [];
					 let resT = !listeASCourant in
					 let listeIF = (rechercheLesVar resT []) in
					 listeASCourant := [];
					 evalStore i2 [];
					
					
					 let resF = !listeASCourant in	

					 let listeELSE = (rechercheLesVar resF []) in

					 let inter = intersection listeELSE  listeIF in
					 	listeASCourant := []; 
					 produit resT resF 	;
					 let resA = !listeASCourant in	
						listeASCourant := []; 
					 produitEm a resA inter
					 
					(* let resA = !listeASCourant in	
						listeASCourant := []; 
					 produitEm a resA inter	;*)
		end;
(*Printf.printf "fin evalStore IF THEN ELSE\n";
print_expVA myCond; new_line();
Printf.printf "les as de if \n" ;
afficherListeAS !listeASCourant;
Printf.printf "fin \n";*)
					
	| IFV ( cond, i1) 		->(*Printf.printf "evalStore if TRUE \n"; *)
		let avant = a in

		let myCond = applyStoreVA (applyStoreVA  cond a) !abGlobales  in 

		let myTest = calculer myCond  !infoaffichNull  [] in
		(*print_expVA myCond; new_line();

		print_expTerm myTest;new_line();*)
	
		(*if !estDansBoucle = true then Printf.printf "IF DANS BOUCLE\n";*)
		if (!estDansBoucle = false && estTrue myTest)  then evalStore i1 a
		else if (!estDansBoucle = true) then
			begin
				(*Printf.printf "evalStore if TRUE dans boucle\n"; *)
				listeASCourant := [];
				evalStore i1 [];
				let resT = !listeASCourant in
				produitEm a resT []
				(*let resT = !listeASCourant in
				(*let listeT = (rechercheLesVar resT []) in*)
				listeASCourant := [];
				produitEm a resT [];*)

			end
			else 	if (estFalse myTest = true ) then  listeASCourant := avant 
					else 
					begin
					(*	Printf.printf "if non executé peut etre\n"; *)
						listeASCourant := [];evalStore i1 []; let resT = !listeASCourant in
						(*evalStore i1 [];
						let resT = !listeASCourant in
						(*let listeT = (rechercheLesVar resT []) in*)
						listeASCourant := [];*)
						produitEm a resT []
						(*produit a resT *)

					end;
(*Printf.printf "fin evalStore IF THEN \n";		
print_expVA myCond; new_line();
Printf.printf "les as de if \n" ;
(*afficherListeAS !listeASCourant;*)
Printf.printf "fin \n";*)
					
	| FORV (num,id, _, _, _, _, inst)	-> 
	(*	Printf.printf "\nevalStore boucle executed %d variable %s\n" num id;*)
		listeASCourant := [];
		let listePred = !listeDesVarDependITitcour in
		listeDesVarDependITitcour := [];
   		evalStore inst [];
(*Printf.printf "les as de la boucle avant transfo %d\n" num;
afficherListeAS !listeASCourant;
Printf.printf "les as de la boucle avant transfo \n";*)
		let resT = !listeASCourant in
		let newas=(closeFormPourToutXdelisteES resT id (*aS*) ) in

(*Printf.printf "les as de FOR aprescloseform\n" ;
afficherListeAS newas;
Printf.printf "fin \n";
Printf.printf "contexte\n" ;
afficherListeAS a;
Printf.printf "fin \n";*)

		listeASCourant:= (rond a  newas);
		(*abGlobales := majVG !abGlobales !listeASCourant;*)
		listeDesVarDependITitcour := listePred;
		(*Printf.printf "\nFIN evalStore boucle executed %d variable %s\n" num id;*)

(*Printf.printf "les as de FOR \n" ;
afficherListeAS !listeASCourant;
Printf.printf "fin \n";*)
			
	| APPEL (n,e,nomFonc,s,c,varB)->
		listeASCourant := [];
		(*let globales = majVG !abGlobales a in*)

		(*let contexte = rond  !abGlobales a  in*)

	(*	Printf.printf "evalStore fonction %s  \n" nomFonc ;	*)
		let sorties = (match s with BEGIN(sss)-> sss |_->[]) in
		listeASCourant := [];
		evalStore s [];
		let affectSortie = !listeASCourant in	

		let corps =   (match c with BEGIN(ccc)-> ccc |_->[]) in
		let entrees = (match e with BEGIN(eee)-> eee |_->[]) in

		if varB = "" then
		begin
			(* POUR ESSAYER D'OPTIMISER NE GUARDER QUE LES ENTREES ET LES GLOBALES*)
			listeASCourant := [];				
			evalStore (c) (evalInputFunction a entrees !abGlobales);
			corpsNouv := !listeASCourant;
			let rc =  !corpsNouv in listeASCourant := []; 
(*Printf.printf "contxte \n" ;afficherListeAS rc;Printf.printf "fin liste\n" ;*)
			if sorties <> [] then
			begin
				(*afficherListeAS rc; *)
				List.iter (
					fun sortie -> 
					(match sortie with 
					VAR (id, e) ->  
						listeASCourant :=  List.append 
						[new_assign_simple id  (applyStoreVA e rc)  ]  !listeASCourant; 
						()
					| TAB (id, e1, e2) ->  
						listeASCourant := List.append
							[ASSIGN_DOUBLE (id,   (applyStoreVA e1 rc) ,  (applyStoreVA e2 rc) )] !listeASCourant;
						()
					|_-> ())
					)sorties	
			end;
			let returnf = Printf.sprintf "res%s"  nomFonc in
			if existeAffectationVarListe returnf rc then
			begin
				let affectres = ro returnf rc in
				listeASCourant :=  List.append [affectres] !listeASCourant
			end;
			let nginterne = filterGlobales rc !globalesVar in
			listeASCourant := (*rond ng *) (rond a (List.append  !listeASCourant nginterne))
		end
		else 
		begin
			(*	Printf.printf "dans boucle\n";*)
			listeASCourant := [];
			corpsNouvI := sorties ;
			(*listeAvant := contexte;*)
			if entrees <> [] then
			begin
				List.iter (
					fun entree -> 
						match entree with 
						VAR (id, exp) ->
							let nouvar = Printf.sprintf "%s%s_%d" id nomFonc n in
							let idsortie = rechercheAffectVDsListeAS  id affectSortie in
							if idsortie = EXP(NOTHING) then corpsNouvI:= List.append !corpsNouvI [VAR (id, EXP(VARIABLE(nouvar)))]
						|_-> ()
					)entrees;

			end;

		(*	Printf.printf "le sorties a apere reecrire \%s depend de var de boucle %s\n" nomFonc varB;*)
		(*	afficherUneAffect (BEGIN(corps)); new_line(); Printf.printf "affect a apere reecrire fin\n";*)
			let memoutput = !corpsNouvI in
			let listeInput =   (evalInputFunction a entrees !abGlobales) in
			listeASCourant := [];
			evalStore (BEGIN(corps)) (*rond a*) listeInput;
			let rc = !listeASCourant in
			listeASCourant := [];
			if memoutput <> [] then
			begin
				(*afficherListeAS rc; *)
				List.iter (
					fun sortie -> 
					(match sortie with 
					VAR (id, e) ->  
						listeASCourant :=  List.append  [new_assign_simple id  (applyStoreVA e rc)]  !listeASCourant; 
						()
					| TAB (id, e1, e2) ->  
						listeASCourant := List.append [ASSIGN_DOUBLE (id, applyStoreVA e1 rc, applyStoreVA e2 rc)] !listeASCourant;
						()
					|_-> ())
					)memoutput	
			end;
			let returnf = Printf.sprintf "res%s"  nomFonc in
			if existeAffectationVarListe returnf rc then
			begin
				let affectres = ro returnf rc in
				listeASCourant :=  List.append [affectres] !listeASCourant
			end;
			let nginterne = filterGlobales rc !globalesVar in
		 

		(*Printf.printf "\nsorties %s depend de var de boucle %s\n" nomFonc varB; afficherListeAS !listeASCourant; Printf.printf "fin sorties\n";*)
			listeASCourant := rond (*rond contexte globales  *)a (List.append  !listeASCourant nginterne);
		
(*Printf.printf "evalStore fonction %s  \n global filter" nomFonc ; afficherListeAS nginterne; Printf.printf "fin res\n" ;*)
(*Printf.printf "evalStore fonction %s  \n" nomFonc ;afficherListeAS !listeASCourant; Printf.printf "fin res\n" ;*)
		end	
)	

and evalInputFunction a entrees  globales =
	if entrees <> [] then
	begin
		let(entree, others) = (List.hd entrees, List.tl entrees) in
				match entree with 
				VAR (id, exp) ->
					let new_exp = applyStoreVA (applyStoreVA exp a) globales in
					List.append   [new_assign_simple id  new_exp]  (evalInputFunction a others globales)
						
				|_-> (evalInputFunction a others globales)
	end	
	else []


and  traiterSequence liste a =
if liste = [] then a
else
begin

	listeASCourant := [];
	evalStore (List.hd liste) a;
	(traiterSequence (List.tl liste) !listeASCourant)														
end

and closeFormPourToutXdelisteES l id  =
(*Printf.printf "closeFormPourToutXdelisteES %s fin\n" id; *)
let listeDesVarModifiees = (rechercheLesVar l [] ) in
 let listeres =  (closeFormrec id  listeDesVarModifiees l listeDesVarModifiees) in
(traiterAntidepPointFixe id listeres )

and closeFormrec id  l listeaS listeDesVarModifiees =
(*Printf.printf "closeFormrec %s \n" id;*) 
if (listeaS = []) then begin (*Printf.printf "FIN closeFormrec %s \n" id; *) []end
else 
	begin
		let aSCourant = List.hd listeaS in
		let suite = List.tl listeaS in

		let new_affect =  closeForm aSCourant  id listeDesVarModifiees 	in

(*afficherListeAS [new_affect];new_line();*)
		List.append [new_affect] (closeFormrec id l suite listeDesVarModifiees)
end

and traiterAntidepPointFixe id listeAffect =
(* Printf.printf "traiterAntidepPointFixe\n" ;*)
	if !listeDesVarDependITitcour = [] then
	begin
		(*Printf.printf "traiterAntidepPointFixe FIN :  liste res :\n";
		afficherListeAS listeAffect;
		Printf.printf "traiterAntidepPointFixe : fin liste res :\n";   *)
		listeAffect
	end
	else
	begin (*Printf.printf "poursuivre point fixe\n" ;*)

(*Printf.printf "traiterAntidepPointFixe : liste des variables modifiées :\n";
afficherListeAS !listeDesVarDependITitcour;
Printf.printf "traiterAntidepPointFixe : fin liste des variables modifiées :\n";
Printf.printf "AVANT TRAITER ANTI DEP\n";*)
		let liste = !listeDesVarDependITitcour in
		listeDesVarDependITitcour := [];

(*Printf.printf "traiterAntidepPointFixe : liste des variables modifiées :\n";
afficherListeAS liste;*)

		let res = traiterAntidep id listeAffect liste  in

(*Printf.printf "traiterAntidepPointFixe :  liste res :\n";
afficherListeAS res;
Printf.printf "traiterAntidepPointFixe : fin liste res :\n";*)
		traiterAntidepPointFixe id res   
	end 

and  traiterAntidep id listeAffect listeAffectP =
(*Printf.printf "traiterAntidep \n";*)
if listeAffect = [] then []
else
begin
	if listeAffectP = [] then listeAffect
	else
		begin
			let listeaffectEtape = listeAffectP in
			let listeDesnewAffect = List.map (fun a -> remplacer id a) listeAffectP in

(*Printf.printf "traiterAntidep : liste des variables modifiées :\n";
afficherListeAS listeDesnewAffect;
Printf.printf "traiterAntidep : fin liste des variables modifiées :\n";*)


			remplacerToutes listeDesnewAffect listeAffect listeaffectEtape 		
		end
end

and  listeAffectBegin liste affect = (* liste affect pred *)
if liste = [] then ([], [])
else
begin
	let (a, suite) = (List.hd liste, List.tl liste) in
	if a = affect then ([] , suite)
	else 
	begin
		let (deb, fin) = (listeAffectBegin suite affect) in
		(List.append  deb [a], fin)
	end
end

and remplacerUneAffect assign aSC =
let listeDesVarModifiees = (rechercheLesVar aSC [] ) in

(*Printf.printf " remplacer remplacerUneAffect \n";afficherAS assign;new_line();*)
match assign with
	ASSIGN_SIMPLE (id, e)->	 	
		(match e with 
			MULTIPLE -> assign
			| EXP (exp) -> 
			if ( intersection (listeDesVarsDeExpSeules exp)  listeDesVarModifiees  ) != [] then  
				new_assign_simple id  (applyStoreVA e aSC) 
			else assign)
	| ASSIGN_DOUBLE (id,e1,e2) ->  
	(match e1 with 
			MULTIPLE -> assign
			| EXP (exp) -> 
			if ( intersection (listeDesVarsDeExpSeules exp)  listeDesVarModifiees  ) != [] then 
			begin 
				(match e2 with 
					MULTIPLE -> assign
					| EXP (exp2) -> 
					if ( intersection (listeDesVarsDeExpSeules exp2)  listeDesVarModifiees ) != []then  
						ASSIGN_DOUBLE (id,  applyStoreVA e1 aSC, applyStoreVA e2 aSC) 
					else assign)
			end 
			else assign)
	| ASSIGN_MEM (id,e1,e2) ->  
	(match e1 with 
			MULTIPLE -> assign
			| EXP (exp) -> 
			if ( intersection (listeDesVarsDeExpSeules exp)  listeDesVarModifiees  ) != [] then 
			begin 
				(match e2 with 
					MULTIPLE -> assign
					| EXP (exp2) -> 
					if ( intersection (listeDesVarsDeExpSeules exp2)  listeDesVarModifiees ) != []then  
						ASSIGN_MEM (id,  applyStoreVA e1 aSC, applyStoreVA e2 aSC) 
					else assign)
			end 
			else assign)


and remplacerToutes reverseliste l listeaffectEtape 	=
(*Printf.printf "remplacer toutes\n";
Printf.printf "liste affect etape \n";
afficherListeAS listeaffectEtape;
Printf.printf "remplacerToutesAffect fin liste l\n" ;*)
if listeaffectEtape = [] then begin  (*Printf.printf "liste affect etape vide\n";*)l end
else
begin
	let derniereAffectCour = List.hd listeaffectEtape in
	(*let aa = List.hd reverseliste in*)
	let (ltete , suite ) = listeAffectBegin l derniereAffectCour in
	let (teteaux , suiteaux) =(List.rev ltete, List.rev  suite) in


(*Printf.printf "remplacerToutesAffect precedentes\n" ;
afficherListeAS teteaux;
Printf.printf "remplacerToutesAffect fin liste\nAffectation courante :\n" ;
afficherAS derniereAffectCour;

Printf.printf "\nremplacerToutesAffect suite\n" ;
afficherListeAS suiteaux;
Printf.printf "\nremplacerToutesAffect fin liste\n" ;*)

	if teteaux = [] then (List.append [derniereAffectCour] (remplacerToutes (List.tl reverseliste)  suite (List.tl listeaffectEtape)))
	else
	begin
		let new_tete =  List.map
				(fun a ->(*afficherAS a;*)
					let na = remplacerUneAffect a reverseliste in
						 if a != na then  
						begin
						(*	Printf.printf "a != na\n";*)
(*Printf.printf "maj liste dep it cou\n" ;
afficherAS na;
Printf.printf "remplacerUneAffect nouveau assign fin\n" ;*)
						(*afficherAS na;*)
						listeDesVarDependITitcour := List.append !listeDesVarDependITitcour [na]
						end;
						 na
				) teteaux in

let ressuite = remplacerToutes (List.tl reverseliste)  suite (List.tl listeaffectEtape) in

(*Printf.printf "remplacerToutesAffect l :\n" ;
afficherListeAS l;
Printf.printf "remplacerToutesAffect fin liste l\n" ;

Printf.printf "remplacerToutesAffect res\n";
Printf.printf "tete\n";
afficherListeAS ( new_tete);
Printf.printf "cour\n";
afficherAS derniereAffectCour;
Printf.printf "suite\n";
afficherListeAS ( ressuite);
Printf.printf "remplacerToutesAffect res\n" ;*)
	List.append ( new_tete)  (List.append [derniereAffectCour] ressuite)
 	end 
end


