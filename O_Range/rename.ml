(* a variable name must be used only once -> rename
printf call must be replace...*)
(* rename -- use Frontc CAML  a variable name must be used only once -> rename
**
** Project:	O_Range
** File:	rename.ml
** Version:	1.1
** Date:	11.7.2008
** Author:	Marianne de Michiel
*)


open Cabs
let version = "rename Marianne de Michiel"

let rec isProto typ =
	match typ with
	 	PROTO (_, _, _) -> 		true
	| OLD_PROTO (_, _, _) ->	true
	| GNU_TYPE (_, typ) ->isProto typ
	| _ -> false

(* type newIdent  (string, string) List *)
let monContexte = ref [] (* newIdent list *) 


let listeDesVariablesFic = ref [] (* ident list *)
let existsVar var =  List.mem  var !listeDesVariablesFic
let addVar var = 
		listeDesVariablesFic := List.append [var] !listeDesVariablesFic

let existeAssosVarNewVal var contexte = List.mem_assoc var  contexte
let getAssosVarNewVal var contexte = List.assoc var contexte

let rec getNewIdent var instance= 
	let newStr = (Printf.sprintf "%s_%d" var instance) in
	if (existsVar newStr) then	getNewIdent var  (instance + 1) 
	else newStr

let renameIfNecessary var =
	let newVar = (	if existsVar var then 
					begin 
						let newStr = getNewIdent var 0 in
						monContexte := List.append !monContexte [(var, newStr)];
						newStr
					end 
					else var) in
addVar newVar;
newVar


let rec  concatContexte contCour contEng =
if contEng = [] then contCour
else
begin
	let (var , _) = List.hd contEng in
	if existeAssosVarNewVal var contCour then concatContexte contCour (List.tl contEng)
	else List.append [List.hd contEng] (concatContexte contCour (List.tl contEng))
	
end




let convertListeParamES (pars : single_name list) =
	List.map
	(fun courant ->	
			let (typ, a, name) = courant in
			let (nom, x, y, z) = name in
			let name = (renameIfNecessary nom, x, y,z) in
			(typ, a, name)			
	) pars


let convert_type (typ : base_type ) =
		match typ with
		PROTO (typ1, pars, ell) ->  PROTO(typ1,convertListeParamES pars, ell) 
		| _ -> typ

let rec convert_param ((id, typ, attr, exp) : name) =
		(id, convert_type typ, attr, convert_expression exp)


and convert_comma_exps exps =	List.map  convert_expression  exps


and convert_expression (exp : expression) =
		 match exp with
			  UNARY (op, exp1) -> UNARY (op, (convert_expression exp1))
			| BINARY (op, exp1, exp2) -> 
					BINARY (op, (convert_expression exp1), (convert_expression exp2))
			| QUESTION (exp1, exp2, exp3) ->
					QUESTION ((convert_expression exp1), (convert_expression exp2), (convert_expression exp3))
			| CAST (typ, exp) ->		CAST (typ, (convert_expression exp))
			| CALL (exp, args) ->		
						if exp = VARIABLE("printf") || exp= VARIABLE("sprintf") || exp = VARIABLE("fprintf") then
						begin
							(* to be completed || exp ="scanf" *)
							(*lineariser_comma_exp(exps)*) NOTHING
						end
						else	CALL(exp,convert_comma_exps args)
			| COMMA exps ->				COMMA(convert_comma_exps exps)
			| CONSTANT cst -> 			CONSTANT cst	
			| VARIABLE name ->			
					if existeAssosVarNewVal name !monContexte then VARIABLE (getAssosVarNewVal name !monContexte)
					else VARIABLE name
			| EXPR_SIZEOF exp ->		EXPR_SIZEOF (convert_expression exp)
			| TYPE_SIZEOF typ ->		TYPE_SIZEOF typ
			| INDEX (exp, idx) ->		INDEX ((convert_expression exp), idx)
			| MEMBEROF (exp, fld) ->	MEMBEROF ((convert_expression exp), fld)
			| MEMBEROFPTR (exp, fld) ->	MEMBEROFPTR ((convert_expression exp), fld)
			| EXPR_LINE (exp, file, line)->EXPR_LINE ((convert_expression exp), file, line)
			| GNU_BODY (decs, stat) ->  let decs = List.map convert_def decs in
										GNU_BODY (decs,convert_statement stat) 
			| _ -> exp


			

and convert_statement stat = 
		match stat with
		  COMPUTATION exp -> COMPUTATION (convert_expression exp)
		| BLOCK (defs, stat) -> 
			let contexteEnglobant = !monContexte in
			monContexte := [];
			let defs = List.map convert_def defs in
			monContexte := concatContexte !monContexte contexteEnglobant;
			let res = (if stat <> NOP then   BLOCK (defs, (convert_statement stat))  else  BLOCK (defs, NOP) ) in
			 monContexte := contexteEnglobant;
			res
		| SEQUENCE (s1, s2) -> 
				SEQUENCE (convert_statement s1, convert_statement s2)
		| IF (exp, s1, s2) ->  IF (convert_expression exp, convert_statement s1, convert_statement s2)
		| WHILE (exp, stat) -> WHILE (convert_expression  exp, convert_statement stat)
		| DOWHILE (exp, stat)->DOWHILE (convert_expression  exp, convert_statement stat) 
		| FOR (exp1, exp2, exp3, stat) ->
			FOR (convert_expression  exp1, convert_expression  exp2,convert_expression  exp3, convert_statement stat)
		| BREAK ->				BREAK
		| CONTINUE ->			CONTINUE
		| RETURN exp -> 		RETURN (convert_expression exp)
		| SWITCH (exp, stat) ->	SWITCH (convert_expression exp, convert_statement stat)
		| CASE (exp, stat) ->	CASE (convert_expression exp, convert_statement stat)
		| DEFAULT stat -> 		DEFAULT (convert_statement stat)
		| LABEL (name, stat) ->	LABEL (name, convert_statement stat) 
		| GOTO name ->			GOTO name 
		| ASM desc ->			ASM desc
		| GNU_ASM (desc, output, input, mods) ->GNU_ASM (desc, output, input, mods) (*REVOIR*)		
		| STAT_LINE (stat, file, line) -> STAT_LINE (convert_statement stat, file, line) 
		| _ ->	stat


	
	and convert_name ((id, typ, attr, exp) : name) =
		(*let nouType = convert_type typ in*)
		let nouId = renameIfNecessary id  in (* on ne renomme pas les fonctions pas les mêmes noms*)
		let nouExp = (if exp <> NOTHING then  convert_expression exp else exp) in
		(nouId, typ, attr, nouExp)

	and convert_name_group 	(typ, sto, names) =
		(typ, sto, List.map convert_name names)


and convert_def def =
		match def with
			FUNDEF (proto, body) ->
				let contexteEnglobant = !monContexte in
				monContexte := [];
				let (typeP,storageP,nameP)=proto in
				let proto = (typeP, storageP,convert_param nameP) in
				let contexteDecFunc = !monContexte in
				monContexte := contexteDecFunc;
			    let (decs, stat) = body in 
				
				let decs = List.map	(fun dec -> convert_def dec)		decs in
				monContexte := concatContexte   !monContexte contexteEnglobant;
				let res = FUNDEF (  proto,  (decs , convert_statement stat)) in
				monContexte := contexteEnglobant;
			res
			| OLDFUNDEF (proto, decs, body) -> (* no because convert by frontc into FUNDEF*)
				def
				(*
					let contexteEnglobant = monContexte in
					monContexte := [];
						List.map	(fun dec -> convert_name_group dec)		decs;(* !!!!VOIR***)
						let ndecs = List.map	(fun dec -> convert_def dec)		decs in
						let (decs, stat) = body in OLDFUNDEF (proto, ndecs, convert_statement (BLOCK (decs, stat)))
					monContexte := contexteEnglobant;
				*)
			| DECDEF names -> 
				let (baseType, _, namelist) = names in
				if isProto baseType = false then 
					DECDEF (convert_name_group names)
				else def
			| _ -> def 


let convert_comma_exps exps =	List.map  convert_expression  exps
(*let lineariser_comma_exp exps =	List.map  linea_expression  exps*)

let go  (defs : file) =
listeDesVariablesFic :=[];
  let decs = List.map	(fun dec -> convert_def dec)		defs in
decs
  
